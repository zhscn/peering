/*
 * Cross-validation driver: generates event sequences, processes them
 * through the C++ state machine, and outputs replay traces.
 *
 * Protocol (stdout):
 *   Default: JSON Lines (`--format jsonl`)
 *     One structured object per sequence start, replay step, and final summary.
 *
 *   Compatibility: line-based legacy format (`--format legacy`)
 *     Kept for older exploratory tooling.
 *
 * Compile:
 *   cmake -S . -B build
 *   cmake --build build --target cross_validate
 *
 * Run:
 *   ./build/cpp/cross_validate --seed 42 --sequences 5 --events 30
 */

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <random>
#include <set>
#include <string>
#include <algorithm>
#include <vector>

#include "peering_state.h"

using namespace vermilion::peering;

static void print_prefixed_auth_source_lines(const char* label,
                                             const AuthorityImage& auth_sources);

enum class OutputFormat {
    Legacy,
    Jsonl,
};

static journal_seq_t observed_auth_seq(const std::vector<PeerInfo>& infos) {
    journal_seq_t seq = 0;
    for (const auto& raw : infos) {
        auto info = normalized_peer_info(raw);
        seq = std::max(seq, info.committed_seq);
    }
    return seq;
}

// ── Reuse the PBT event generator ────────────────────────────────────

struct TestConfig {
    int num_osds;
    int pool_size;
    int pool_min_size;
    osd_id_t whoami;
    std::vector<osd_id_t> initial_acting;
    epoch_t current_epoch;
};

struct EventGenerator {
    std::mt19937 rng;
    TestConfig cfg;

    explicit EventGenerator(uint64_t seed) : rng(seed) {}

    TestConfig gen_config() {
        TestConfig c;
        c.num_osds = std::uniform_int_distribution<int>(2, 5)(rng);
        c.pool_size = std::uniform_int_distribution<int>(2, std::min(c.num_osds, 3))(rng);
        c.pool_min_size = std::uniform_int_distribution<int>(1, c.pool_size)(rng);
        c.current_epoch = 10;
        std::vector<osd_id_t> all_osds;
        for (int i = 0; i < c.num_osds; i++) all_osds.push_back(i);
        std::shuffle(all_osds.begin(), all_osds.end(), rng);
        c.initial_acting.assign(all_osds.begin(),
                                all_osds.begin() + std::min((int)all_osds.size(), c.pool_size));
        c.whoami = c.initial_acting[0];
        return c;
    }

    event::Initialize gen_initialize() {
        cfg = gen_config();
        uint64_t local_len = std::uniform_int_distribution<uint64_t>(0, 200)(rng);
        return event::Initialize{
            .pgid = 1,
            .whoami = cfg.whoami,
            .epoch = cfg.current_epoch,
            .acting = ActingSet{.osds = cfg.initial_acting, .epoch = cfg.current_epoch},
            .up = ActingSet{.osds = cfg.initial_acting, .epoch = cfg.current_epoch},
            .pool_size = cfg.pool_size,
            .pool_min_size = cfg.pool_min_size,
            .local_info = PGInfo{
                .pgid = 1,
                .committed_seq = local_len,
                .committed_length = local_len,
                .last_epoch_started = cfg.current_epoch,
                .last_interval_started = cfg.current_epoch,
            },
        };
    }

    osd_id_t random_osd() {
        return std::uniform_int_distribution<osd_id_t>(0, cfg.num_osds - 1)(rng);
    }

    osd_id_t random_peer() {
        osd_id_t osd;
        int attempts = 0;
        do {
            osd = random_osd();
            attempts++;
        } while (osd == cfg.whoami && attempts < 20);
        return osd;
    }

    std::vector<osd_id_t> random_acting_set() {
        std::vector<osd_id_t> all_osds;
        for (int i = 0; i < cfg.num_osds; i++) all_osds.push_back(i);
        std::shuffle(all_osds.begin(), all_osds.end(), rng);
        int sz = std::uniform_int_distribution<int>(1, std::min(cfg.num_osds, cfg.pool_size))(rng);
        std::vector<osd_id_t> result(all_osds.begin(), all_osds.begin() + sz);
        if (std::uniform_int_distribution<int>(0, 4)(rng) < 4) {
            auto it = std::find(result.begin(), result.end(), cfg.whoami);
            if (it != result.end()) {
                std::swap(*it, result[0]);
            } else {
                result[0] = cfg.whoami;
            }
        }
        return result;
    }

    PeeringEvent gen_event(const PeeringStateMachine::Snapshot& snap) {
        int choice = std::uniform_int_distribution<int>(0, 99)(rng);
        switch (snap.state) {
        case State::Initial:
            return gen_advance_map(snap);
        case State::GetPeerInfo:
            if (choice < 50) return gen_peer_info_received(snap);
            if (choice < 70) return gen_peer_query_timeout(snap);
            if (choice < 85) return gen_advance_map(snap);
            return gen_delete_start();
        case State::WaitUpThru:
            if (choice < 40) return gen_up_thru_updated(snap);
            if (choice < 60) return gen_peer_info_received(snap);
            if (choice < 80) return gen_advance_map(snap);
            return gen_delete_start();
        case State::Active:
            if (choice < 30) return gen_advance_map(snap);
            if (choice < 50) return event::ActivateCommitted{};
            if (choice < 65) return gen_all_replicas_recovered(snap);
            if (choice < 80) return gen_recovery_complete(snap);
            return gen_delete_start();
        case State::Recovering:
            if (choice < 40) return gen_recovery_complete(snap);
            if (choice < 55) return gen_all_replicas_recovered(snap);
            if (choice < 75) return gen_advance_map(snap);
            if (choice < 85) return event::ActivateCommitted{};
            return gen_delete_start();
        case State::Clean:
            if (choice < 50) return gen_advance_map(snap);
            if (choice < 70) return event::ActivateCommitted{};
            if (choice < 85) return gen_advance_map(snap);
            return gen_delete_start();
        case State::Stray:
            if (choice < 40) return gen_replica_activate(snap);
            if (choice < 70) return gen_advance_map(snap);
            return gen_delete_start();
        case State::ReplicaActive:
            if (choice < 30) return gen_replica_recovery_complete(snap);
            if (choice < 60) return gen_advance_map(snap);
            if (choice < 80) return gen_replica_activate(snap);
            return gen_delete_start();
        case State::Down:
            if (choice < 40) return gen_peer_info_received(snap);
            if (choice < 70) return gen_advance_map(snap);
            if (choice < 85) return gen_peer_query_timeout(snap);
            return gen_delete_start();
        case State::Incomplete:
            if (choice < 40) return gen_peer_info_received(snap);
            if (choice < 70) return gen_advance_map(snap);
            return gen_delete_start();
        case State::Deleting:
            if (choice < 50) return event::DeleteComplete{};
            return gen_advance_map(snap);
        default:
            return gen_advance_map(snap);
        }
    }

    event::AdvanceMap gen_advance_map(const PeeringStateMachine::Snapshot& snap) {
        epoch_t new_epoch = snap.epoch + 1;
        cfg.current_epoch = new_epoch;
        bool new_interval = std::uniform_int_distribution<int>(0, 9)(rng) < 4;
        std::vector<osd_id_t> new_acting_osds;
        if (new_interval) {
            new_acting_osds = random_acting_set();
        } else {
            new_acting_osds = snap.acting.osds;
        }
        int new_pool_size = snap.pool_size;
        int new_pool_min_size = snap.pool_min_size;
        if (std::uniform_int_distribution<int>(0, 9)(rng) == 0) {
            new_pool_min_size = std::uniform_int_distribution<int>(1, new_pool_size)(rng);
        }
        std::vector<osd_id_t> prior;
        if (new_interval && std::uniform_int_distribution<int>(0, 2)(rng) == 0) {
            int n = std::uniform_int_distribution<int>(1, 2)(rng);
            for (int i = 0; i < n; i++) prior.push_back(random_osd());
        }
        return event::AdvanceMap{
            .new_epoch = new_epoch,
            .new_acting = ActingSet{.osds = new_acting_osds, .epoch = new_epoch},
            .new_up = ActingSet{.osds = new_acting_osds, .epoch = new_epoch},
            .new_pool_size = new_pool_size,
            .new_pool_min_size = new_pool_min_size,
            .prior_osds = prior,
        };
    }

    event::PeerInfoReceived gen_peer_info_received(const PeeringStateMachine::Snapshot& snap) {
        osd_id_t from = random_peer();
        uint64_t len = std::uniform_int_distribution<uint64_t>(0, 300)(rng);
        epoch_t les = std::uniform_int_distribution<epoch_t>(
            snap.epoch > 5 ? snap.epoch - 5 : 1, snap.epoch)(rng);
        epoch_t qe = snap.last_peering_reset;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            qe = snap.last_peering_reset > 1 ? snap.last_peering_reset - 1 : 0;
        }
        return event::PeerInfoReceived{
            .from = from,
            .info = PeerInfo{
                .osd = from,
                .committed_seq = len,
                .committed_length = len,
                .image = primary_image(len),
                .last_epoch_started = les,
            },
            .query_epoch = qe,
        };
    }

    event::PeerQueryTimeout gen_peer_query_timeout(const PeeringStateMachine::Snapshot&) {
        return event::PeerQueryTimeout{.peer = random_peer()};
    }

    event::UpThruUpdated gen_up_thru_updated(const PeeringStateMachine::Snapshot& snap) {
        epoch_t ep = snap.epoch;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            ep = snap.epoch > 1 ? snap.epoch - 1 : 1;
        }
        return event::UpThruUpdated{.epoch = ep};
    }

    event::RecoveryComplete gen_recovery_complete(const PeeringStateMachine::Snapshot& snap) {
        osd_id_t peer;
        if (!snap.recovery_targets.empty() && std::uniform_int_distribution<int>(0, 2)(rng) < 2) {
            auto it = snap.recovery_targets.begin();
            std::advance(it, std::uniform_int_distribution<int>(
                0, (int)snap.recovery_targets.size() - 1)(rng));
            peer = *it;
        } else {
            peer = random_peer();
        }
        epoch_t ep = snap.last_peering_reset;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            ep = snap.last_peering_reset > 1 ? snap.last_peering_reset - 1 : 0;
        }
        return event::RecoveryComplete{.peer = peer, .epoch = ep};
    }

    event::AllReplicasRecovered gen_all_replicas_recovered(const PeeringStateMachine::Snapshot& snap) {
        epoch_t ep = snap.last_peering_reset;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            ep = snap.last_peering_reset > 1 ? snap.last_peering_reset - 1 : 0;
        }

        std::vector<osd_id_t> peers;
        for (osd_id_t peer : snap.recovery_targets) {
            if (snap.recovered.count(peer) == 0) {
                peers.push_back(peer);
            }
        }

        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            if (!peers.empty()) {
                peers.pop_back();
            } else {
                peers.push_back(random_peer());
            }
        }

        return event::AllReplicasRecovered{
            .epoch = ep,
            .peers = std::move(peers),
        };
    }

    event::ReplicaActivate gen_replica_activate(const PeeringStateMachine::Snapshot& snap) {
        osd_id_t from = snap.acting.primary();
        if (from < 0) from = random_peer();
        uint64_t len = std::uniform_int_distribution<uint64_t>(50, 300)(rng);
        epoch_t ep = snap.epoch;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            ep = snap.epoch > 1 ? snap.epoch - 1 : 1;
        }
        return event::ReplicaActivate{
            .from = from,
            .auth_info = PeerInfo{
                .osd = from,
                .committed_seq = snap.auth_seq > 0 ? snap.auth_seq : len,
                .committed_length = len,
                .image = snap.auth_image.empty() ? primary_image(len) : snap.auth_image,
                .last_epoch_started = ep,
            },
            .auth_sources = snap.auth_sources,
            .authoritative_seq = snap.auth_seq > 0 ? snap.auth_seq : len,
            .activation_epoch = ep,
        };
    }

    event::ReplicaRecoveryComplete gen_replica_recovery_complete(const PeeringStateMachine::Snapshot& snap) {
        uint64_t len = snap.auth_length;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            len = std::uniform_int_distribution<uint64_t>(0, 300)(rng);
        }
        journal_seq_t seq = snap.auth_seq > 0 ? snap.auth_seq : len;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            seq = std::uniform_int_distribution<journal_seq_t>(0, 300)(rng);
        }
        epoch_t ep = snap.epoch;
        if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
            ep = snap.epoch > 1 ? snap.epoch - 1 : 1;
        }
        return event::ReplicaRecoveryComplete{
            .new_committed_seq = seq,
            .new_committed_length = len,
            .recovered_image = snap.auth_image.empty() ? primary_image(len) : snap.auth_image,
            .activation_epoch = ep,
        };
    }

    event::DeleteStart gen_delete_start() {
        return event::DeleteStart{};
    }
};

// ── Output helpers ───────────────────────────────────────────────────

static void print_object_image(const ObjectImage& image) {
    if (image.empty()) {
        return;
    }
    bool first = true;
    for (const auto& [obj, len] : image) {
        if (!first) printf(" ");
        printf("%lu:%lu", (unsigned long)obj, (unsigned long)len);
        first = false;
    }
}

static void print_osd_list(const char* label, const std::vector<osd_id_t>& osds) {
    printf("%s", label);
    for (size_t i = 0; i < osds.size(); i++) {
        if (i > 0) printf(" ");
        printf("%d", osds[i]);
    }
    printf("\n");
}

static std::vector<PeerInfo> known_peer_images(const PeeringStateMachine::Snapshot& snap) {
    std::vector<PeerInfo> peers;
    peers.reserve(snap.peer_info.size() + 1);
    for (const auto& [osd, info] : snap.peer_info) {
        if (osd == snap.whoami) {
            continue;
        }
        auto copy = normalized_peer_info(info);
        copy.osd = osd;
        peers.push_back(std::move(copy));
    }
    auto local = normalized_pg_info(snap.local_info);
    peers.push_back(PeerInfo{
        .osd = snap.whoami,
        .committed_seq = local.committed_seq,
        .committed_length = local.committed_length,
        .image = local.image,
        .last_epoch_started = local.last_epoch_started,
        .last_interval_started = local.last_interval_started,
    });
    return peers;
}

static std::vector<PeerInfo> acting_replica_images(const PeeringStateMachine::Snapshot& snap) {
    std::vector<PeerInfo> peers;
    for (auto osd : snap.acting.osds) {
        if (osd < 0 || osd == snap.whoami) {
            continue;
        }
        auto it = snap.peer_info.find(osd);
        if (it != snap.peer_info.end()) {
            auto copy = normalized_peer_info(it->second);
            copy.osd = osd;
            peers.push_back(std::move(copy));
        } else {
            peers.push_back(PeerInfo{
                .osd = osd,
                .committed_seq = 0,
                .committed_length = 0,
                .image = {},
                .last_epoch_started = 0,
                .last_interval_started = 0,
            });
        }
    }
    return peers;
}

static bool snapshot_have_enough_info(const PeeringStateMachine::Snapshot& snap) {
    for (auto osd : snap.peers_queried) {
        if (snap.peers_responded.count(osd) == 0) {
            return false;
        }
    }
    for (auto osd : snap.acting.osds) {
        if (osd >= 0 && osd != snap.whoami && snap.peers_responded.count(osd) == 0) {
            return false;
        }
    }
    return true;
}

static bool snapshot_image_invariant(const PeeringStateMachine::Snapshot& snap) {
    auto known_peers = known_peer_images(snap);
    auto recomputed_sources = authoritative_sources(known_peers);
    auto recomputed_image = authority_image_values(recomputed_sources);
    auto recomputed_seq = observed_auth_seq(known_peers);
    auto expected_peer_plans =
        build_peer_recovery_plans(recomputed_sources, recomputed_seq, acting_replica_images(snap));
    auto expected_local_plan = pg_image_recovery_plan(recomputed_sources, snap.local_info);
    bool backed_by_known = true;
    for (const auto& [obj, auth] : snap.auth_sources) {
        bool backed = false;
        for (const auto& peer : known_peers) {
            if (lookup_length(effective_image(peer), obj) == auth.authority_length) {
                backed = true;
                break;
            }
        }
        if (!backed) {
            backed_by_known = false;
            break;
        }
    }
    if (!same_image(snap.auth_image, recomputed_image)) {
        return false;
    }
    if (snap.auth_seq != recomputed_seq) {
        return false;
    }
    if (!same_image(authority_image_values(snap.auth_sources), recomputed_image)) {
        return false;
    }
    if (!backed_by_known) {
        return false;
    }
    if (snap.local_info.committed_seq > snap.auth_seq) {
        return false;
    }
    if (!prefix_image(effective_image(snap.local_info), snap.auth_image)) {
        return false;
    }
    for (const auto& peer : acting_replica_images(snap)) {
        if (peer.committed_seq > snap.auth_seq) {
            return false;
        }
        if (!prefix_image(effective_image(peer), snap.auth_image)) {
            return false;
        }
    }
    if (!(snap.peer_recovery_plans == expected_peer_plans)) {
        return false;
    }
    if (!(snap.local_recovery_plan == expected_local_plan)) {
        return false;
    }
    return true;
}

static bool snapshot_image_clean(const PeeringStateMachine::Snapshot& snap) {
    if (!snapshot_image_invariant(snap)) {
        return false;
    }
    if (!snap.peer_recovery_plans.empty() || !snap.local_recovery_plan.empty()) {
        return false;
    }
    if (snap.local_info.committed_seq < snap.auth_seq
        || !same_image(effective_image(snap.local_info), snap.auth_image)) {
        return false;
    }
    for (const auto& peer : acting_replica_images(snap)) {
        if (peer.committed_seq < snap.auth_seq
            || !same_image(effective_image(peer), snap.auth_image)) {
            return false;
        }
    }
    return true;
}

static bool snapshot_image_recovering(const PeeringStateMachine::Snapshot& snap) {
    bool peer_seq_lag = false;
    for (const auto& peer : acting_replica_images(snap)) {
        if (peer.committed_seq < snap.auth_seq) {
            peer_seq_lag = true;
            break;
        }
    }
    return snapshot_image_invariant(snap)
        && !snapshot_image_clean(snap)
        && (!snap.peer_recovery_plans.empty()
            || !snap.local_recovery_plan.empty()
            || snap.local_info.committed_seq < snap.auth_seq
            || peer_seq_lag);
}

static void print_event(const PeeringEvent& ev) {
    std::visit([](const auto& e) {
        using T = std::decay_t<decltype(e)>;

        if constexpr (std::is_same_v<T, event::Initialize>) {
            printf("IMAGE_EVENT Initialize\n");
            printf("pgid %lu\n", (unsigned long)e.pgid);
            printf("whoami %d\n", e.whoami);
            printf("epoch %u\n", e.epoch);
            print_osd_list("acting ", e.acting.osds);
            print_osd_list("up ", e.up.osds);
            printf("pool_size %d\n", e.pool_size);
            printf("pool_min_size %d\n", e.pool_min_size);
            printf("local_image ");
            print_object_image(effective_image(e.local_info));
            printf("\n");
            printf("local_committed_seq %lu\n", (unsigned long)e.local_info.committed_seq);
            printf("last_epoch_started %u\n", e.local_info.last_epoch_started);
            printf("last_interval_started %u\n", e.local_info.last_interval_started);
            printf("last_epoch_clean %u\n", e.local_info.last_epoch_clean);
            print_osd_list("prior_osds ", e.prior_osds);
        }
        else if constexpr (std::is_same_v<T, event::AdvanceMap>) {
            printf("IMAGE_EVENT AdvanceMap\n");
            printf("new_epoch %u\n", e.new_epoch);
            print_osd_list("new_acting ", e.new_acting.osds);
            print_osd_list("new_up ", e.new_up.osds);
            printf("new_pool_size %d\n", e.new_pool_size);
            printf("new_pool_min_size %d\n", e.new_pool_min_size);
            print_osd_list("prior_osds ", e.prior_osds);
        }
        else if constexpr (std::is_same_v<T, event::PeerInfoReceived>) {
            printf("IMAGE_EVENT PeerImageReceived\n");
            printf("from %d\n", e.from);
            printf("peer_image ");
            print_object_image(effective_image(e.info));
            printf("\n");
            printf("peer_committed_seq %lu\n", (unsigned long)e.info.committed_seq);
            printf("last_epoch_started %u\n", e.info.last_epoch_started);
            printf("query_epoch %u\n", e.query_epoch);
        }
        else if constexpr (std::is_same_v<T, event::PeerQueryTimeout>) {
            printf("IMAGE_EVENT PeerQueryTimeout\n");
            printf("peer %d\n", e.peer);
        }
        else if constexpr (std::is_same_v<T, event::UpThruUpdated>) {
            printf("IMAGE_EVENT UpThruUpdated\n");
            printf("epoch %u\n", e.epoch);
        }
        else if constexpr (std::is_same_v<T, event::ActivateCommitted>) {
            printf("IMAGE_EVENT ActivateCommitted\n");
        }
        else if constexpr (std::is_same_v<T, event::RecoveryComplete>) {
            printf("IMAGE_EVENT RecoveryComplete\n");
            printf("peer %d\n", e.peer);
            printf("epoch %u\n", e.epoch);
        }
        else if constexpr (std::is_same_v<T, event::AllReplicasRecovered>) {
            printf("IMAGE_EVENT AllReplicasRecovered\n");
            printf("epoch %u\n", e.epoch);
            print_osd_list("peers ", e.peers);
        }
        else if constexpr (std::is_same_v<T, event::ReplicaActivate>) {
            printf("IMAGE_EVENT ReplicaActivate\n");
            printf("from %d\n", e.from);
            printf("peer_image ");
            print_object_image(effective_image(e.auth_info));
            printf("\n");
            printf("peer_committed_seq %lu\n", (unsigned long)e.auth_info.committed_seq);
            printf("authoritative_seq %lu\n", (unsigned long)e.authoritative_seq);
            printf("last_epoch_started %u\n", e.auth_info.last_epoch_started);
            print_prefixed_auth_source_lines("activation_auth_source", e.auth_sources);
            printf("activation_epoch %u\n", e.activation_epoch);
        }
        else if constexpr (std::is_same_v<T, event::ReplicaRecoveryComplete>) {
            printf("IMAGE_EVENT ReplicaRecoveryComplete\n");
            printf("recovered_image ");
            print_object_image(e.recovered_image.empty()
                                   ? primary_image(e.new_committed_length)
                                   : e.recovered_image);
            printf("\n");
            printf("new_committed_seq %lu\n", (unsigned long)e.new_committed_seq);
            printf("activation_epoch %u\n", e.activation_epoch);
        }
        else if constexpr (std::is_same_v<T, event::DeleteStart>) {
            printf("IMAGE_EVENT DeleteStart\n");
        }
        else if constexpr (std::is_same_v<T, event::DeleteComplete>) {
            printf("IMAGE_EVENT DeleteComplete\n");
        }
    }, ev);
    printf("---\n");
}

static void print_osd_vector(const std::vector<osd_id_t>& osds) {
    for (size_t i = 0; i < osds.size(); i++) {
        if (i) printf(" ");
        printf("%d", osds[i]);
    }
}

static void print_osd_set(const std::set<osd_id_t>& osds) {
    bool first = true;
    for (auto osd : osds) {
        if (!first) printf(" ");
        printf("%d", osd);
        first = false;
    }
}

static void print_peer_image_lines(const std::map<osd_id_t, PeerInfo>& infos) {
    for (const auto& [osd, info] : infos) {
        printf("peer_image %d ", osd);
        print_object_image(effective_image(info));
        printf(" %u\n", info.last_epoch_started);
        printf("peer_committed_seq %d %lu\n", osd, (unsigned long)info.committed_seq);
    }
}

static void print_auth_source_lines(const AuthorityImage& auth_sources) {
    for (const auto& [obj, item] : auth_sources) {
        printf("auth_source %lu %d %lu\n",
               (unsigned long)obj,
               item.authority_osd,
               (unsigned long)item.authority_length);
    }
}

static void print_prefixed_auth_source_lines(const char* label,
                                             const AuthorityImage& auth_sources) {
    for (const auto& [obj, item] : auth_sources) {
        printf("%s %lu %d %lu\n",
               label,
               (unsigned long)obj,
               item.authority_osd,
               (unsigned long)item.authority_length);
    }
}

static void print_peer_recovery_plan_lines(const std::vector<PeerRecoveryPlan>& plans) {
    for (const auto& plan : plans) {
        printf("peer_recovery_seq %d %lu %lu\n",
               plan.target,
               (unsigned long)plan.peer_committed_seq,
               (unsigned long)plan.authoritative_seq);
        for (const auto& item : plan.recoveries) {
            printf("peer_recovery %d %lu %lu %lu\n",
                   plan.target,
                   (unsigned long)item.obj,
                   (unsigned long)item.from_length,
                   (unsigned long)item.to_length);
            printf("peer_recovery_source %d %lu %d\n",
                   plan.target,
                   (unsigned long)item.obj,
                   item.source);
        }
    }
}

static void print_local_recovery_lines(const std::vector<ObjRecovery>& recoveries) {
    for (const auto& item : recoveries) {
        printf("local_recovery %lu %lu %lu\n",
               (unsigned long)item.obj,
               (unsigned long)item.from_length,
               (unsigned long)item.to_length);
        printf("local_recovery_source %lu %d\n",
               (unsigned long)item.obj,
               item.source);
    }
}

static void print_state(const PeeringStateMachine::Snapshot& snap) {
    printf("IMAGE_CONTEXT\n");
    printf("pgid %lu\n", (unsigned long)snap.pgid);
    printf("whoami %d\n", snap.whoami);
    printf("epoch %u\n", snap.epoch);
    printf("acting ");
    print_osd_vector(snap.acting.osds);
    printf("\n");
    printf("acting_epoch %u\n", snap.acting.epoch);
    printf("up ");
    print_osd_vector(snap.up.osds);
    printf("\n");
    printf("up_epoch %u\n", snap.up.epoch);
    printf("pool_size %d\n", snap.pool_size);
    printf("pool_min_size %d\n", snap.pool_min_size);
    printf("local_committed_seq %lu\n", (unsigned long)snap.local_info.committed_seq);
    printf("local_image ");
    print_object_image(snap.local_info.image);
    printf("\n");
    printf("local_last_epoch_started %u\n", snap.local_info.last_epoch_started);
    printf("local_last_interval_started %u\n", snap.local_info.last_interval_started);
    printf("local_last_epoch_clean %u\n", snap.local_info.last_epoch_clean);
    printf("auth_seq %lu\n", (unsigned long)snap.auth_seq);
    printf("auth_image ");
    print_object_image(snap.auth_image);
    printf("\n");
    print_auth_source_lines(snap.auth_sources);
    print_peer_image_lines(snap.peer_info);
    printf("peers_queried ");
    print_osd_set(snap.peers_queried);
    printf("\n");
    printf("peers_responded ");
    print_osd_set(snap.peers_responded);
    printf("\n");
    printf("prior_osds ");
    print_osd_set(snap.prior_osds);
    printf("\n");
    print_peer_recovery_plan_lines(snap.peer_recovery_plans);
    print_local_recovery_lines(snap.local_recovery_plan);
    if (snap.local_info.committed_seq < snap.auth_seq) {
        printf("local_recovery_seq %lu %lu\n",
               (unsigned long)snap.local_info.committed_seq,
               (unsigned long)snap.auth_seq);
    }
    printf("recovered ");
    print_osd_set(snap.recovered);
    printf("\n");
    printf("timed_out_probes ");
    print_osd_set(snap.timed_out_probes);
    printf("\n");
    printf("need_up_thru %d\n", snap.need_up_thru ? 1 : 0);
    printf("activated %d\n", snap.activated ? 1 : 0);
    printf("pending_acting_change %d\n", snap.pending_acting_change ? 1 : 0);
    printf("last_peering_reset %u\n", snap.last_peering_reset);
    printf("have_enough_info %d\n", snapshot_have_enough_info(snap) ? 1 : 0);
    printf("image_invariant %d\n", snapshot_image_invariant(snap) ? 1 : 0);
    printf("image_clean %d\n", snapshot_image_clean(snap) ? 1 : 0);
    printf("image_recovering %d\n", snapshot_image_recovering(snap) ? 1 : 0);
    printf("---\n");
}

// ── Structured output helpers ───────────────────────────────────────

static std::string json_escape(const std::string& input) {
    std::string out;
    out.reserve(input.size());
    for (unsigned char ch : input) {
        switch (ch) {
        case '\\':
            out += "\\\\";
            break;
        case '"':
            out += "\\\"";
            break;
        case '\n':
            out += "\\n";
            break;
        case '\r':
            out += "\\r";
            break;
        case '\t':
            out += "\\t";
            break;
        default:
            if (ch < 0x20) {
                char buf[7];
                std::snprintf(buf, sizeof(buf), "\\u%04x", ch);
                out += buf;
            } else {
                out.push_back(static_cast<char>(ch));
            }
            break;
        }
    }
    return out;
}

static std::string json_string(const std::string& value) {
    return "\"" + json_escape(value) + "\"";
}

template <typename T>
static std::string json_number(T value) {
    if constexpr (std::is_signed_v<T>) {
        return std::to_string(static_cast<long long>(value));
    } else {
        return std::to_string(static_cast<unsigned long long>(value));
    }
}

static std::string json_bool(bool value) {
    return value ? "true" : "false";
}

template <typename Range, typename Fn>
static std::string json_array(const Range& range, Fn fn) {
    std::string out = "[";
    bool first = true;
    for (const auto& item : range) {
        if (!first) out += ",";
        first = false;
        out += fn(item);
    }
    out += "]";
    return out;
}

static void json_field(std::string& out, bool& first,
                       const char* key, const std::string& value) {
    if (!first) out += ",";
    first = false;
    out += json_string(key);
    out += ":";
    out += value;
}

static std::string json_object_image(const ObjectImage& image) {
    return json_array(image, [](const auto& item) {
        std::string out = "{";
        bool first = true;
        json_field(out, first, "obj", json_number(item.first));
        json_field(out, first, "len", json_number(item.second));
        out += "}";
        return out;
    });
}

static std::string json_authority_image(const AuthorityImage& auth) {
    return json_array(auth, [](const auto& item) {
        std::string out = "{";
        bool first = true;
        json_field(out, first, "obj", json_number(item.first));
        json_field(out, first, "osd", json_number(item.second.authority_osd));
        json_field(out, first, "len", json_number(item.second.authority_length));
        out += "}";
        return out;
    });
}

static std::string json_acting_set(const ActingSet& acting) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "osds",
               json_array(acting.osds, [](osd_id_t osd) { return json_number(osd); }));
    json_field(out, first, "epoch", json_number(acting.epoch));
    out += "}";
    return out;
}

static std::string json_obj_recovery(const ObjRecovery& item) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "obj", json_number(item.obj));
    json_field(out, first, "source", json_number(item.source));
    json_field(out, first, "from_length", json_number(item.from_length));
    json_field(out, first, "to_length", json_number(item.to_length));
    out += "}";
    return out;
}

static std::string json_peer_recovery_plan(const PeerRecoveryPlan& plan) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "target", json_number(plan.target));
    json_field(out, first, "peer_committed_seq", json_number(plan.peer_committed_seq));
    json_field(out, first, "authoritative_seq", json_number(plan.authoritative_seq));
    json_field(out, first, "recoveries",
               json_array(plan.recoveries, [](const ObjRecovery& item) {
                   return json_obj_recovery(item);
               }));
    out += "}";
    return out;
}

static std::string json_peer_info(const PeerInfo& info) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "osd", json_number(info.osd));
    json_field(out, first, "committed_seq", json_number(info.committed_seq));
    json_field(out, first, "committed_length", json_number(info.committed_length));
    json_field(out, first, "image", json_object_image(effective_image(info)));
    json_field(out, first, "last_epoch_started", json_number(info.last_epoch_started));
    json_field(out, first, "last_interval_started", json_number(info.last_interval_started));
    out += "}";
    return out;
}

static std::string json_pg_info(const PGInfo& raw) {
    auto info = normalized_pg_info(raw);
    std::string out = "{";
    bool first = true;
    json_field(out, first, "pgid", json_number(info.pgid));
    json_field(out, first, "committed_seq", json_number(info.committed_seq));
    json_field(out, first, "committed_length", json_number(info.committed_length));
    json_field(out, first, "image", json_object_image(info.image));
    json_field(out, first, "last_epoch_started", json_number(info.last_epoch_started));
    json_field(out, first, "last_interval_started", json_number(info.last_interval_started));
    json_field(out, first, "last_epoch_clean", json_number(info.last_epoch_clean));
    json_field(out, first, "epoch_created", json_number(info.epoch_created));
    json_field(out, first, "same_interval_since", json_number(info.same_interval_since));
    json_field(out, first, "same_up_since", json_number(info.same_up_since));
    json_field(out, first, "same_primary_since", json_number(info.same_primary_since));
    out += "}";
    return out;
}

static std::string json_peer_info_map(const std::map<osd_id_t, PeerInfo>& infos) {
    return json_array(infos, [](const auto& entry) {
        auto info = normalized_peer_info(entry.second);
        info.osd = entry.first;
        return json_peer_info(info);
    });
}

static std::string json_osd_set(const std::set<osd_id_t>& osds) {
    return json_array(osds, [](osd_id_t osd) { return json_number(osd); });
}

static std::string json_snapshot_checks(const PeeringStateMachine::Snapshot& snap) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "have_enough_info", json_bool(snapshot_have_enough_info(snap)));
    json_field(out, first, "image_invariant", json_bool(snapshot_image_invariant(snap)));
    json_field(out, first, "image_clean", json_bool(snapshot_image_clean(snap)));
    json_field(out, first, "image_recovering", json_bool(snapshot_image_recovering(snap)));
    out += "}";
    return out;
}

static std::string json_snapshot(const PeeringStateMachine::Snapshot& snap) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "state", json_string(state_name(snap.state)));
    json_field(out, first, "pgid", json_number(snap.pgid));
    json_field(out, first, "whoami", json_number(snap.whoami));
    json_field(out, first, "epoch", json_number(snap.epoch));
    json_field(out, first, "acting", json_acting_set(snap.acting));
    json_field(out, first, "up", json_acting_set(snap.up));
    json_field(out, first, "pool_size", json_number(snap.pool_size));
    json_field(out, first, "pool_min_size", json_number(snap.pool_min_size));
    json_field(out, first, "local_info", json_pg_info(snap.local_info));
    json_field(out, first, "auth_seq", json_number(snap.auth_seq));
    json_field(out, first, "auth_image", json_object_image(snap.auth_image));
    json_field(out, first, "auth_sources", json_authority_image(snap.auth_sources));
    json_field(out, first, "peer_info", json_peer_info_map(snap.peer_info));
    json_field(out, first, "peers_queried", json_osd_set(snap.peers_queried));
    json_field(out, first, "peers_responded", json_osd_set(snap.peers_responded));
    json_field(out, first, "prior_osds", json_osd_set(snap.prior_osds));
    json_field(out, first, "recovery_targets", json_osd_set(snap.recovery_targets));
    json_field(out, first, "peer_recovery_plans",
               json_array(snap.peer_recovery_plans, [](const PeerRecoveryPlan& plan) {
                   return json_peer_recovery_plan(plan);
               }));
    json_field(out, first, "local_recovery_plan",
               json_array(snap.local_recovery_plan, [](const ObjRecovery& item) {
                   return json_obj_recovery(item);
               }));
    json_field(out, first, "recovered", json_osd_set(snap.recovered));
    json_field(out, first, "timed_out_probes", json_osd_set(snap.timed_out_probes));
    json_field(out, first, "need_up_thru", json_bool(snap.need_up_thru));
    json_field(out, first, "activated", json_bool(snap.activated));
    json_field(out, first, "pending_acting_change", json_bool(snap.pending_acting_change));
    json_field(out, first, "last_peering_reset", json_number(snap.last_peering_reset));
    out += "}";
    return out;
}

static std::string json_event(const PeeringEvent& ev) {
    return std::visit([](const auto& e) -> std::string {
        using T = std::decay_t<decltype(e)>;
        std::string out = "{";
        bool first = true;
        if constexpr (std::is_same_v<T, event::Initialize>) {
            json_field(out, first, "type", json_string("Initialize"));
            json_field(out, first, "pgid", json_number(e.pgid));
            json_field(out, first, "whoami", json_number(e.whoami));
            json_field(out, first, "epoch", json_number(e.epoch));
            json_field(out, first, "acting", json_acting_set(e.acting));
            json_field(out, first, "up", json_acting_set(e.up));
            json_field(out, first, "pool_size", json_number(e.pool_size));
            json_field(out, first, "pool_min_size", json_number(e.pool_min_size));
            json_field(out, first, "local_info", json_pg_info(e.local_info));
            json_field(out, first, "prior_osds",
                       json_array(e.prior_osds, [](osd_id_t osd) { return json_number(osd); }));
        } else if constexpr (std::is_same_v<T, event::AdvanceMap>) {
            json_field(out, first, "type", json_string("AdvanceMap"));
            json_field(out, first, "new_epoch", json_number(e.new_epoch));
            json_field(out, first, "new_acting", json_acting_set(e.new_acting));
            json_field(out, first, "new_up", json_acting_set(e.new_up));
            json_field(out, first, "new_pool_size", json_number(e.new_pool_size));
            json_field(out, first, "new_pool_min_size", json_number(e.new_pool_min_size));
            json_field(out, first, "prior_osds",
                       json_array(e.prior_osds, [](osd_id_t osd) { return json_number(osd); }));
        } else if constexpr (std::is_same_v<T, event::PeerInfoReceived>) {
            json_field(out, first, "type", json_string("PeerInfoReceived"));
            json_field(out, first, "from", json_number(e.from));
            json_field(out, first, "info", json_peer_info(normalized_peer_info(e.info)));
            json_field(out, first, "query_epoch", json_number(e.query_epoch));
        } else if constexpr (std::is_same_v<T, event::PeerQueryTimeout>) {
            json_field(out, first, "type", json_string("PeerQueryTimeout"));
            json_field(out, first, "peer", json_number(e.peer));
        } else if constexpr (std::is_same_v<T, event::UpThruUpdated>) {
            json_field(out, first, "type", json_string("UpThruUpdated"));
            json_field(out, first, "epoch", json_number(e.epoch));
        } else if constexpr (std::is_same_v<T, event::ActivateCommitted>) {
            json_field(out, first, "type", json_string("ActivateCommitted"));
        } else if constexpr (std::is_same_v<T, event::RecoveryComplete>) {
            json_field(out, first, "type", json_string("RecoveryComplete"));
            json_field(out, first, "peer", json_number(e.peer));
            json_field(out, first, "epoch", json_number(e.epoch));
        } else if constexpr (std::is_same_v<T, event::AllReplicasRecovered>) {
            json_field(out, first, "type", json_string("AllReplicasRecovered"));
            json_field(out, first, "epoch", json_number(e.epoch));
            json_field(out, first, "peers",
                       json_array(e.peers, [](osd_id_t osd) { return json_number(osd); }));
        } else if constexpr (std::is_same_v<T, event::ReplicaActivate>) {
            json_field(out, first, "type", json_string("ReplicaActivate"));
            json_field(out, first, "from", json_number(e.from));
            json_field(out, first, "auth_info", json_peer_info(normalized_peer_info(e.auth_info)));
            json_field(out, first, "auth_sources", json_authority_image(e.auth_sources));
            json_field(out, first, "authoritative_seq", json_number(e.authoritative_seq));
            json_field(out, first, "activation_epoch", json_number(e.activation_epoch));
        } else if constexpr (std::is_same_v<T, event::ReplicaRecoveryComplete>) {
            json_field(out, first, "type", json_string("ReplicaRecoveryComplete"));
            json_field(out, first, "new_committed_seq", json_number(e.new_committed_seq));
            json_field(out, first, "new_committed_length", json_number(e.new_committed_length));
            json_field(out, first, "recovered_image", json_object_image(e.recovered_image));
            json_field(out, first, "activation_epoch", json_number(e.activation_epoch));
        } else if constexpr (std::is_same_v<T, event::DeleteStart>) {
            json_field(out, first, "type", json_string("DeleteStart"));
        } else if constexpr (std::is_same_v<T, event::DeleteComplete>) {
            json_field(out, first, "type", json_string("DeleteComplete"));
        }
        out += "}";
        return out;
    }, ev);
}

static std::string json_effect(const PeeringEffect& effect) {
    return std::visit([](const auto& fx) -> std::string {
        using T = std::decay_t<decltype(fx)>;
        std::string out = "{";
        bool first = true;
        if constexpr (std::is_same_v<T, effect::SendQuery>) {
            json_field(out, first, "type", json_string("SendQuery"));
            json_field(out, first, "target", json_number(fx.target));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "epoch", json_number(fx.epoch));
        } else if constexpr (std::is_same_v<T, effect::SendNotify>) {
            json_field(out, first, "type", json_string("SendNotify"));
            json_field(out, first, "target", json_number(fx.target));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "info", json_peer_info(normalized_peer_info(fx.info)));
            json_field(out, first, "epoch", json_number(fx.epoch));
        } else if constexpr (std::is_same_v<T, effect::SendActivate>) {
            json_field(out, first, "type", json_string("SendActivate"));
            json_field(out, first, "target", json_number(fx.target));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "auth_info", json_peer_info(normalized_peer_info(fx.auth_info)));
            json_field(out, first, "auth_sources", json_authority_image(fx.auth_sources));
            json_field(out, first, "authoritative_seq", json_number(fx.authoritative_seq));
            json_field(out, first, "activation_epoch", json_number(fx.activation_epoch));
        } else if constexpr (std::is_same_v<T, effect::ActivatePG>) {
            json_field(out, first, "type", json_string("ActivatePG"));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "authoritative_seq", json_number(fx.authoritative_seq));
            json_field(out, first, "authoritative_length", json_number(fx.authoritative_length));
            json_field(out, first, "authoritative_image", json_object_image(fx.authoritative_image));
            json_field(out, first, "activation_epoch", json_number(fx.activation_epoch));
        } else if constexpr (std::is_same_v<T, effect::DeactivatePG>) {
            json_field(out, first, "type", json_string("DeactivatePG"));
            json_field(out, first, "pgid", json_number(fx.pgid));
        } else if constexpr (std::is_same_v<T, effect::ScheduleRecovery>) {
            json_field(out, first, "type", json_string("ScheduleRecovery"));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "targets",
                       json_array(fx.targets, [](const effect::ScheduleRecovery::Target& target) {
                           std::string target_json = "{";
                           bool target_first = true;
                           json_field(target_json, target_first, "osd", json_number(target.osd));
                           json_field(target_json, target_first, "peer_length",
                                      json_number(target.peer_length));
                           json_field(target_json, target_first, "authoritative_length",
                                      json_number(target.authoritative_length));
                           json_field(target_json, target_first, "peer_committed_seq",
                                      json_number(target.peer_committed_seq));
                           json_field(target_json, target_first, "authoritative_seq",
                                      json_number(target.authoritative_seq));
                           json_field(target_json, target_first, "recoveries",
                                      json_array(target.recoveries, [](const ObjRecovery& item) {
                                          return json_obj_recovery(item);
                                      }));
                           target_json += "}";
                           return target_json;
                       }));
        } else if constexpr (std::is_same_v<T, effect::CancelRecovery>) {
            json_field(out, first, "type", json_string("CancelRecovery"));
            json_field(out, first, "pgid", json_number(fx.pgid));
        } else if constexpr (std::is_same_v<T, effect::MarkClean>) {
            json_field(out, first, "type", json_string("MarkClean"));
            json_field(out, first, "pgid", json_number(fx.pgid));
        } else if constexpr (std::is_same_v<T, effect::PersistState>) {
            json_field(out, first, "type", json_string("PersistState"));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "info", json_pg_info(fx.info));
        } else if constexpr (std::is_same_v<T, effect::RequestUpThru>) {
            json_field(out, first, "type", json_string("RequestUpThru"));
            json_field(out, first, "epoch", json_number(fx.epoch));
        } else if constexpr (std::is_same_v<T, effect::RequestActingChange>) {
            json_field(out, first, "type", json_string("RequestActingChange"));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "want_acting",
                       json_array(fx.want_acting, [](osd_id_t osd) {
                           return json_number(osd);
                       }));
        } else if constexpr (std::is_same_v<T, effect::UpdateHeartbeats>) {
            json_field(out, first, "type", json_string("UpdateHeartbeats"));
            json_field(out, first, "peers",
                       json_array(fx.peers, [](osd_id_t osd) { return json_number(osd); }));
        } else if constexpr (std::is_same_v<T, effect::PublishStats>) {
            json_field(out, first, "type", json_string("PublishStats"));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "state", json_string(state_name(fx.state)));
            json_field(out, first, "committed_seq", json_number(fx.committed_seq));
            json_field(out, first, "authoritative_seq", json_number(fx.authoritative_seq));
            json_field(out, first, "committed_length", json_number(fx.committed_length));
            json_field(out, first, "image", json_object_image(fx.image));
            json_field(out, first, "authoritative_image", json_object_image(fx.authoritative_image));
            json_field(out, first, "acting_size", json_number(fx.acting_size));
            json_field(out, first, "up_size", json_number(fx.up_size));
        } else if constexpr (std::is_same_v<T, effect::DeletePG>) {
            json_field(out, first, "type", json_string("DeletePG"));
            json_field(out, first, "pgid", json_number(fx.pgid));
        } else if constexpr (std::is_same_v<T, effect::LogTransition>) {
            json_field(out, first, "type", json_string("LogTransition"));
            json_field(out, first, "pgid", json_number(fx.pgid));
            json_field(out, first, "from", json_string(state_name(fx.from)));
            json_field(out, first, "to", json_string(state_name(fx.to)));
            json_field(out, first, "reason", json_string(fx.reason ? fx.reason : ""));
        }
        out += "}";
        return out;
    }, effect);
}

static void emit_jsonl_sequence_start(int sequence_idx, uint64_t seed) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "kind", json_string("sequence_start"));
    json_field(out, first, "sequence", json_number(sequence_idx));
    json_field(out, first, "seed", json_number(seed));
    out += "}";
    std::puts(out.c_str());
}

static void emit_jsonl_step(int sequence_idx, int step_idx, const PeeringEvent& event,
                            const PeeringStateMachine::SnapshotStepResult& result) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "kind", json_string("step"));
    json_field(out, first, "sequence", json_number(sequence_idx));
    json_field(out, first, "step", json_number(step_idx));
    json_field(out, first, "from_state", json_string(state_name(result.from)));
    json_field(out, first, "to_state", json_string(state_name(result.to)));
    json_field(out, first, "event", json_event(event));
    json_field(out, first, "before", json_snapshot(result.before));
    json_field(out, first, "before_checks", json_snapshot_checks(result.before));
    json_field(out, first, "after", json_snapshot(result.after));
    json_field(out, first, "after_checks", json_snapshot_checks(result.after));
    json_field(out, first, "effects",
               json_array(result.effects, [](const PeeringEffect& fx) {
                   return json_effect(fx);
               }));
    out += "}";
    std::puts(out.c_str());
}

static void emit_jsonl_summary(uint64_t seed, int sequences, int total_events) {
    std::string out = "{";
    bool first = true;
    json_field(out, first, "kind", json_string("summary"));
    json_field(out, first, "seed", json_number(seed));
    json_field(out, first, "sequences", json_number(sequences));
    json_field(out, first, "events", json_number(total_events));
    out += "}";
    std::puts(out.c_str());
}

// ── Main ─────────────────────────────────────────────────────────────

int main(int argc, char* argv[]) {
    uint64_t seed = 42;
    int num_sequences = 5;
    int num_events = 30;
    OutputFormat format = OutputFormat::Jsonl;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) {
            seed = strtoull(argv[++i], nullptr, 10);
        } else if (strcmp(argv[i], "--sequences") == 0 && i + 1 < argc) {
            num_sequences = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--events") == 0 && i + 1 < argc) {
            num_events = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--format") == 0 && i + 1 < argc) {
            const char* value = argv[++i];
            if (strcmp(value, "jsonl") == 0) {
                format = OutputFormat::Jsonl;
            } else if (strcmp(value, "legacy") == 0) {
                format = OutputFormat::Legacy;
            } else {
                fprintf(stderr, "Unknown format: %s\n", value);
                return 1;
            }
        } else if (strcmp(argv[i], "--help") == 0) {
            fprintf(stderr,
                    "Usage: %s [--seed N] [--sequences N] [--events N] "
                    "[--format jsonl|legacy]\n",
                    argv[0]);
            return 0;
        }
    }

    fprintf(stderr, "Cross-validation driver: seed=%lu sequences=%d events=%d format=%s\n",
            (unsigned long)seed, num_sequences, num_events,
            format == OutputFormat::Jsonl ? "jsonl" : "legacy");

    int total_events = 0;

    for (int seq_idx = 0; seq_idx < num_sequences; seq_idx++) {
        uint64_t s = seed + seq_idx;
        EventGenerator gen(s);
        PeeringStateMachine::Snapshot snap = PeeringStateMachine().snapshot();

        // Separator between sequences.
        if (format == OutputFormat::Legacy) {
            if (seq_idx > 0) printf("SEQUENCE\n");
        } else {
            emit_jsonl_sequence_start(seq_idx, s);
        }

        // Initialize.
        auto init_event = PeeringEvent(gen.gen_initialize());
        auto init_result = PeeringStateMachine::step(snap, init_event);
        if (format == OutputFormat::Legacy) {
            print_event(init_event);
            print_state(init_result.after);
        } else {
            emit_jsonl_step(seq_idx, 0, init_event, init_result);
        }
        snap = init_result.after;
        total_events++;

        // Generate events.
        int actual_events = std::uniform_int_distribution<int>(
            std::min(50, num_events), num_events)(gen.rng);

        for (int ev_idx = 1; ev_idx <= actual_events; ev_idx++) {
            auto event = gen.gen_event(snap);
            auto result = PeeringStateMachine::step(snap, event);
            if (format == OutputFormat::Legacy) {
                print_event(event);
                print_state(result.after);
            } else {
                emit_jsonl_step(seq_idx, ev_idx, event, result);
            }
            snap = result.after;
            total_events++;
        }
    }

    fprintf(stderr, "Done. Total events: %d\n", total_events);
    if (format == OutputFormat::Jsonl) {
        emit_jsonl_summary(seed, num_sequences, total_events);
    }
    return 0;
}
