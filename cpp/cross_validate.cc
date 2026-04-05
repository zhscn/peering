/*
 * Cross-validation driver: generates one random event trace, processes it
 * through the C++ state machine, and outputs replay traces.
 *
 * Protocol (stdout):
 *   Default: JSON Lines (`--format jsonl`)
 *     One structured object per replay step and final summary.
 *
 *   Compatibility: line-based legacy format (`--format legacy`)
 *     Kept for older exploratory tooling.
 *
 * Compile:
 *   cmake -S . -B build
 *   cmake --build build --target cross_validate
 *
 * Run:
 *   ./build/cpp/cross_validate --seed 42 --events 30
 *   ./build/cpp/cross_validate --profile lean-core --seed 1 --events 25
 */

#include <algorithm>
#include <cstdint>
#include <map>
#include <random>
#include <ranges>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include <CLI/CLI.hpp>
#include <fmt/core.h>
#include <fmt/ranges.h>
#include <glaze/glaze.hpp>

#include "peering_state.h"

using namespace vermilion::peering;
using namespace std::string_view_literals;

// ── JSON view types ─────────────────────────────────────────────────
//
// Glaze serializes these via C++23 aggregate reflection.
// View types exist for domain types that need transformation before
// serialization (ObjectImage→array, PeerInfo→normalized, enum→string).

struct ObjImageEntry {
  uint64_t obj{};
  uint64_t len{};
};

struct AuthImageEntry {
  uint64_t obj{};
  int32_t osd{};
  uint64_t len{};
};

struct BlobMetaEntry {
  uint64_t obj{};
  bool sealed{};
  std::optional<uint64_t> final_len;
};

struct PeerInfoView {
  int32_t osd{};
  uint64_t committed_seq{};
  uint64_t committed_length{};
  std::vector<ObjImageEntry> image;
  std::vector<BlobMetaEntry> blob_meta;
  uint32_t last_epoch_started{};
  uint32_t last_interval_started{};
};

struct PGInfoView {
  uint64_t pgid{};
  uint64_t committed_seq{};
  uint64_t committed_length{};
  std::vector<ObjImageEntry> image;
  std::vector<BlobMetaEntry> blob_meta;
  uint32_t last_epoch_started{};
  uint32_t last_interval_started{};
  uint32_t last_epoch_clean{};
  uint32_t epoch_created{};
  uint32_t same_interval_since{};
  uint32_t same_up_since{};
  uint32_t same_primary_since{};
};

struct ObjRecoveryView {
  uint64_t obj{};
  int32_t source{};
  uint64_t from_length{};
  uint64_t to_length{};
};

struct PeerRecoveryPlanView {
  int32_t target{};
  uint64_t peer_committed_seq{};
  uint64_t authoritative_seq{};
  std::vector<ObjRecoveryView> recoveries;
};

struct SnapshotChecksView {
  bool have_enough_info{};
  bool image_invariant{};
  bool image_clean{};
  bool image_recovering{};
};

struct SnapshotView {
  std::string state;
  uint64_t pgid{};
  int32_t whoami{};
  uint32_t epoch{};
  ActingSet acting;
  ActingSet up;
  int pool_size{};
  int pool_min_size{};
  PGInfoView local_info;
  uint64_t auth_seq{};
  std::vector<ObjImageEntry> auth_image;
  std::vector<AuthImageEntry> auth_sources;
  std::vector<BlobMetaEntry> auth_blob_meta;
  std::vector<PeerInfoView> peer_info;
  std::vector<int32_t> peers_queried;
  std::vector<int32_t> peers_responded;
  std::vector<int32_t> prior_osds;
  std::vector<int32_t> recovery_targets;
  std::vector<PeerRecoveryPlanView> peer_recovery_plans;
  std::vector<ObjRecoveryView> local_recovery_plan;
  std::vector<int32_t> recovered;
  std::vector<int32_t> timed_out_probes;
  bool need_up_thru{};
  bool activated{};
  bool pending_acting_change{};
  uint32_t last_peering_reset{};
};

// Event view types (for events with ObjectImage/PeerInfo/PGInfo fields)
struct InitializeView {
  std::string type = "Initialize";
  uint64_t pgid{};
  int32_t whoami{};
  uint32_t epoch{};
  ActingSet acting;
  ActingSet up;
  int pool_size{};
  int pool_min_size{};
  PGInfoView local_info;
  std::vector<int32_t> prior_osds;
};

struct PeerInfoReceivedView {
  std::string type = "PeerInfoReceived";
  int32_t from{};
  PeerInfoView info;
  uint32_t query_epoch{};
};

struct ReplicaActivateView {
  std::string type = "ReplicaActivate";
  int32_t from{};
  PeerInfoView auth_info;
  std::vector<AuthImageEntry> auth_sources;
  std::vector<BlobMetaEntry> auth_blob_meta;
  uint64_t authoritative_seq{};
  uint32_t activation_epoch{};
};

struct ReplicaRecoveryCompleteView {
  std::string type = "ReplicaRecoveryComplete";
  uint64_t new_committed_seq{};
  uint64_t new_committed_length{};
  std::vector<ObjImageEntry> recovered_image;
  uint32_t activation_epoch{};
};

// Effect view types
struct SendNotifyView {
  std::string type = "SendNotify";
  int32_t target{};
  uint64_t pgid{};
  PeerInfoView info;
  uint32_t epoch{};
};

struct SendActivateView {
  std::string type = "SendActivate";
  int32_t target{};
  uint64_t pgid{};
  PeerInfoView auth_info;
  std::vector<AuthImageEntry> auth_sources;
  std::vector<BlobMetaEntry> auth_blob_meta;
  uint64_t authoritative_seq{};
  uint32_t activation_epoch{};
};

struct ActivatePGView {
  std::string type = "ActivatePG";
  uint64_t pgid{};
  uint64_t authoritative_seq{};
  uint64_t authoritative_length{};
  std::vector<ObjImageEntry> authoritative_image;
  std::vector<BlobMetaEntry> authoritative_blob_meta;
  uint32_t activation_epoch{};
};

struct ScheduleRecoveryTargetView {
  int32_t osd{};
  uint64_t peer_length{};
  uint64_t authoritative_length{};
  uint64_t peer_committed_seq{};
  uint64_t authoritative_seq{};
  std::vector<ObjRecoveryView> recoveries;
};

struct ScheduleRecoveryView {
  std::string type = "ScheduleRecovery";
  uint64_t pgid{};
  std::vector<ScheduleRecoveryTargetView> targets;
};

struct PersistStateView {
  std::string type = "PersistState";
  uint64_t pgid{};
  PGInfoView info;
};

struct PublishStatsView {
  std::string type = "PublishStats";
  uint64_t pgid{};
  std::string state;
  uint64_t committed_seq{};
  uint64_t authoritative_seq{};
  uint64_t committed_length{};
  std::vector<ObjImageEntry> image;
  std::vector<ObjImageEntry> authoritative_image;
  std::vector<BlobMetaEntry> authoritative_blob_meta;
  int acting_size{};
  int up_size{};
};

struct LogTransitionView {
  std::string type = "LogTransition";
  uint64_t pgid{};
  std::string from;
  std::string to;
  std::string reason;
};

// Simple event/effect types serialized directly via tagged_json
struct SendQueryTagged {
  std::string type = "SendQuery";
  int32_t target{};
  uint64_t pgid{};
  uint32_t epoch{};
};

struct DeactivatePGTagged {
  std::string type = "DeactivatePG";
  uint64_t pgid{};
};

struct CancelRecoveryTagged {
  std::string type = "CancelRecovery";
  uint64_t pgid{};
};

struct MarkCleanTagged {
  std::string type = "MarkClean";
  uint64_t pgid{};
};

struct RequestUpThruTagged {
  std::string type = "RequestUpThru";
  uint32_t epoch{};
};

struct RequestActingChangeTagged {
  std::string type = "RequestActingChange";
  uint64_t pgid{};
  std::vector<int32_t> want_acting;
};

struct UpdateHeartbeatsTagged {
  std::string type = "UpdateHeartbeats";
  std::vector<int32_t> peers;
};

struct DeletePGTagged {
  std::string type = "DeletePG";
  uint64_t pgid{};
};

// Simple tagged event views (no complex nested types)
struct AdvanceMapTagged {
  std::string type = "AdvanceMap";
  uint32_t new_epoch{};
  ActingSet new_acting;
  ActingSet new_up;
  int new_pool_size{};
  int new_pool_min_size{};
  std::vector<int32_t> prior_osds;
};

struct PeerQueryTimeoutTagged {
  std::string type = "PeerQueryTimeout";
  int32_t peer{};
};

struct UpThruUpdatedTagged {
  std::string type = "UpThruUpdated";
  uint32_t epoch{};
};

struct ActivateCommittedTagged {
  std::string type = "ActivateCommitted";
};

struct RecoveryCompleteTagged {
  std::string type = "RecoveryComplete";
  int32_t peer{};
  uint32_t epoch{};
};

struct AllReplicasRecoveredTagged {
  std::string type = "AllReplicasRecovered";
  uint32_t epoch{};
  std::vector<int32_t> peers;
};

struct DeleteStartTagged {
  std::string type = "DeleteStart";
};

struct DeleteCompleteTagged {
  std::string type = "DeleteComplete";
};

// JSONL wrapper types
struct SummaryJson {
  std::string kind = "summary";
  uint64_t seed{};
  int events{};
};

struct StepJson {
  std::string kind = "step";
  int step{};
  std::string from_state;
  std::string to_state;
  glz::raw_json event;
  glz::raw_json before;
  glz::raw_json before_checks;
  glz::raw_json after;
  glz::raw_json after_checks;
  glz::raw_json effects;
};

// ── Conversion helpers ──────────────────────────────────────────────

static auto to_entries(const ObjectImage &img) -> std::vector<ObjImageEntry> {
  std::vector<ObjImageEntry> v;
  v.reserve(img.size());
  for (const auto &[k, val] : img)
    v.push_back({k, val});
  return v;
}

static auto to_entries(const AuthorityImage &auth)
    -> std::vector<AuthImageEntry> {
  std::vector<AuthImageEntry> v;
  v.reserve(auth.size());
  for (const auto &[k, a] : auth)
    v.push_back({k, a.authority_osd, a.authority_length});
  return v;
}

static auto to_entries(const BlobMetaImage &blob_meta)
    -> std::vector<BlobMetaEntry> {
  std::vector<BlobMetaEntry> v;
  v.reserve(blob_meta.size());
  for (const auto &[obj, meta] : blob_meta) {
    v.push_back({obj, meta.sealed, meta.final_len});
  }
  return v;
}

static auto to_vec(const std::set<osd_id_t> &s) -> std::vector<int32_t> {
  return {s.begin(), s.end()};
}

static auto to_recovery_view(const ObjRecovery &r) -> ObjRecoveryView {
  return {r.obj, r.source, r.from_length, r.to_length};
}

static auto to_recovery_views(const std::vector<ObjRecovery> &rs)
    -> std::vector<ObjRecoveryView> {
  std::vector<ObjRecoveryView> v;
  v.reserve(rs.size());
  for (const auto &r : rs)
    v.push_back(to_recovery_view(r));
  return v;
}

static auto to_plan_view(const PeerRecoveryPlan &p) -> PeerRecoveryPlanView {
  return {p.target, p.peer_committed_seq, p.authoritative_seq,
          to_recovery_views(p.recoveries)};
}

static auto to_plan_views(const std::vector<PeerRecoveryPlan> &plans)
    -> std::vector<PeerRecoveryPlanView> {
  std::vector<PeerRecoveryPlanView> v;
  v.reserve(plans.size());
  for (const auto &p : plans)
    v.push_back(to_plan_view(p));
  return v;
}

static auto to_peer_info_view(const PeerInfo &raw) -> PeerInfoView {
  auto info = normalized_peer_info(raw);
  return {info.osd,
          info.committed_seq,
          info.committed_length,
          to_entries(effective_image(info)),
          to_entries(info.blob_meta),
          info.last_epoch_started,
          info.last_interval_started};
}

static auto to_pg_info_view(const PGInfo &raw) -> PGInfoView {
  auto info = normalized_pg_info(raw);
  return {info.pgid,
          info.committed_seq,
          info.committed_length,
          to_entries(info.image),
          to_entries(info.blob_meta),
          info.last_epoch_started,
          info.last_interval_started,
          info.last_epoch_clean,
          info.epoch_created,
          info.same_interval_since,
          info.same_up_since,
          info.same_primary_since};
}

static auto to_peer_info_views(const std::map<osd_id_t, PeerInfo> &infos)
    -> std::vector<PeerInfoView> {
  std::vector<PeerInfoView> v;
  v.reserve(infos.size());
  for (const auto &[osd, info] : infos) {
    auto view = to_peer_info_view(info);
    view.osd = osd;
    v.push_back(std::move(view));
  }
  return v;
}

// ── Glaze serialization ─────────────────────────────────────────────

template <typename T> static auto to_json_str(const T &value) -> std::string {
  std::string buf;
  [[maybe_unused]] auto ec = glz::write_json(value, buf);
  return buf;
}

// ── Snapshot view conversion ────────────────────────────────────────

static auto to_snapshot_view(const PeeringStateMachine::Snapshot &snap)
    -> SnapshotView {
  return {
      .state = state_name(snap.state),
      .pgid = snap.pgid,
      .whoami = snap.whoami,
      .epoch = snap.epoch,
      .acting = snap.acting,
      .up = snap.up,
      .pool_size = snap.pool_size,
      .pool_min_size = snap.pool_min_size,
      .local_info = to_pg_info_view(snap.local_info),
      .auth_seq = snap.auth_seq,
      .auth_image = to_entries(snap.auth_image),
      .auth_sources = to_entries(snap.auth_sources),
      .auth_blob_meta = to_entries(snap.auth_blob_meta),
      .peer_info = to_peer_info_views(snap.peer_info),
      .peers_queried = to_vec(snap.peers_queried),
      .peers_responded = to_vec(snap.peers_responded),
      .prior_osds = to_vec(snap.prior_osds),
      .recovery_targets = to_vec(snap.recovery_targets),
      .peer_recovery_plans = to_plan_views(snap.peer_recovery_plans),
      .local_recovery_plan = to_recovery_views(snap.local_recovery_plan),
      .recovered = to_vec(snap.recovered),
      .timed_out_probes = to_vec(snap.timed_out_probes),
      .need_up_thru = snap.need_up_thru,
      .activated = snap.activated,
      .pending_acting_change = snap.pending_acting_change,
      .last_peering_reset = snap.last_peering_reset,
  };
}

// ── Event / Effect JSON serialization ───────────────────────────────

template <typename... Ts> struct overloaded : Ts... {
  using Ts::operator()...;
};

static auto event_to_json(const PeeringEvent &ev) -> std::string {
  return std::visit(
      overloaded{
          [](const event::Initialize &e) {
            return to_json_str(InitializeView{
                .type = "Initialize",
                .pgid = e.pgid,
                .whoami = e.whoami,
                .epoch = e.epoch,
                .acting = e.acting,
                .up = e.up,
                .pool_size = e.pool_size,
                .pool_min_size = e.pool_min_size,
                .local_info = to_pg_info_view(e.local_info),
                .prior_osds = {e.prior_osds.begin(), e.prior_osds.end()},
            });
          },
          [](const event::AdvanceMap &e) {
            return to_json_str(AdvanceMapTagged{
                .type = "AdvanceMap",
                .new_epoch = e.new_epoch,
                .new_acting = e.new_acting,
                .new_up = e.new_up,
                .new_pool_size = e.new_pool_size,
                .new_pool_min_size = e.new_pool_min_size,
                .prior_osds = {e.prior_osds.begin(), e.prior_osds.end()},
            });
          },
          [](const event::PeerInfoReceived &e) {
            auto info = normalized_peer_info(e.info);
            return to_json_str(PeerInfoReceivedView{
                .type = "PeerInfoReceived",
                .from = e.from,
                .info = to_peer_info_view(info),
                .query_epoch = e.query_epoch,
            });
          },
          [](const event::PeerQueryTimeout &e) {
            return to_json_str(PeerQueryTimeoutTagged{
                .type = "PeerQueryTimeout",
                .peer = e.peer,
            });
          },
          [](const event::UpThruUpdated &e) {
            return to_json_str(UpThruUpdatedTagged{
                .type = "UpThruUpdated",
                .epoch = e.epoch,
            });
          },
          [](const event::ActivateCommitted &) {
            return to_json_str(
                ActivateCommittedTagged{.type = "ActivateCommitted"});
          },
          [](const event::RecoveryComplete &e) {
            return to_json_str(RecoveryCompleteTagged{
                .type = "RecoveryComplete",
                .peer = e.peer,
                .epoch = e.epoch,
            });
          },
          [](const event::AllReplicasRecovered &e) {
            return to_json_str(AllReplicasRecoveredTagged{
                .type = "AllReplicasRecovered",
                .epoch = e.epoch,
                .peers = {e.peers.begin(), e.peers.end()},
            });
          },
          [](const event::ReplicaActivate &e) {
            return to_json_str(ReplicaActivateView{
                .type = "ReplicaActivate",
                .from = e.from,
                .auth_info = to_peer_info_view(e.auth_info),
                .auth_sources = to_entries(e.auth_sources),
                .auth_blob_meta = to_entries(e.auth_blob_meta),
                .authoritative_seq = e.authoritative_seq,
                .activation_epoch = e.activation_epoch,
            });
          },
          [](const event::ReplicaRecoveryComplete &e) {
            return to_json_str(ReplicaRecoveryCompleteView{
                .type = "ReplicaRecoveryComplete",
                .new_committed_seq = e.new_committed_seq,
                .new_committed_length = e.new_committed_length,
                .recovered_image = to_entries(e.recovered_image),
                .activation_epoch = e.activation_epoch,
            });
          },
          [](const event::DeleteStart &) {
            return to_json_str(DeleteStartTagged{.type = "DeleteStart"});
          },
          [](const event::DeleteComplete &) {
            return to_json_str(DeleteCompleteTagged{.type = "DeleteComplete"});
          },
      },
      ev);
}

static auto effect_to_json(const PeeringEffect &fx) -> std::string {
  return std::visit(
      overloaded{
          [](const effect::SendQuery &f) {
            return to_json_str(SendQueryTagged{
                .type = "SendQuery",
                .target = f.target,
                .pgid = f.pgid,
                .epoch = f.epoch,
            });
          },
          [](const effect::SendNotify &f) {
            return to_json_str(SendNotifyView{
                .type = "SendNotify",
                .target = f.target,
                .pgid = f.pgid,
                .info = to_peer_info_view(f.info),
                .epoch = f.epoch,
            });
          },
          [](const effect::SendActivate &f) {
            return to_json_str(SendActivateView{
                .type = "SendActivate",
                .target = f.target,
                .pgid = f.pgid,
                .auth_info = to_peer_info_view(f.auth_info),
                .auth_sources = to_entries(f.auth_sources),
                .auth_blob_meta = to_entries(f.auth_blob_meta),
                .authoritative_seq = f.authoritative_seq,
                .activation_epoch = f.activation_epoch,
            });
          },
          [](const effect::ActivatePG &f) {
            return to_json_str(ActivatePGView{
                .type = "ActivatePG",
                .pgid = f.pgid,
                .authoritative_seq = f.authoritative_seq,
                .authoritative_length = f.authoritative_length,
                .authoritative_image = to_entries(f.authoritative_image),
                .authoritative_blob_meta =
                    to_entries(f.authoritative_blob_meta),
                .activation_epoch = f.activation_epoch,
            });
          },
          [](const effect::DeactivatePG &f) {
            return to_json_str(
                DeactivatePGTagged{.type = "DeactivatePG", .pgid = f.pgid});
          },
          [](const effect::ScheduleRecovery &f) {
            std::vector<ScheduleRecoveryTargetView> targets;
            targets.reserve(f.targets.size());
            for (const auto &t : f.targets) {
              targets.push_back({
                  .osd = t.osd,
                  .peer_length = t.peer_length,
                  .authoritative_length = t.authoritative_length,
                  .peer_committed_seq = t.peer_committed_seq,
                  .authoritative_seq = t.authoritative_seq,
                  .recoveries = to_recovery_views(t.recoveries),
              });
            }
            return to_json_str(ScheduleRecoveryView{
                .type = "ScheduleRecovery",
                .pgid = f.pgid,
                .targets = std::move(targets),
            });
          },
          [](const effect::CancelRecovery &f) {
            return to_json_str(
                CancelRecoveryTagged{.type = "CancelRecovery", .pgid = f.pgid});
          },
          [](const effect::MarkClean &f) {
            return to_json_str(
                MarkCleanTagged{.type = "MarkClean", .pgid = f.pgid});
          },
          [](const effect::PersistState &f) {
            return to_json_str(PersistStateView{
                .type = "PersistState",
                .pgid = f.pgid,
                .info = to_pg_info_view(f.info),
            });
          },
          [](const effect::RequestUpThru &f) {
            return to_json_str(
                RequestUpThruTagged{.type = "RequestUpThru", .epoch = f.epoch});
          },
          [](const effect::RequestActingChange &f) {
            return to_json_str(RequestActingChangeTagged{
                .type = "RequestActingChange",
                .pgid = f.pgid,
                .want_acting = {f.want_acting.begin(), f.want_acting.end()},
            });
          },
          [](const effect::UpdateHeartbeats &f) {
            return to_json_str(UpdateHeartbeatsTagged{
                .type = "UpdateHeartbeats",
                .peers = {f.peers.begin(), f.peers.end()},
            });
          },
          [](const effect::PublishStats &f) {
            return to_json_str(PublishStatsView{
                .type = "PublishStats",
                .pgid = f.pgid,
                .state = state_name(f.state),
                .committed_seq = f.committed_seq,
                .authoritative_seq = f.authoritative_seq,
                .committed_length = f.committed_length,
                .image = to_entries(f.image),
                .authoritative_image = to_entries(f.authoritative_image),
                .authoritative_blob_meta =
                    to_entries(f.authoritative_blob_meta),
                .acting_size = f.acting_size,
                .up_size = f.up_size,
            });
          },
          [](const effect::DeletePG &f) {
            return to_json_str(
                DeletePGTagged{.type = "DeletePG", .pgid = f.pgid});
          },
          [](const effect::LogTransition &f) {
            return to_json_str(LogTransitionView{
                .type = "LogTransition",
                .pgid = f.pgid,
                .from = state_name(f.from),
                .to = state_name(f.to),
                .reason = f.reason ? f.reason : "",
            });
          },
      },
      fx);
}

static auto effects_to_json(const std::vector<PeeringEffect> &effects)
    -> std::string {
  std::string buf = "[";
  for (size_t i = 0; i < effects.size(); ++i) {
    if (i > 0)
      buf += ',';
    buf += effect_to_json(effects[i]);
  }
  buf += ']';
  return buf;
}

// ── Validation helpers (unchanged logic) ────────────────────────────

static auto observed_auth_seq(const std::vector<PeerInfo> &infos)
    -> journal_seq_t {
  journal_seq_t seq = 0;
  for (const auto &raw : infos) {
    auto info = normalized_peer_info(raw);
    seq = std::max(seq, info.committed_seq);
  }
  return seq;
}

static auto known_peer_images(const PeeringStateMachine::Snapshot &snap)
    -> std::vector<PeerInfo> {
  std::vector<PeerInfo> peers;
  peers.reserve(snap.peer_info.size() + 1);
  for (const auto &[osd, info] : snap.peer_info) {
    if (osd == snap.whoami)
      continue;
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
      .blob_meta = local.blob_meta,
      .last_epoch_started = local.last_epoch_started,
      .last_interval_started = local.last_interval_started,
  });
  return peers;
}

static auto acting_replica_images(const PeeringStateMachine::Snapshot &snap)
    -> std::vector<PeerInfo> {
  std::vector<PeerInfo> peers;
  for (auto osd : snap.acting.osds) {
    if (osd < 0 || osd == snap.whoami)
      continue;
    auto it = snap.peer_info.find(osd);
    if (it != snap.peer_info.end()) {
      auto copy = normalized_peer_info(it->second);
      copy.osd = osd;
      peers.push_back(std::move(copy));
    } else {
      peers.push_back(PeerInfo{.osd = osd});
    }
  }
  return peers;
}

static bool
snapshot_have_enough_info(const PeeringStateMachine::Snapshot &snap) {
  for (auto osd : snap.peers_queried) {
    if (!snap.peers_responded.contains(osd))
      return false;
  }
  for (auto osd : snap.acting.osds) {
    if (osd >= 0 && osd != snap.whoami && !snap.peers_responded.contains(osd))
      return false;
  }
  return true;
}

static bool
snapshot_image_invariant(const PeeringStateMachine::Snapshot &snap) {
  auto known_peers = known_peer_images(snap);
  auto recomputed_sources = authoritative_sources(known_peers);
  auto recomputed_image = authority_image_values(recomputed_sources);
  auto recomputed_blob_meta =
      authoritative_blob_meta(known_peers, recomputed_sources);
  auto recomputed_seq = observed_auth_seq(known_peers);
  auto expected_peer_plans = build_peer_recovery_plans(
      recomputed_sources, recomputed_seq, acting_replica_images(snap));
  auto expected_local_plan =
      pg_image_recovery_plan(recomputed_sources, snap.local_info);

  for (const auto &[obj, auth] : snap.auth_sources) {
    bool backed = std::ranges::any_of(known_peers, [&](const PeerInfo &peer) {
      return lookup_length(effective_image(peer), obj) == auth.authority_length;
    });
    if (!backed)
      return false;
  }
  if (!same_image(snap.auth_image, recomputed_image))
    return false;
  if (snap.auth_seq != recomputed_seq)
    return false;
  if (!same_image(authority_image_values(snap.auth_sources), recomputed_image))
    return false;
  if (snap.auth_blob_meta != recomputed_blob_meta)
    return false;
  if (snap.local_info.committed_seq > snap.auth_seq)
    return false;
  if (!prefix_image(effective_image(snap.local_info), snap.auth_image))
    return false;
  for (const auto &peer : acting_replica_images(snap)) {
    if (peer.committed_seq > snap.auth_seq)
      return false;
    if (!prefix_image(effective_image(peer), snap.auth_image))
      return false;
  }
  if (snap.peer_recovery_plans != expected_peer_plans)
    return false;
  if (snap.local_recovery_plan != expected_local_plan)
    return false;
  return true;
}

static bool snapshot_image_clean(const PeeringStateMachine::Snapshot &snap) {
  if (!snapshot_image_invariant(snap))
    return false;
  if (!snap.peer_recovery_plans.empty() || !snap.local_recovery_plan.empty())
    return false;
  if (snap.local_info.committed_seq < snap.auth_seq ||
      !same_image(effective_image(snap.local_info), snap.auth_image))
    return false;
  for (const auto &peer : acting_replica_images(snap)) {
    if (peer.committed_seq < snap.auth_seq ||
        !same_image(effective_image(peer), snap.auth_image))
      return false;
  }
  return true;
}

static bool
snapshot_image_recovering(const PeeringStateMachine::Snapshot &snap) {
  bool peer_seq_lag =
      std::ranges::any_of(acting_replica_images(snap), [&](const PeerInfo &p) {
        return p.committed_seq < snap.auth_seq;
      });
  return snapshot_image_invariant(snap) && !snapshot_image_clean(snap) &&
         (!snap.peer_recovery_plans.empty() ||
          !snap.local_recovery_plan.empty() ||
          snap.local_info.committed_seq < snap.auth_seq || peer_seq_lag);
}

static auto to_checks_view(const PeeringStateMachine::Snapshot &snap)
    -> SnapshotChecksView {
  return {
      .have_enough_info = snapshot_have_enough_info(snap),
      .image_invariant = snapshot_image_invariant(snap),
      .image_clean = snapshot_image_clean(snap),
      .image_recovering = snapshot_image_recovering(snap),
  };
}

// ── Event generator ─────────────────────────────────────────────────

enum class OutputFormat { Legacy, Jsonl };
enum class EventProfile { Full, LeanCore };

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
  EventProfile profile;

  explicit EventGenerator(uint64_t seed,
                          EventProfile profile = EventProfile::Full)
      : rng(seed), profile(profile) {}

  TestConfig gen_config() {
    TestConfig c;
    c.num_osds = std::uniform_int_distribution<int>(2, 5)(rng);
    c.pool_size =
        std::uniform_int_distribution<int>(2, std::min(c.num_osds, 3))(rng);
    c.pool_min_size = std::uniform_int_distribution<int>(1, c.pool_size)(rng);
    c.current_epoch = 10;
    std::vector<osd_id_t> all_osds;
    for (int i = 0; i < c.num_osds; i++)
      all_osds.push_back(i);
    std::ranges::shuffle(all_osds, rng);
    c.initial_acting.assign(
        all_osds.begin(),
        all_osds.begin() +
            std::min(static_cast<int>(all_osds.size()), c.pool_size));
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
        .acting =
            ActingSet{.osds = cfg.initial_acting, .epoch = cfg.current_epoch},
        .up = ActingSet{.osds = cfg.initial_acting, .epoch = cfg.current_epoch},
        .pool_size = cfg.pool_size,
        .pool_min_size = cfg.pool_min_size,
        .local_info =
            PGInfo{
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
    for (int i = 0; i < cfg.num_osds; i++)
      all_osds.push_back(i);
    std::ranges::shuffle(all_osds, rng);
    int sz = std::uniform_int_distribution<int>(
        1, std::min(cfg.num_osds, cfg.pool_size))(rng);
    std::vector<osd_id_t> result(all_osds.begin(), all_osds.begin() + sz);
    if (std::uniform_int_distribution<int>(0, 4)(rng) < 4) {
      auto it = std::ranges::find(result, cfg.whoami);
      if (it != result.end()) {
        std::swap(*it, result[0]);
      } else {
        result[0] = cfg.whoami;
      }
    }
    return result;
  }

  PeeringEvent gen_event(const PeeringStateMachine::Snapshot &snap) {
    if (profile == EventProfile::LeanCore) {
      return gen_lean_core_event(snap);
    }
    int choice = std::uniform_int_distribution<int>(0, 99)(rng);
    switch (snap.state) {
    case State::Initial:
      return gen_advance_map(snap);
    case State::GetPeerInfo:
      if (choice < 50)
        return gen_peer_info_received(snap);
      if (choice < 70)
        return gen_peer_query_timeout(snap);
      if (choice < 85)
        return gen_advance_map(snap);
      return gen_delete_start();
    case State::WaitUpThru:
      if (choice < 40)
        return gen_up_thru_updated(snap);
      if (choice < 60)
        return gen_peer_info_received(snap);
      if (choice < 80)
        return gen_advance_map(snap);
      return gen_delete_start();
    case State::Active:
      if (choice < 30)
        return gen_advance_map(snap);
      if (choice < 50)
        return event::ActivateCommitted{};
      if (choice < 65)
        return gen_all_replicas_recovered(snap);
      if (choice < 80)
        return gen_recovery_complete(snap);
      return gen_delete_start();
    case State::Recovering:
      if (choice < 40)
        return gen_recovery_complete(snap);
      if (choice < 55)
        return gen_all_replicas_recovered(snap);
      if (choice < 75)
        return gen_advance_map(snap);
      if (choice < 85)
        return event::ActivateCommitted{};
      return gen_delete_start();
    case State::Clean:
      if (choice < 50)
        return gen_advance_map(snap);
      if (choice < 70)
        return event::ActivateCommitted{};
      if (choice < 85)
        return gen_advance_map(snap);
      return gen_delete_start();
    case State::Stray:
      if (choice < 40)
        return gen_replica_activate(snap);
      if (choice < 70)
        return gen_advance_map(snap);
      return gen_delete_start();
    case State::ReplicaActive:
      if (choice < 30)
        return gen_replica_recovery_complete(snap);
      if (choice < 60)
        return gen_advance_map(snap);
      if (choice < 80)
        return gen_replica_activate(snap);
      return gen_delete_start();
    case State::Down:
      if (choice < 40)
        return gen_peer_info_received(snap);
      if (choice < 70)
        return gen_advance_map(snap);
      if (choice < 85)
        return gen_peer_query_timeout(snap);
      return gen_delete_start();
    case State::Incomplete:
      if (choice < 40)
        return gen_peer_info_received(snap);
      if (choice < 70)
        return gen_advance_map(snap);
      return gen_delete_start();
    case State::Deleting:
      if (choice < 50)
        return event::DeleteComplete{};
      return gen_advance_map(snap);
    default:
      return gen_advance_map(snap);
    }
  }

  PeeringEvent gen_lean_core_event(const PeeringStateMachine::Snapshot &snap) {
    int choice = std::uniform_int_distribution<int>(0, 99)(rng);
    switch (snap.state) {
    case State::Initial:
      return gen_advance_map(snap);
    case State::GetPeerInfo:
      if (choice < 55)
        return gen_peer_info_received(snap);
      if (choice < 80)
        return gen_peer_query_timeout(snap);
      return gen_advance_map(snap);
    case State::WaitUpThru:
      if (choice < 45)
        return gen_up_thru_updated(snap);
      if (choice < 75)
        return gen_peer_info_received(snap);
      return gen_advance_map(snap);
    case State::Active:
      if (choice < 20)
        return gen_advance_map(snap);
      if (choice < 50)
        return event::ActivateCommitted{};
      if (choice < 75)
        return gen_all_replicas_recovered(snap);
      return gen_recovery_complete(snap);
    case State::Recovering:
      if (choice < 20)
        return gen_advance_map(snap);
      if (choice < 55)
        return gen_recovery_complete(snap);
      if (choice < 80)
        return gen_all_replicas_recovered(snap);
      return event::ActivateCommitted{};
    case State::Clean:
      if (choice < 35)
        return gen_advance_map(snap);
      return event::ActivateCommitted{};
    case State::Stray:
      if (choice < 35)
        return gen_advance_map(snap);
      return gen_replica_activate(snap);
    case State::ReplicaActive:
      if (choice < 20)
        return gen_advance_map(snap);
      if (choice < 68)
        return gen_replica_recovery_complete(snap);
      return gen_replica_activate(snap);
    case State::Down:
      if (choice < 45)
        return gen_peer_info_received(snap);
      if (choice < 75)
        return gen_peer_query_timeout(snap);
      return gen_advance_map(snap);
    case State::Incomplete:
      if (choice < 70)
        return gen_peer_info_received(snap);
      return gen_advance_map(snap);
    case State::Deleting:
      return event::DeleteComplete{};
    default:
      return gen_advance_map(snap);
    }
  }

  event::AdvanceMap gen_advance_map(const PeeringStateMachine::Snapshot &snap) {
    epoch_t new_epoch = snap.epoch + 1;
    cfg.current_epoch = new_epoch;
    bool new_interval = std::uniform_int_distribution<int>(0, 9)(rng) < 4;
    auto new_acting_osds = new_interval
                               ? random_acting_set()
                               : std::vector<osd_id_t>(snap.acting.osds);
    int new_pool_size = snap.pool_size;
    int new_pool_min_size = snap.pool_min_size;
    if (std::uniform_int_distribution<int>(0, 9)(rng) == 0) {
      new_pool_min_size =
          std::uniform_int_distribution<int>(1, new_pool_size)(rng);
    }
    std::vector<osd_id_t> prior;
    if (new_interval && std::uniform_int_distribution<int>(0, 2)(rng) == 0) {
      int n = std::uniform_int_distribution<int>(1, 2)(rng);
      for (int i = 0; i < n; i++)
        prior.push_back(random_osd());
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

  event::PeerInfoReceived
  gen_peer_info_received(const PeeringStateMachine::Snapshot &snap) {
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
        .info =
            PeerInfo{
                .osd = from,
                .committed_seq = len,
                .committed_length = len,
                .image = primary_image(len),
                .last_epoch_started = les,
            },
        .query_epoch = qe,
    };
  }

  event::PeerQueryTimeout
  gen_peer_query_timeout(const PeeringStateMachine::Snapshot &) {
    return event::PeerQueryTimeout{.peer = random_peer()};
  }

  event::UpThruUpdated
  gen_up_thru_updated(const PeeringStateMachine::Snapshot &snap) {
    epoch_t ep = snap.epoch;
    if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
      ep = snap.epoch > 1 ? snap.epoch - 1 : 1;
    }
    return event::UpThruUpdated{.epoch = ep};
  }

  event::RecoveryComplete
  gen_recovery_complete(const PeeringStateMachine::Snapshot &snap) {
    osd_id_t peer;
    if (!snap.recovery_targets.empty() &&
        std::uniform_int_distribution<int>(0, 2)(rng) < 2) {
      auto it = snap.recovery_targets.begin();
      std::advance(
          it, std::uniform_int_distribution<int>(
                  0, static_cast<int>(snap.recovery_targets.size()) - 1)(rng));
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

  event::AllReplicasRecovered
  gen_all_replicas_recovered(const PeeringStateMachine::Snapshot &snap) {
    epoch_t ep = snap.last_peering_reset;
    if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
      ep = snap.last_peering_reset > 1 ? snap.last_peering_reset - 1 : 0;
    }
    std::vector<osd_id_t> peers;
    for (osd_id_t peer : snap.recovery_targets) {
      if (!snap.recovered.contains(peer))
        peers.push_back(peer);
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

  event::ReplicaActivate
  gen_replica_activate(const PeeringStateMachine::Snapshot &snap) {
    osd_id_t from = snap.acting.primary();
    if (from < 0)
      from = random_peer();
    epoch_t ep = snap.epoch;
    if (std::uniform_int_distribution<int>(0, 4)(rng) == 0) {
      ep = snap.epoch > 1 ? snap.epoch - 1 : 1;
    }
    if (profile == EventProfile::LeanCore) {
      auto auth_image = snap.auth_image;
      auto auth_sources = snap.auth_sources;
      auto auth_blob_meta = snap.auth_blob_meta;
      return event::ReplicaActivate{
          .from = from,
          .auth_info =
              PeerInfo{
                  .osd = from,
                  .committed_seq = snap.auth_seq,
                  .committed_length = primary_length(auth_image),
                  .image = auth_image,
                  .blob_meta = auth_blob_meta,
                  .last_epoch_started = ep,
                  .last_interval_started = ep,
              },
          .auth_sources = auth_sources,
          .auth_blob_meta = auth_blob_meta,
          .authoritative_seq = snap.auth_seq,
          .activation_epoch = ep,
      };
    }
    uint64_t len = std::uniform_int_distribution<uint64_t>(50, 300)(rng);
    return event::ReplicaActivate{
        .from = from,
        .auth_info =
            PeerInfo{
                .osd = from,
                .committed_seq = snap.auth_seq > 0 ? snap.auth_seq : len,
                .committed_length = len,
                .image = snap.auth_image.empty() ? primary_image(len)
                                                 : snap.auth_image,
                .blob_meta = snap.auth_blob_meta,
                .last_epoch_started = ep,
            },
        .auth_sources = snap.auth_sources,
        .auth_blob_meta = snap.auth_blob_meta,
        .authoritative_seq = snap.auth_seq > 0 ? snap.auth_seq : len,
        .activation_epoch = ep,
    };
  }

  event::ReplicaRecoveryComplete
  gen_replica_recovery_complete(const PeeringStateMachine::Snapshot &snap) {
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
        .recovered_image =
            snap.auth_image.empty() ? primary_image(len) : snap.auth_image,
        .activation_epoch = ep,
    };
  }

  event::DeleteStart gen_delete_start() { return event::DeleteStart{}; }
};

// ── Legacy output helpers ───────────────────────────────────────────

static void print_object_image(const ObjectImage &image) {
  if (image.empty())
    return;
  bool first = true;
  for (const auto &[obj, len] : image) {
    if (!first)
      fmt::print(" ");
    fmt::print("{}:{}", obj, len);
    first = false;
  }
}

static void print_osd_list(std::string_view label,
                           const std::vector<osd_id_t> &osds) {
  fmt::print("{}", label);
  fmt::print("{}", fmt::join(osds, " "));
  fmt::print("\n");
}

static void print_osd_vector(const std::vector<osd_id_t> &osds) {
  fmt::print("{}", fmt::join(osds, " "));
}

static void print_osd_set(const std::set<osd_id_t> &osds) {
  bool first = true;
  for (auto osd : osds) {
    if (!first)
      fmt::print(" ");
    fmt::print("{}", osd);
    first = false;
  }
}

static void print_prefixed_auth_source_lines(std::string_view label,
                                             const AuthorityImage &auth) {
  for (const auto &[obj, item] : auth) {
    fmt::print("{} {} {} {}\n", label, obj, item.authority_osd,
               item.authority_length);
  }
}

static void print_prefixed_blob_meta_lines(std::string_view label,
                                           const BlobMetaImage &blob_meta) {
  for (const auto &[obj, item] : blob_meta) {
    fmt::print("{} {} {} ", label, obj, item.sealed ? 1 : 0);
    if (item.final_len.has_value()) {
      fmt::print("{}\n", *item.final_len);
    } else {
      fmt::print("-1\n");
    }
  }
}

static void print_event(const PeeringEvent &ev) {
  std::visit(
      overloaded{
          [](const event::Initialize &e) {
            fmt::print("IMAGE_EVENT Initialize\n");
            fmt::print("pgid {}\n", e.pgid);
            fmt::print("whoami {}\n", e.whoami);
            fmt::print("epoch {}\n", e.epoch);
            print_osd_list("acting ", e.acting.osds);
            print_osd_list("up ", e.up.osds);
            fmt::print("pool_size {}\n", e.pool_size);
            fmt::print("pool_min_size {}\n", e.pool_min_size);
            fmt::print("local_image ");
            print_object_image(effective_image(e.local_info));
            fmt::print("\n");
            fmt::print("local_committed_seq {}\n", e.local_info.committed_seq);
            fmt::print("last_epoch_started {}\n",
                       e.local_info.last_epoch_started);
            fmt::print("last_interval_started {}\n",
                       e.local_info.last_interval_started);
            fmt::print("last_epoch_clean {}\n", e.local_info.last_epoch_clean);
            print_osd_list("prior_osds ", e.prior_osds);
          },
          [](const event::AdvanceMap &e) {
            fmt::print("IMAGE_EVENT AdvanceMap\n");
            fmt::print("new_epoch {}\n", e.new_epoch);
            print_osd_list("new_acting ", e.new_acting.osds);
            print_osd_list("new_up ", e.new_up.osds);
            fmt::print("new_pool_size {}\n", e.new_pool_size);
            fmt::print("new_pool_min_size {}\n", e.new_pool_min_size);
            print_osd_list("prior_osds ", e.prior_osds);
          },
          [](const event::PeerInfoReceived &e) {
            fmt::print("IMAGE_EVENT PeerImageReceived\n");
            fmt::print("from {}\n", e.from);
            fmt::print("peer_image ");
            print_object_image(effective_image(e.info));
            fmt::print("\n");
            fmt::print("peer_committed_seq {}\n", e.info.committed_seq);
            fmt::print("last_epoch_started {}\n", e.info.last_epoch_started);
            fmt::print("query_epoch {}\n", e.query_epoch);
          },
          [](const event::PeerQueryTimeout &e) {
            fmt::print("IMAGE_EVENT PeerQueryTimeout\n");
            fmt::print("peer {}\n", e.peer);
          },
          [](const event::UpThruUpdated &e) {
            fmt::print("IMAGE_EVENT UpThruUpdated\n");
            fmt::print("epoch {}\n", e.epoch);
          },
          [](const event::ActivateCommitted &) {
            fmt::print("IMAGE_EVENT ActivateCommitted\n");
          },
          [](const event::RecoveryComplete &e) {
            fmt::print("IMAGE_EVENT RecoveryComplete\n");
            fmt::print("peer {}\n", e.peer);
            fmt::print("epoch {}\n", e.epoch);
          },
          [](const event::AllReplicasRecovered &e) {
            fmt::print("IMAGE_EVENT AllReplicasRecovered\n");
            fmt::print("epoch {}\n", e.epoch);
            print_osd_list("peers ", e.peers);
          },
          [](const event::ReplicaActivate &e) {
            fmt::print("IMAGE_EVENT ReplicaActivate\n");
            fmt::print("from {}\n", e.from);
            fmt::print("peer_image ");
            print_object_image(effective_image(e.auth_info));
            fmt::print("\n");
            fmt::print("peer_committed_seq {}\n", e.auth_info.committed_seq);
            fmt::print("authoritative_seq {}\n", e.authoritative_seq);
            fmt::print("last_epoch_started {}\n",
                       e.auth_info.last_epoch_started);
            print_prefixed_auth_source_lines("activation_auth_source",
                                             e.auth_sources);
            print_prefixed_blob_meta_lines("activation_blob_meta",
                                           e.auth_blob_meta);
            fmt::print("activation_epoch {}\n", e.activation_epoch);
          },
          [](const event::ReplicaRecoveryComplete &e) {
            fmt::print("IMAGE_EVENT ReplicaRecoveryComplete\n");
            fmt::print("recovered_image ");
            print_object_image(e.recovered_image.empty()
                                   ? primary_image(e.new_committed_length)
                                   : e.recovered_image);
            fmt::print("\n");
            fmt::print("new_committed_seq {}\n", e.new_committed_seq);
            fmt::print("activation_epoch {}\n", e.activation_epoch);
          },
          [](const event::DeleteStart &) {
            fmt::print("IMAGE_EVENT DeleteStart\n");
          },
          [](const event::DeleteComplete &) {
            fmt::print("IMAGE_EVENT DeleteComplete\n");
          },
      },
      ev);
  fmt::print("---\n");
}

static void print_peer_image_lines(const std::map<osd_id_t, PeerInfo> &infos) {
  for (const auto &[osd, info] : infos) {
    fmt::print("peer_image {} ", osd);
    print_object_image(effective_image(info));
    fmt::print(" {}\n", info.last_epoch_started);
    fmt::print("peer_committed_seq {} {}\n", osd, info.committed_seq);
  }
}

static void print_auth_source_lines(const AuthorityImage &auth_sources) {
  for (const auto &[obj, item] : auth_sources) {
    fmt::print("auth_source {} {} {}\n", obj, item.authority_osd,
               item.authority_length);
  }
}

static void print_blob_meta_lines(const BlobMetaImage &blob_meta) {
  print_prefixed_blob_meta_lines("auth_blob_meta", blob_meta);
}

static void
print_peer_recovery_plan_lines(const std::vector<PeerRecoveryPlan> &plans) {
  for (const auto &plan : plans) {
    fmt::print("peer_recovery_seq {} {} {}\n", plan.target,
               plan.peer_committed_seq, plan.authoritative_seq);
    for (const auto &item : plan.recoveries) {
      fmt::print("peer_recovery {} {} {} {}\n", plan.target, item.obj,
                 item.from_length, item.to_length);
      fmt::print("peer_recovery_source {} {} {}\n", plan.target, item.obj,
                 item.source);
    }
  }
}

static void
print_local_recovery_lines(const std::vector<ObjRecovery> &recoveries) {
  for (const auto &item : recoveries) {
    fmt::print("local_recovery {} {} {}\n", item.obj, item.from_length,
               item.to_length);
    fmt::print("local_recovery_source {} {}\n", item.obj, item.source);
  }
}

static void print_state(const PeeringStateMachine::Snapshot &snap) {
  fmt::print("IMAGE_CONTEXT\n");
  fmt::print("pgid {}\n", snap.pgid);
  fmt::print("whoami {}\n", snap.whoami);
  fmt::print("epoch {}\n", snap.epoch);
  fmt::print("acting ");
  print_osd_vector(snap.acting.osds);
  fmt::print("\n");
  fmt::print("acting_epoch {}\n", snap.acting.epoch);
  fmt::print("up ");
  print_osd_vector(snap.up.osds);
  fmt::print("\n");
  fmt::print("up_epoch {}\n", snap.up.epoch);
  fmt::print("pool_size {}\n", snap.pool_size);
  fmt::print("pool_min_size {}\n", snap.pool_min_size);
  fmt::print("local_committed_seq {}\n", snap.local_info.committed_seq);
  fmt::print("local_image ");
  print_object_image(snap.local_info.image);
  fmt::print("\n");
  fmt::print("local_last_epoch_started {}\n",
             snap.local_info.last_epoch_started);
  fmt::print("local_last_interval_started {}\n",
             snap.local_info.last_interval_started);
  fmt::print("local_last_epoch_clean {}\n", snap.local_info.last_epoch_clean);
  fmt::print("auth_seq {}\n", snap.auth_seq);
  fmt::print("auth_image ");
  print_object_image(snap.auth_image);
  fmt::print("\n");
  print_auth_source_lines(snap.auth_sources);
  print_blob_meta_lines(snap.auth_blob_meta);
  print_peer_image_lines(snap.peer_info);
  fmt::print("peers_queried ");
  print_osd_set(snap.peers_queried);
  fmt::print("\n");
  fmt::print("peers_responded ");
  print_osd_set(snap.peers_responded);
  fmt::print("\n");
  fmt::print("prior_osds ");
  print_osd_set(snap.prior_osds);
  fmt::print("\n");
  print_peer_recovery_plan_lines(snap.peer_recovery_plans);
  print_local_recovery_lines(snap.local_recovery_plan);
  if (snap.local_info.committed_seq < snap.auth_seq) {
    fmt::print("local_recovery_seq {} {}\n", snap.local_info.committed_seq,
               snap.auth_seq);
  }
  fmt::print("recovered ");
  print_osd_set(snap.recovered);
  fmt::print("\n");
  fmt::print("timed_out_probes ");
  print_osd_set(snap.timed_out_probes);
  fmt::print("\n");
  fmt::print("need_up_thru {}\n", snap.need_up_thru ? 1 : 0);
  fmt::print("activated {}\n", snap.activated ? 1 : 0);
  fmt::print("pending_acting_change {}\n", snap.pending_acting_change ? 1 : 0);
  fmt::print("last_peering_reset {}\n", snap.last_peering_reset);
  fmt::print("have_enough_info {}\n", snapshot_have_enough_info(snap) ? 1 : 0);
  fmt::print("image_invariant {}\n", snapshot_image_invariant(snap) ? 1 : 0);
  fmt::print("image_clean {}\n", snapshot_image_clean(snap) ? 1 : 0);
  fmt::print("image_recovering {}\n", snapshot_image_recovering(snap) ? 1 : 0);
  fmt::print("---\n");
}

// ── JSONL output ────────────────────────────────────────────────────

static void
emit_jsonl_step(int step_idx, const PeeringEvent &event,
                const PeeringStateMachine::SnapshotStepResult &result) {
  auto view = StepJson{
      .kind = "step",
      .step = step_idx,
      .from_state = state_name(result.from),
      .to_state = state_name(result.to),
      .event = {event_to_json(event)},
      .before = {to_json_str(to_snapshot_view(result.before))},
      .before_checks = {to_json_str(to_checks_view(result.before))},
      .after = {to_json_str(to_snapshot_view(result.after))},
      .after_checks = {to_json_str(to_checks_view(result.after))},
      .effects = {effects_to_json(result.effects)},
  };
  fmt::println("{}", to_json_str(view));
}

static void emit_jsonl_summary(uint64_t seed, int total_events) {
  fmt::println("{}", to_json_str(SummaryJson{
                         .kind = "summary",
                         .seed = seed,
                         .events = total_events,
                     }));
}

// ── Main ────────────────────────────────────────────────────────────

int main(int argc, char *argv[]) {
  uint64_t seed = 42;
  int num_events = 30;
  std::string format_str = "jsonl";
  std::string profile_str = "full";

  CLI::App app{"Cross-validation driver for peering state machine"};
  app.add_option("--seed", seed, "Random seed")->default_val(42);
  app.add_option("--events", num_events, "Max events per trace")
      ->default_val(30);
  app.add_option("--format", format_str, "Output format: jsonl|legacy")
      ->default_val("jsonl")
      ->check(CLI::IsMember({"jsonl", "legacy"}));
  app.add_option("--profile", profile_str, "Event profile: full|lean-core")
      ->default_val("full")
      ->check(CLI::IsMember({"full", "lean-core"}));

  CLI11_PARSE(app, argc, argv);

  OutputFormat format =
      (format_str == "legacy") ? OutputFormat::Legacy : OutputFormat::Jsonl;
  EventProfile profile = (profile_str == "lean-core") ? EventProfile::LeanCore
                                                      : EventProfile::Full;

  fmt::print(
      stderr,
      "Cross-validation driver: seed={} events={} format={} profile={}\n", seed,
      num_events, format == OutputFormat::Jsonl ? "jsonl" : "legacy",
      profile == EventProfile::LeanCore ? "lean-core" : "full");

  int total_events = 0;
  EventGenerator gen(seed, profile);
  PeeringStateMachine::Snapshot snap = PeeringStateMachine().snapshot();

  auto init_event = PeeringEvent(gen.gen_initialize());
  auto init_result = PeeringStateMachine::step(snap, init_event);
  if (format == OutputFormat::Legacy) {
    print_event(init_event);
    print_state(init_result.after);
  } else {
    emit_jsonl_step(0, init_event, init_result);
  }
  snap = init_result.after;
  total_events++;

  int actual_events = std::uniform_int_distribution<int>(
      std::min(50, num_events), num_events)(gen.rng);

  for (int ev_idx = 1; ev_idx <= actual_events; ev_idx++) {
    auto event = gen.gen_event(snap);
    auto result = PeeringStateMachine::step(snap, event);
    if (format == OutputFormat::Legacy) {
      print_event(event);
      print_state(result.after);
    } else {
      emit_jsonl_step(ev_idx, event, result);
    }
    snap = result.after;
    total_events++;
  }

  fmt::print(stderr, "Done. Total events: {}\n", total_events);
  if (format == OutputFormat::Jsonl) {
    emit_jsonl_summary(seed, total_events);
  }
  return 0;
}
