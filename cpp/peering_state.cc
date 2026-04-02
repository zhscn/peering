/*
 * Vermilion peering state machine implementation.
 *
 * This implements the simplified append-only peering protocol, following
 * Ceph's approach for correctness-critical decisions:
 *
 *   - Authoritative state is now tracked as an objectwise image plus per-object
 *     source map, rather than one scalar committed_length.
 *
 *   - Probe set includes prior-interval OSDs (Ceph: PastIntervals::PriorSet),
 *     not just current acting + up. The longest replica can live outside
 *     the current acting set after a remap.
 *
 *   - Late PeerInfoReceived is accepted in Down/Incomplete states
 *     (Ceph: GetInfo::react(MNotifyRec) and Peering::react(MNotifyRec)),
 *     so peering can recover from stalls.
 *
 *   - Short primary is included in recovery targets. If a better primary
 *     exists, RequestActingChange is emitted (Ceph: pg_temp).
 *
 * The flow for a primary is:
 *
 *   Initial --(Initialize)--> GetPeerInfo
 *     Query all peers (acting + up + prior_osds) for image summaries.
 *
 *   GetPeerInfo --(all PeerInfoReceived)--> [WaitUpThru | Active]
 *     Select authoritative objectwise image from known peer images.
 *     If current acting set is suboptimal, emit RequestActingChange.
 *
 *   WaitUpThru --(UpThruUpdated)--> Active
 *
 *   Active --(recovery needed?)--> Recovering
 *     Schedule recovery for all short replicas, including self.
 *
 *   Recovering --(AllReplicasRecovered)--> Clean
 *
 * For replicas:
 *   Initial --(Initialize)--> Stray --(ReplicaActivate)--> ReplicaActive
 */

#include "peering_state.h"

#include <algorithm>
#include <cassert>
#include <type_traits>

namespace vermilion::peering {

// ── State name lookup ──────────────────────────────────────────────

const char *state_name(State s) {
  switch (s) {
  case State::Initial:
    return "Initial";
  case State::Reset:
    return "Reset";
  case State::GetPeerInfo:
    return "GetPeerInfo";
  case State::WaitUpThru:
    return "WaitUpThru";
  case State::Active:
    return "Active";
  case State::Recovering:
    return "Recovering";
  case State::Clean:
    return "Clean";
  case State::Stray:
    return "Stray";
  case State::ReplicaActive:
    return "ReplicaActive";
  case State::Down:
    return "Down";
  case State::Incomplete:
    return "Incomplete";
  case State::Deleting:
    return "Deleting";
  }
  return "Unknown";
}

namespace {

bool is_fresh_epoch(epoch_t reset, epoch_t msg_epoch) {
  return msg_epoch == 0 || msg_epoch >= reset;
}

PeerInfo normalize_peer_info_copy(PeerInfo info) {
  return normalized_peer_info(std::move(info));
}

PGInfo normalize_pg_info_copy(PGInfo info) {
  return normalized_pg_info(std::move(info));
}

std::map<osd_id_t, PeerInfo>
normalize_peer_info_map(const std::map<osd_id_t, PeerInfo> &infos) {
  std::map<osd_id_t, PeerInfo> normalized;
  for (const auto &[osd, info] : infos) {
    auto copy = normalize_peer_info_copy(info);
    copy.osd = osd;
    normalized.emplace(osd, std::move(copy));
  }
  return normalized;
}

std::vector<PeerInfo>
known_peer_images(osd_id_t whoami, const PGInfo &local_info,
                  const std::map<osd_id_t, PeerInfo> &peer_info) {
  std::vector<PeerInfo> peers;
  peers.reserve(peer_info.size() + 1);
  for (const auto &[osd, info] : peer_info) {
    if (osd == whoami) {
      continue;
    }
    auto copy = normalize_peer_info_copy(info);
    copy.osd = osd;
    peers.push_back(std::move(copy));
  }
  auto local = normalize_pg_info_copy(local_info);
  peers.push_back(PeerInfo{
      .osd = whoami,
      .committed_seq = local.committed_seq,
      .committed_length = local.committed_length,
      .image = local.image,
      .last_epoch_started = local.last_epoch_started,
      .last_interval_started = local.last_interval_started,
  });
  return peers;
}

std::vector<PeerInfo>
acting_replica_images(const ActingSet &acting, osd_id_t whoami,
                      const std::map<osd_id_t, PeerInfo> &peer_info) {
  std::vector<PeerInfo> peers;
  for (auto osd : acting.osds) {
    if (osd < 0 || osd == whoami) {
      continue;
    }
    auto it = peer_info.find(osd);
    if (it != peer_info.end()) {
      auto copy = normalize_peer_info_copy(it->second);
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

osd_id_t authority_osd_for(const AuthorityImage &auth, object_id_t obj) {
  auto it = auth.find(obj);
  return it == auth.end() ? -1 : it->second.authority_osd;
}

journal_seq_t authoritative_committed_seq(const std::vector<PeerInfo> &infos) {
  journal_seq_t seq = 0;
  for (const auto &raw : infos) {
    auto info = normalized_peer_info(raw);
    if (info.committed_seq > seq) {
      seq = info.committed_seq;
    }
  }
  return seq;
}

std::set<osd_id_t>
recovery_targets_from_plans(const std::vector<PeerRecoveryPlan> &peer_plans,
                            const std::vector<ObjRecovery> &local_plan,
                            journal_seq_t local_committed_seq,
                            journal_seq_t authoritative_seq, osd_id_t whoami) {
  std::set<osd_id_t> targets;
  for (const auto &plan : peer_plans) {
    targets.insert(plan.target);
  }
  if (!local_plan.empty() || local_committed_seq < authoritative_seq) {
    targets.insert(whoami);
  }
  return targets;
}

} // namespace

std::optional<ValidatedEvent> validate_event(epoch_t reset,
                                             const PeeringEvent &event) {
  return std::visit(
      [=](const auto &e) -> std::optional<ValidatedEvent> {
        using T = std::decay_t<decltype(e)>;

        if constexpr (std::is_same_v<T, event::PeerInfoReceived>) {
          return is_fresh_epoch(reset, e.query_epoch)
                     ? std::optional<ValidatedEvent>(e)
                     : std::nullopt;
        } else if constexpr (std::is_same_v<T, event::RecoveryComplete>) {
          return is_fresh_epoch(reset, e.epoch)
                     ? std::optional<ValidatedEvent>(e)
                     : std::nullopt;
        } else if constexpr (std::is_same_v<T, event::AllReplicasRecovered>) {
          return is_fresh_epoch(reset, e.epoch)
                     ? std::optional<ValidatedEvent>(e)
                     : std::nullopt;
        } else if constexpr (std::is_same_v<T, event::ReplicaActivate>) {
          return is_fresh_epoch(reset, e.activation_epoch)
                     ? std::optional<ValidatedEvent>(e)
                     : std::nullopt;
        } else if constexpr (std::is_same_v<T,
                                            event::ReplicaRecoveryComplete>) {
          return is_fresh_epoch(reset, e.activation_epoch)
                     ? std::optional<ValidatedEvent>(e)
                     : std::nullopt;
        } else {
          return e;
        }
      },
      event);
}

// ── Event dispatch ─────────────────────────────────────────────────

std::vector<PeeringEffect>
PeeringStateMachine::process(const PeeringEvent &event) {
  return step(event).effects;
}

PeeringStateMachine::SnapshotStepResult
PeeringStateMachine::step(const Snapshot &snapshot, const PeeringEvent &event) {
  auto validated = validate_event(snapshot.last_peering_reset, event);
  if (!validated.has_value()) {
    return {snapshot, snapshot, snapshot.state, snapshot.state, {}};
  }
  return step_with_validated(snapshot, *validated);
}

PeeringStateMachine::SnapshotStepResult
PeeringStateMachine::step_with_validated(
    const Snapshot &snapshot, const ValidatedEvent &validated_event) {
  auto sim = from_snapshot(snapshot);
  State before = sim.state_;
  auto effects = sim.process_validated(validated_event);
  State after = sim.state_;
  return {snapshot, sim.snapshot(), before, after, std::move(effects)};
}

StepResult PeeringStateMachine::step(const PeeringEvent &event) {
  auto result = step(snapshot(), event);
  return {result.from, result.to, std::move(result.effects)};
}

std::vector<PeeringEffect>
PeeringStateMachine::process_validated(const ValidatedEvent &event) {
  return std::visit(
      [this](const auto &e) -> Effects {
        using T = std::decay_t<decltype(e)>;

        if constexpr (std::is_same_v<T, event::Initialize>)
          return on_initialize(e);
        else if constexpr (std::is_same_v<T, event::AdvanceMap>)
          return on_advance_map(e);
        else if constexpr (std::is_same_v<T, event::PeerInfoReceived>)
          return on_peer_info_received(e);
        else if constexpr (std::is_same_v<T, event::PeerQueryTimeout>)
          return on_peer_query_timeout(e);
        else if constexpr (std::is_same_v<T, event::UpThruUpdated>)
          return on_up_thru_updated(e);
        else if constexpr (std::is_same_v<T, event::ActivateCommitted>)
          return on_activate_committed(e);
        else if constexpr (std::is_same_v<T, event::RecoveryComplete>)
          return on_recovery_complete(e);
        else if constexpr (std::is_same_v<T, event::AllReplicasRecovered>)
          return on_all_replicas_recovered(e);
        else if constexpr (std::is_same_v<T, event::ReplicaActivate>)
          return on_replica_activate(e);
        else if constexpr (std::is_same_v<T, event::ReplicaRecoveryComplete>)
          return on_replica_recovery_complete(e);
        else if constexpr (std::is_same_v<T, event::DeleteStart>)
          return on_delete_start(e);
        else if constexpr (std::is_same_v<T, event::DeleteComplete>)
          return on_delete_complete(e);
        else
          return {};
      },
      event);
}

// ── Helper: start peering as primary ───────────────────────────────

void PeeringStateMachine::start_peering_primary(
    const std::vector<osd_id_t> &prior_osds, Effects &fx) {
  transition_to(State::GetPeerInfo, "start peering as primary", fx);

  // Record prior-interval OSDs for probing.
  prior_osds_.clear();
  for (auto osd : prior_osds) {
    if (osd >= 0 && osd != whoami_)
      prior_osds_.insert(osd);
  }

  // Include ourselves in peer info.
  PeerInfo self_info;
  self_info.osd = whoami_;
  self_info.committed_seq = local_info_.committed_seq;
  self_info.committed_length = local_info_.committed_length;
  self_info.image = effective_image(local_info_);
  self_info.last_epoch_started = local_info_.last_epoch_started;
  self_info.last_interval_started = local_info_.last_interval_started;
  peer_info_[whoami_] = self_info;
  peers_responded_.insert(whoami_);
  refresh_image_state_from_known_peers();

  send_queries(fx);

  // If no peers to query (single-OSD), proceed immediately.
  if (have_enough_info()) {
    choose_acting(fx);
  }
}

// ── Initialize ─────────────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_initialize(const event::Initialize &e) {
  Effects fx;
  auto decision = decide_initialize(e);
  apply_initialize_decision(fx, decision);
  return fx;
}

// ── AdvanceMap ─────────────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_advance_map(const event::AdvanceMap &e) {
  Effects fx;
  auto decision = decide_advance_map(e);
  apply_advance_map_decision(fx, decision);
  return fx;
}

// ── PeerInfoReceived ───────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_peer_info_received(const event::PeerInfoReceived &e) {
  Effects fx;
  auto decision = decide_peer_info_received(e);
  apply_peer_info_received_decision(fx, decision);
  return fx;
}

// ── PeerQueryTimeout ───────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_peer_query_timeout(const event::PeerQueryTimeout &e) {
  Effects fx;
  auto decision = decide_peer_query_timeout(e);
  apply_peer_query_timeout_decision(fx, decision);
  return fx;
}

// ── UpThruUpdated ──────────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_up_thru_updated(const event::UpThruUpdated &e) {
  Effects fx;
  auto decision = decide_up_thru_updated(e);
  apply_up_thru_decision(fx, decision);
  return fx;
}

// ── ActivateCommitted ──────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_activate_committed(const event::ActivateCommitted &) {
  Effects fx;
  auto decision = decide_activate_committed();
  apply_activate_committed_decision(fx, decision);
  return fx;
}

// ── RecoveryComplete ───────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_recovery_complete(const event::RecoveryComplete &e) {
  Effects fx;
  auto decision = decide_recovery_complete(e);
  apply_recovery_progress_decision(fx, decision);
  return fx;
}

// ── AllReplicasRecovered ───────────────────────────────────────────

PeeringStateMachine::Effects PeeringStateMachine::on_all_replicas_recovered(
    const event::AllReplicasRecovered &e) {
  Effects fx;
  auto decision = decide_all_replicas_recovered(e);
  apply_recovery_progress_decision(fx, decision);
  return fx;
}

// ── ReplicaActivate ────────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_replica_activate(const event::ReplicaActivate &e) {
  Effects fx;
  auto decision = decide_replica_activation(e);
  apply_replica_activation_decision(fx, decision);
  return fx;
}

// ── ReplicaRecoveryComplete ────────────────────────────────────────

PeeringStateMachine::Effects PeeringStateMachine::on_replica_recovery_complete(
    const event::ReplicaRecoveryComplete &e) {
  Effects fx;
  auto decision = decide_replica_recovery_complete(e);
  apply_replica_recovery_decision(fx, decision);
  return fx;
}

// ── Delete events ──────────────────────────────────────────────────

PeeringStateMachine::Effects
PeeringStateMachine::on_delete_start(const event::DeleteStart &) {
  Effects fx;
  auto decision = decide_delete_start();
  apply_delete_start_decision(fx, decision);
  return fx;
}

PeeringStateMachine::Effects
PeeringStateMachine::on_delete_complete(const event::DeleteComplete &) {
  return {};
}

// ── Internal helpers ───────────────────────────────────────────────

void PeeringStateMachine::transition_to(State new_state, const char *reason,
                                        Effects &fx) {
  if (state_ == new_state)
    return;

  fx.push_back(effect::LogTransition{
      .pgid = pgid_,
      .from = state_,
      .to = new_state,
      .reason = reason,
  });
  state_ = new_state;
}

std::set<osd_id_t> PeeringStateMachine::build_probe_set() const {
  // Probe acting + up + prior-interval OSDs.
  // This matches Ceph's PriorSet::probe construction:
  // the longest replica can live outside the current acting/up set
  // if a remap happened.
  std::set<osd_id_t> probes;
  for (auto osd : acting_.osds) {
    if (osd != whoami_ && osd >= 0)
      probes.insert(osd);
  }
  for (auto osd : up_.osds) {
    if (osd != whoami_ && osd >= 0)
      probes.insert(osd);
  }
  for (auto osd : prior_osds_) {
    if (osd != whoami_ && osd >= 0)
      probes.insert(osd);
  }
  return probes;
}

void PeeringStateMachine::send_queries(Effects &fx) {
  auto probes = build_probe_set();
  for (osd_id_t osd : probes) {
    if (!peers_responded_.contains(osd) && !peers_queried_.contains(osd)) {
      fx.push_back(effect::SendQuery{
          .target = osd,
          .pgid = pgid_,
          .epoch = epoch_,
      });
      peers_queried_.insert(osd);
    }
  }
}

bool PeeringStateMachine::have_enough_info() const {
  // We need responses from all queried peers.
  // This includes prior-interval OSDs, matching Ceph's GetInfo
  // which waits for all probed peers (PriorSet::probe).
  for (auto osd : peers_queried_) {
    if (!peers_responded_.contains(osd)) {
      return false;
    }
  }
  // Also need all queried acting replicas other than self.
  for (auto osd : acting_.osds) {
    if (osd >= 0 && osd != whoami_ && !peers_responded_.contains(osd)) {
      return false;
    }
  }
  return true;
}

void PeeringStateMachine::refresh_authority_from_known_peers() {
  auto local = normalize_pg_info_copy(local_info_);
  auto peers = normalize_peer_info_map(peer_info_);
  auto known_peers = known_peer_images(whoami_, local, peers);
  auth_seq_ = authoritative_committed_seq(known_peers);
  auth_sources_ = authoritative_sources(known_peers);
  auth_image_ = authority_image_values(auth_sources_);
}

void PeeringStateMachine::refresh_recovery_plans_from_current_authority() {
  auto local = normalize_pg_info_copy(local_info_);
  auto peers = normalize_peer_info_map(peer_info_);
  peer_recovery_plans_ = build_peer_recovery_plans(
      auth_sources_, auth_seq_, acting_replica_images(acting_, whoami_, peers));
  local_recovery_plan_ = pg_image_recovery_plan(auth_sources_, local);
}

void PeeringStateMachine::refresh_image_state_from_known_peers() {
  refresh_authority_from_known_peers();
  refresh_recovery_plans_from_current_authority();
}

std::set<osd_id_t> PeeringStateMachine::image_recovery_targets() const {
  return recovery_targets_from_plans(peer_recovery_plans_, local_recovery_plan_,
                                     local_info_.committed_seq, auth_seq_,
                                     whoami_);
}

bool PeeringStateMachine::is_image_recovery_target(osd_id_t peer) const {
  return image_recovery_targets().contains(peer);
}

PeeringStateMachine::InitializeDecision
PeeringStateMachine::decide_initialize(const event::Initialize &e) const {
  InitializeDecision decision;
  decision.pgid = e.pgid;
  decision.whoami = e.whoami;
  decision.epoch = e.epoch;
  decision.acting = e.acting;
  decision.up = e.up;
  decision.pool_size = e.pool_size;
  decision.pool_min_size = e.pool_min_size;
  decision.local_info = e.local_info;
  decision.prior_osds = e.prior_osds;

  if (e.acting.primary() == e.whoami) {
    decision.kind = InitializeDecisionKind::StartPrimary;
  } else if (e.acting.contains(e.whoami)) {
    decision.kind = InitializeDecisionKind::BecomeReplicaStray;
    decision.reason = "initialize as replica";
  } else {
    decision.kind = InitializeDecisionKind::BecomeStray;
    decision.reason = "initialize as stray";
  }
  return decision;
}

void PeeringStateMachine::apply_initialize_decision(
    Effects &fx, const InitializeDecision &decision) {
  if (decision.kind == InitializeDecisionKind::None) {
    return;
  }

  pgid_ = decision.pgid;
  whoami_ = decision.whoami;
  epoch_ = decision.epoch;
  acting_ = decision.acting;
  up_ = decision.up;
  pool_size_ = decision.pool_size;
  pool_min_size_ = decision.pool_min_size;
  local_info_ = normalize_pg_info_copy(decision.local_info);
  reset_peering_state();
  last_peering_reset_ = decision.epoch;
  refresh_image_state_from_known_peers();

  if (decision.kind == InitializeDecisionKind::StartPrimary) {
    start_peering_primary(decision.prior_osds, fx);
  } else {
    transition_to(State::Stray, decision.reason, fx);
  }

  fx.push_back(effect::UpdateHeartbeats{
      .peers =
          std::vector<osd_id_t>(acting_.osds.begin(), acting_.osds.end())});
}

PeeringStateMachine::PeerInfoReceivedDecision
PeeringStateMachine::decide_peer_info_received(
    const event::PeerInfoReceived &e) const {
  PeerInfoReceivedDecision decision;

  // Fix (round 12): Reject replies from OSDs we never probed or that
  // aren't in acting/up/prior sets.
  if (!peers_queried_.contains(e.from) && !acting_.contains(e.from) &&
      !up_.contains(e.from) && !prior_osds_.contains(e.from)) {
    return decision;
  }

  // Discard stale replies from previous peering intervals.
  if (e.query_epoch > 0 && e.query_epoch < last_peering_reset_) {
    return decision;
  }

  decision.from = e.from;
  decision.info = e.info;
  decision.info.osd = e.from; // trust transport sender, not payload

  if (state_ == State::Down || state_ == State::Incomplete ||
      state_ == State::WaitUpThru) {
    decision.kind = PeerInfoReceivedDecisionKind::StoreAndChooseActing;
    return decision;
  }

  if (state_ != State::GetPeerInfo) {
    decision.kind = PeerInfoReceivedDecisionKind::None;
    return decision;
  }

  bool enough_info = true;
  for (auto osd : peers_queried_) {
    if (osd != e.from && !peers_responded_.contains(osd)) {
      enough_info = false;
      break;
    }
  }
  if (enough_info) {
    for (auto osd : acting_.osds) {
      if (osd >= 0 && osd != whoami_ && osd != e.from &&
          !peers_responded_.contains(osd)) {
        enough_info = false;
        break;
      }
    }
  }

  decision.kind = enough_info
                      ? PeerInfoReceivedDecisionKind::StoreAndChooseActing
                      : PeerInfoReceivedDecisionKind::StoreOnly;
  return decision;
}

void PeeringStateMachine::apply_peer_info_received_decision(
    Effects &fx, const PeerInfoReceivedDecision &decision) {
  if (decision.kind == PeerInfoReceivedDecisionKind::None) {
    return;
  }

  peer_info_[decision.from] = normalize_peer_info_copy(decision.info);
  peers_responded_.insert(decision.from);
  refresh_image_state_from_known_peers();

  if (decision.kind == PeerInfoReceivedDecisionKind::StoreAndChooseActing) {
    choose_acting(fx);
  }
}

PeeringStateMachine::AdvanceMapDecision
PeeringStateMachine::decide_advance_map(const event::AdvanceMap &e) const {
  AdvanceMapDecision decision;
  decision.epoch = e.new_epoch;
  decision.acting = e.new_acting;
  decision.up = e.new_up;
  decision.pool_size = e.new_pool_size;
  decision.pool_min_size = e.new_pool_min_size;
  decision.prior_osds = e.prior_osds;

  // Check if this is a new interval (acting or up set changed).
  bool new_interval =
      (e.new_acting.osds != acting_.osds || e.new_up.osds != up_.osds);

  // Fix (round 5+6+10): Pool parameter changes must be detected BEFORE
  // overwriting the old values. Save old min_size for comparison.
  bool pool_params_changed =
      (e.new_pool_size != pool_size_ || e.new_pool_min_size != pool_min_size_);
  int old_pool_min_size = pool_min_size_;

  bool next_is_primary = (e.new_acting.primary() == whoami_);
  bool next_contains_self = e.new_acting.contains(whoami_);

  if (!new_interval && !pool_params_changed) {
    // Fix (round 8): If we have a pending acting change and got a
    // same-interval epoch bump, re-run choose_acting to retry.
    if (pending_acting_change_ && next_is_primary &&
        (state_ == State::GetPeerInfo || state_ == State::WaitUpThru)) {
      decision.kind = AdvanceMapDecisionKind::RetryChooseActing;
    } else {
      decision.kind = AdvanceMapDecisionKind::PublishOnly;
    }
    return decision;
  }

  // Pool param change without interval change: re-evaluate peering.
  // Fix (round 9): Only run this on the primary. Replicas don't have
  // peer_info_ census and would incorrectly go Down.
  if (!new_interval && pool_params_changed) {
    if (next_is_primary && is_active()) {
      int available = 0;
      for (auto osd : e.new_acting.osds) {
        if (osd >= 0 && peer_info_.contains(osd))
          available++;
      }
      if (available < e.new_pool_min_size) {
        decision.kind = AdvanceMapDecisionKind::DownForMinSize;
        decision.cancel_recovery = (state_ == State::Recovering);
        decision.deactivate_pg = true;
        decision.retry_choose_acting =
            (old_pool_min_size > e.new_pool_min_size);
        decision.reason = "min_size increased, insufficient peers";
        return decision;
      }
    }
    // Fix (round 8+10): If Down/Incomplete and min_size decreased, re-evaluate.
    if (next_is_primary &&
        (state_ == State::Down || state_ == State::Incomplete) &&
        old_pool_min_size > e.new_pool_min_size) {
      decision.kind = AdvanceMapDecisionKind::RetryChooseActingAfterPoolChange;
      return decision;
    }
    decision.kind = AdvanceMapDecisionKind::PoolParamsOnly;
    return decision;
  }

  // New interval: restart peering.
  decision.cancel_recovery = (state_ == State::Recovering);
  decision.deactivate_pg = is_active();
  if (next_is_primary) {
    decision.kind = AdvanceMapDecisionKind::RestartPrimary;
  } else if (next_contains_self) {
    decision.kind = AdvanceMapDecisionKind::RestartReplica;
  } else {
    decision.kind = AdvanceMapDecisionKind::RestartStray;
  }
  return decision;
}

void PeeringStateMachine::apply_advance_map_decision(
    Effects &fx, const AdvanceMapDecision &decision) {
  if (decision.kind == AdvanceMapDecisionKind::None) {
    return;
  }

  epoch_ = decision.epoch;
  acting_ = decision.acting;
  up_ = decision.up;

  switch (decision.kind) {
  case AdvanceMapDecisionKind::PublishOnly:
    publish_stats(fx);
    return;
  case AdvanceMapDecisionKind::PoolParamsOnly:
    pool_size_ = decision.pool_size;
    pool_min_size_ = decision.pool_min_size;
    return;
  case AdvanceMapDecisionKind::RetryChooseActing:
    choose_acting(fx);
    return;
  case AdvanceMapDecisionKind::RetryChooseActingAfterPoolChange:
    pool_size_ = decision.pool_size;
    pool_min_size_ = decision.pool_min_size;
    choose_acting(fx);
    return;
  case AdvanceMapDecisionKind::DownForMinSize:
    pool_size_ = decision.pool_size;
    pool_min_size_ = decision.pool_min_size;
    if (decision.cancel_recovery) {
      fx.push_back(effect::CancelRecovery{.pgid = pgid_});
    }
    if (decision.deactivate_pg) {
      fx.push_back(effect::DeactivatePG{.pgid = pgid_});
    }
    transition_to(State::Down, decision.reason, fx);
    publish_stats(fx);
    if (decision.retry_choose_acting) {
      choose_acting(fx);
    }
    return;
  case AdvanceMapDecisionKind::RestartPrimary:
  case AdvanceMapDecisionKind::RestartReplica:
  case AdvanceMapDecisionKind::RestartStray:
    pool_size_ = decision.pool_size;
    pool_min_size_ = decision.pool_min_size;
    if (decision.cancel_recovery) {
      fx.push_back(effect::CancelRecovery{.pgid = pgid_});
    }
    if (decision.deactivate_pg) {
      fx.push_back(effect::DeactivatePG{.pgid = pgid_});
    }
    reset_peering_state();
    last_peering_reset_ = epoch_;

    if (decision.kind == AdvanceMapDecisionKind::RestartPrimary) {
      start_peering_primary(decision.prior_osds, fx);
    } else if (decision.kind == AdvanceMapDecisionKind::RestartReplica) {
      refresh_image_state_from_known_peers();
      transition_to(State::Stray, "new interval, replica", fx);
    } else {
      refresh_image_state_from_known_peers();
      transition_to(State::Stray, "new interval, stray", fx);
    }

    fx.push_back(effect::UpdateHeartbeats{
        .peers =
            std::vector<osd_id_t>(acting_.osds.begin(), acting_.osds.end())});
    return;
  case AdvanceMapDecisionKind::None:
    return;
  }
}

PeeringStateMachine::PeerQueryTimeoutDecision
PeeringStateMachine::decide_peer_query_timeout(
    const event::PeerQueryTimeout &e) const {
  PeerQueryTimeoutDecision decision;

  if (state_ != State::GetPeerInfo) {
    return decision;
  }

  decision.peer = e.peer;
  decision.kind = PeerQueryTimeoutDecisionKind::RecordTimeout;

  bool enough_info = true;
  for (auto osd : peers_queried_) {
    if (osd != e.peer && !peers_responded_.contains(osd)) {
      enough_info = false;
      break;
    }
  }
  if (enough_info) {
    for (auto osd : acting_.osds) {
      if (osd >= 0 && osd != whoami_ && osd != e.peer &&
          !peers_responded_.contains(osd)) {
        enough_info = false;
        break;
      }
    }
  }

  if (enough_info) {
    decision.kind = PeerQueryTimeoutDecisionKind::RecordTimeoutAndChooseActing;
  }
  return decision;
}

void PeeringStateMachine::apply_peer_query_timeout_decision(
    Effects &fx, const PeerQueryTimeoutDecision &decision) {
  if (decision.kind == PeerQueryTimeoutDecisionKind::None) {
    return;
  }

  // Fix (round 5): If a prior-interval OSD times out, it might have
  // the longest committed copy. Track it as timed out so choose_acting
  // can be conservative.
  peers_responded_.insert(decision.peer);
  timed_out_probes_.insert(decision.peer);

  if (decision.kind ==
      PeerQueryTimeoutDecisionKind::RecordTimeoutAndChooseActing) {
    choose_acting(fx);
  }
}

PeeringStateMachine::DeleteStartDecision
PeeringStateMachine::decide_delete_start() const {
  DeleteStartDecision decision;
  decision.deactivate_pg = is_active();
  decision.cancel_recovery = (state_ == State::Recovering);
  return decision;
}

void PeeringStateMachine::apply_delete_start_decision(
    Effects &fx, const DeleteStartDecision &decision) {
  if (decision.deactivate_pg) {
    fx.push_back(effect::DeactivatePG{.pgid = pgid_});
  }
  if (decision.cancel_recovery) {
    fx.push_back(effect::CancelRecovery{.pgid = pgid_});
  }

  transition_to(State::Deleting, "delete requested", fx);
  fx.push_back(effect::DeletePG{.pgid = pgid_});
}

PeeringStateMachine::UpThruDecision PeeringStateMachine::decide_up_thru_updated(
    const event::UpThruUpdated &e) const {
  UpThruDecision decision;

  if (state_ != State::WaitUpThru)
    return decision;
  // Fix (round 7): Only accept up_thru for our exact epoch.
  // Reject both stale (past) and premature (future) notifications.
  if (e.epoch != epoch_)
    return decision;

  decision.proceed = true;
  return decision;
}

void PeeringStateMachine::apply_up_thru_decision(
    Effects &fx, const UpThruDecision &decision) {
  if (!decision.proceed) {
    return;
  }

  need_up_thru_ = false;
  if (local_info_.last_interval_started < epoch_) {
    local_info_.last_interval_started = epoch_;
  }
  try_activate(fx);
}

PeeringStateMachine::ActivateCommittedDecision
PeeringStateMachine::decide_activate_committed() const {
  ActivateCommittedDecision decision;
  decision.persist_activation = is_active();
  return decision;
}

void PeeringStateMachine::apply_activate_committed_decision(
    Effects &fx, const ActivateCommittedDecision &decision) {
  if (!decision.persist_activation) {
    return;
  }

  activated_ = true;
  persist(fx);
}

PeeringStateMachine::ActingDecision PeeringStateMachine::decide_acting() const {
  ActingDecision decision;
  auto local = normalize_pg_info_copy(local_info_);
  auto peers = normalize_peer_info_map(peer_info_);
  auto known_peers = known_peer_images(whoami_, local, peers);
  if (known_peers.empty()) {
    decision.kind = ActingDecisionKind::Incomplete;
    decision.reason = "no valid peer info";
    return decision;
  }

  decision.kind = ActingDecisionKind::Activate;
  decision.auth_seq = authoritative_committed_seq(known_peers);
  decision.auth_sources = authoritative_sources(known_peers);
  decision.auth_image = authority_image_values(decision.auth_sources);
  decision.peer_recovery_plans = build_peer_recovery_plans(
      decision.auth_sources, decision.auth_seq,
      acting_replica_images(acting_, whoami_, peers));
  decision.local_recovery_plan =
      pg_image_recovery_plan(decision.auth_sources, local);

  // Fix (round 5): If any prior-interval OSD timed out and had the
  // same interval, it might still carry unseen objectwise authority.
  for (osd_id_t osd : timed_out_probes_) {
    if (prior_osds_.contains(osd) && !peer_info_.contains(osd)) {
      decision.kind = ActingDecisionKind::Down;
      decision.reason = "prior-interval probe timed out";
      return decision;
    }
  }

  // 2. Build the desired acting set from all responding peers.
  // Fix (round 1): Consider all peers (including prior-interval OSDs),
  // not just current acting members. This prevents false unavailability
  // when the recoverable quorum requires a prior-interval OSD.
  std::vector<osd_id_t> want_acting;
  std::set<osd_id_t> in_want;

  // Keep the acting primary CRUSH-chosen. Journal/image authority determines
  // recovery sources, not who coordinates the PG.
  osd_id_t desired_primary = acting_.primary();
  if (desired_primary < 0) {
    desired_primary = whoami_;
  }

  // Seed with desired primary.
  want_acting.push_back(desired_primary);
  in_want.insert(desired_primary);

  // Prefer peers already fully caught up to the objectwise authority.
  auto add_peer = [&](osd_id_t osd) {
    if (osd < 0 || in_want.contains(osd))
      return;
    if (static_cast<int>(want_acting.size()) >= pool_size_)
      return;
    if (!peers.contains(osd))
      return;
    want_acting.push_back(osd);
    in_want.insert(osd);
  };

  auto is_complete_peer = [&](osd_id_t osd) {
    auto it = peers.find(osd);
    return it != peers.end() &&
           it->second.committed_seq >= decision.auth_seq &&
           same_image(effective_image(it->second), decision.auth_image);
  };

  // Pass 1: Add fully recovered peers from acting, up, prior.
  for (auto osd : acting_.osds) {
    if (is_complete_peer(osd))
      add_peer(osd);
  }
  for (auto osd : up_.osds) {
    if (is_complete_peer(osd))
      add_peer(osd);
  }
  for (auto osd : prior_osds_) {
    if (is_complete_peer(osd))
      add_peer(osd);
  }

  // Pass 2: Fill remaining slots with short peers.
  for (auto osd : acting_.osds)
    add_peer(osd);
  for (auto osd : up_.osds)
    add_peer(osd);
  for (auto osd : prior_osds_)
    add_peer(osd);

  int available = static_cast<int>(want_acting.size());
  if (available < pool_min_size_) {
    decision.kind = available == 0 ? ActingDecisionKind::Incomplete
                                   : ActingDecisionKind::Down;
    decision.reason = (available == 0 ? "no peers available"
                                      : "insufficient peers for min_size");
    return decision;
  }

  // 3. Request acting change only if:
  //    (a) primary needs to change (desired_primary != current primary), or
  //    (b) an OSD outside acting set needs to be included.
  bool need_acting_change = false;
  for (auto osd : want_acting) {
    if (!acting_.contains(osd)) {
      need_acting_change = true;
      break;
    }
  }
  if (need_acting_change) {
    decision.kind = ActingDecisionKind::NeedActingChange;
    decision.want_acting = std::move(want_acting);
    return decision;
  }
  decision.want_acting = std::move(want_acting);

  // 5. Check if we need up_thru.
  if (local_info_.last_interval_started < epoch_) {
    decision.kind = ActingDecisionKind::NeedUpThru;
    return decision;
  }

  return decision;
}

void PeeringStateMachine::apply_acting_decision(
    Effects &fx, const ActingDecision &decision) {
  if (decision.kind == ActingDecisionKind::None) {
    return;
  }

  auth_seq_ = decision.auth_seq;
  auth_image_ = decision.auth_image;
  auth_sources_ = decision.auth_sources;
  peer_recovery_plans_ = decision.peer_recovery_plans;
  local_recovery_plan_ = decision.local_recovery_plan;

  switch (decision.kind) {
  case ActingDecisionKind::Incomplete:
    transition_to(State::Incomplete, decision.reason, fx);
    publish_stats(fx);
    return;
  case ActingDecisionKind::Down:
    transition_to(State::Down, decision.reason, fx);
    publish_stats(fx);
    return;
  case ActingDecisionKind::NeedActingChange:
    fx.push_back(effect::RequestActingChange{
        .pgid = pgid_,
        .want_acting = decision.want_acting,
    });
    pending_acting_change_ = true;
    return;
  case ActingDecisionKind::NeedUpThru:
    pending_acting_change_ = false;
    need_up_thru_ = true;
    transition_to(State::WaitUpThru, "need up_thru", fx);
    fx.push_back(effect::RequestUpThru{.epoch = epoch_});
    return;
  case ActingDecisionKind::Activate:
    pending_acting_change_ = false;
    try_activate(fx);
    return;
  case ActingDecisionKind::None:
    break;
  }
}

void PeeringStateMachine::choose_acting(Effects &fx) {
  auto decision = decide_acting();
  apply_acting_decision(fx, decision);
}

PeeringStateMachine::ActivationDecision
PeeringStateMachine::decide_activation() const {
  ActivationDecision decision;

  // Fix (round 3): Don't activate if an acting change was requested.
  if (pending_acting_change_)
    return decision;

  // Fix (round 11): Recheck min_size before activating. Pool params may
  // have changed since choose_acting() originally ran.
  int available = 0;
  for (auto osd : acting_.osds) {
    if (osd >= 0 && peer_info_.contains(osd))
      available++;
  }
  if (available < pool_min_size_) {
    decision.kind = ActivationDecisionKind::Down;
    decision.reason = "min_size check failed at activation";
    return decision;
  }

  decision.clamp_local_to_auth =
      local_info_.committed_seq >= auth_seq_ &&
      prefix_image(auth_image_, effective_image(local_info_));
  for (auto osd : acting_.osds) {
    if (osd >= 0 && osd != whoami_) {
      decision.activate_replicas.push_back(osd);
    }
  }

  for (const auto &plan : peer_recovery_plans_) {
    auto it = peer_info_.find(plan.target);
    uint64_t peer_len = (it != peer_info_.end())
                            ? primary_length(effective_image(it->second))
                            : 0;
    journal_seq_t peer_seq =
        (it != peer_info_.end()) ? it->second.committed_seq : 0;
    decision.recovery_targets.push_back({
        .osd = plan.target,
        .peer_length = peer_len,
        .authoritative_length = primary_length(auth_image_),
        .peer_committed_seq = peer_seq,
        .authoritative_seq = auth_seq_,
        .recoveries = plan.recoveries,
    });
  }
  if (!local_recovery_plan_.empty() || local_info_.committed_seq < auth_seq_) {
    decision.recovery_targets.push_back({
        .osd = whoami_,
        .peer_length = primary_length(effective_image(local_info_)),
        .authoritative_length = primary_length(auth_image_),
        .peer_committed_seq = local_info_.committed_seq,
        .authoritative_seq = auth_seq_,
        .recoveries = local_recovery_plan_,
    });
  }

  decision.kind = decision.recovery_targets.empty()
                      ? ActivationDecisionKind::Clean
                      : ActivationDecisionKind::Recovering;
  decision.reason = "peering complete";
  return decision;
}

void PeeringStateMachine::apply_activation_decision(
    Effects &fx, const ActivationDecision &decision) {
  if (decision.kind == ActivationDecisionKind::None) {
    return;
  }

  if (decision.kind == ActivationDecisionKind::Down) {
    transition_to(State::Down, decision.reason, fx);
    publish_stats(fx);
    return;
  }

  // Update local info.
  local_info_.last_epoch_started = epoch_;
  local_info_.last_interval_started = epoch_;
  if (decision.clamp_local_to_auth) {
    local_info_.image = auth_image_;
    local_info_.committed_seq = auth_seq_;
    local_info_.committed_length = primary_length(auth_image_);
  }
  refresh_recovery_plans_from_current_authority();

  // Transition to Active.
  transition_to(State::Active, "peering complete", fx);

  // Activate replicas.
  for (auto osd : decision.activate_replicas) {
    PeerInfo auth_info;
    auth_info.osd = whoami_;
    auth_info.committed_seq = auth_seq_;
    auth_info.committed_length = primary_length(auth_image_);
    auth_info.image = auth_image_;
    auth_info.last_epoch_started = epoch_;
    auth_info.last_interval_started = epoch_;

    fx.push_back(effect::SendActivate{
        .target = osd,
        .pgid = pgid_,
        .auth_info = auth_info,
        .auth_sources = auth_sources_,
        .authoritative_seq = auth_seq_,
        .activation_epoch = epoch_,
    });
  }

  // Emit ActivatePG so the runtime starts serving IO.
  fx.push_back(effect::ActivatePG{
      .pgid = pgid_,
      .authoritative_seq = auth_seq_,
      .authoritative_length = primary_length(auth_image_),
      .authoritative_image = auth_image_,
      .activation_epoch = epoch_,
  });

  // Persist and publish.
  persist(fx);
  publish_stats(fx);

  // If recovery is needed, schedule it.
  if (decision.kind == ActivationDecisionKind::Recovering) {
    transition_to(State::Recovering, "replicas need recovery", fx);
    fx.push_back(effect::ScheduleRecovery{
        .pgid = pgid_,
        .targets = decision.recovery_targets,
    });
    return;
  }

  if (decision.kind == ActivationDecisionKind::Clean) {
    // Already clean.
    transition_to(State::Clean, "all replicas up to date", fx);
    fx.push_back(effect::MarkClean{.pgid = pgid_});
  }
}

void PeeringStateMachine::try_activate(Effects &fx) {
  auto decision = decide_activation();
  apply_activation_decision(fx, decision);
}

PeeringStateMachine::RecoveryProgressDecision
PeeringStateMachine::decide_recovery_complete(
    const event::RecoveryComplete &e) const {
  RecoveryProgressDecision decision;

  if (state_ != State::Recovering)
    return decision;

  // Fix (round 4): Reject stale recovery completions from prior intervals.
  if (e.epoch < last_peering_reset_)
    return decision;

  // Fix (round 7): Only accept completions for actual recovery targets.
  if (!is_image_recovery_target(e.peer))
    return decision;

  decision.kind = RecoveryProgressDecisionKind::Progress;
  decision.completed_peers.insert(e.peer);
  decision.update_local_to_auth = (e.peer == whoami_);
  decision.clean_reason = "all replicas recovered";

  return decision;
}

PeeringStateMachine::RecoveryProgressDecision
PeeringStateMachine::decide_all_replicas_recovered(
    const event::AllReplicasRecovered &e) const {
  RecoveryProgressDecision decision;

  if (state_ != State::Recovering && state_ != State::Active)
    return decision;

  // Fix (round 7): Reject stale batch completions from prior intervals.
  if (e.epoch < last_peering_reset_)
    return decision;

  for (osd_id_t peer : e.peers) {
    if (!is_image_recovery_target(peer)) {
      return decision;
    }
    decision.completed_peers.insert(peer);
  }

  std::set<osd_id_t> completed = recovered_;
  completed.insert(decision.completed_peers.begin(),
                   decision.completed_peers.end());
  if (completed != image_recovery_targets()) {
    decision.completed_peers.clear();
    return decision;
  }

  decision.kind = RecoveryProgressDecisionKind::Progress;
  decision.update_local_to_auth = true;
  decision.clean_reason = "all replicas recovered (batch)";
  return decision;
}

void PeeringStateMachine::apply_recovery_progress_decision(
    Effects &fx, const RecoveryProgressDecision &decision) {
  if (decision.kind == RecoveryProgressDecisionKind::None) {
    return;
  }

  for (osd_id_t peer : decision.completed_peers) {
    recovered_.insert(peer);

    auto &info = peer_info_[peer];
    info.osd = peer;
    info.committed_seq = auth_seq_;
    info.committed_length = primary_length(auth_image_);
    info.image = auth_image_;
  }

  if (decision.update_local_to_auth) {
    local_info_.image = auth_image_;
    local_info_.committed_seq = auth_seq_;
    local_info_.committed_length = primary_length(auth_image_);
  }
  // Recovery progress can change source tie-breaking for the remaining gaps,
  // so recompute the full authority view before rebuilding plans.
  refresh_image_state_from_known_peers();

  if (decision.clean_reason != nullptr && image_recovery_targets().empty()) {
    // Once recovery is complete, this bookkeeping is no longer live.
    recovered_.clear();
    transition_to(State::Clean, decision.clean_reason, fx);
    fx.push_back(effect::MarkClean{.pgid = pgid_});
    persist(fx);
    publish_stats(fx);
  }
}

PeeringStateMachine::ReplicaActivationDecision
PeeringStateMachine::decide_replica_activation(
    const event::ReplicaActivate &e) const {
  ReplicaActivationDecision decision;

  if (state_ != State::Stray && state_ != State::ReplicaActive)
    return decision;

  // Fix (round 12): Only accept if we're actually in the acting set.
  if (!acting_.contains(whoami_))
    return decision;

  // Fix (round 1+2+10): Validate sender is the primary and epoch matches.
  if (e.activation_epoch != epoch_)
    return decision;
  if (e.from != acting_.primary())
    return decision;

  auto auth_info = normalize_peer_info_copy(e.auth_info);
  decision.kind = ReplicaActivationDecisionKind::Activate;
  decision.auth_seq =
      e.authoritative_seq > 0 ? e.authoritative_seq : auth_info.committed_seq;
  decision.auth_sources = !e.auth_sources.empty() ? e.auth_sources
                                                  : authority_from_peer_info(auth_info);
  decision.auth_image = !decision.auth_sources.empty()
                            ? authority_image_values(decision.auth_sources)
                            : auth_info.image;
  decision.activation_epoch = e.activation_epoch;
  decision.advance_history = decision.auth_seq <= local_info_.committed_seq &&
      prefix_image(decision.auth_image, effective_image(local_info_));
  return decision;
}

void PeeringStateMachine::apply_replica_activation_decision(
    Effects &fx, const ReplicaActivationDecision &decision) {
  if (decision.kind == ReplicaActivationDecisionKind::None) {
    return;
  }

  auth_seq_ = decision.auth_seq;
  auth_image_ = decision.auth_image;
  auth_sources_ = decision.auth_sources;

  // Fix (round 1+8): Advance LES only for a fully caught-up replica and
  // clamp any overlong local tail to the chosen authority.
  local_info_.image = clamp_image_to(auth_image_, effective_image(local_info_));
  if (local_info_.committed_seq > auth_seq_) {
    local_info_.committed_seq = auth_seq_;
  }
  local_info_.committed_length = primary_length(local_info_.image);
  if (decision.advance_history) {
    local_info_.committed_seq = auth_seq_;
    local_info_.last_epoch_started = decision.activation_epoch;
    local_info_.last_interval_started = decision.activation_epoch;
  }
  refresh_recovery_plans_from_current_authority();

  transition_to(State::ReplicaActive, "activated by primary", fx);
  persist(fx);
  publish_stats(fx);
}

PeeringStateMachine::ReplicaRecoveryDecision
PeeringStateMachine::decide_replica_recovery_complete(
    const event::ReplicaRecoveryComplete &e) const {
  ReplicaRecoveryDecision decision;

  if (state_ != State::ReplicaActive)
    return decision;

  // Fix (round 7): Monotonicity guards — reject stale completions that
  // would roll back committed journal progress or epoch history.
  if (e.activation_epoch < last_peering_reset_)
    return decision;
  auto recovered_image = e.recovered_image;
  if (recovered_image.empty() && e.new_committed_length > 0) {
    recovered_image = primary_image(e.new_committed_length);
  }
  auto merged = join_image(effective_image(local_info_), recovered_image);
  auto clamped = clamp_image_to(auth_image_, merged);
  if (!prefix_image(effective_image(local_info_), clamped))
    return decision;
  if (e.activation_epoch < local_info_.last_epoch_started)
    return decision;
  journal_seq_t recovered_seq = e.new_committed_seq;
  if (recovered_seq == 0 && !recovered_image.empty() &&
      same_image(recovered_image, auth_image_)) {
    recovered_seq = auth_seq_;
  }
  if (recovered_seq < local_info_.committed_seq)
    return decision;
  if (recovered_seq > auth_seq_)
    return decision;

  decision.kind = ReplicaRecoveryDecisionKind::Complete;
  decision.committed_seq = recovered_seq;
  decision.recovered_image = clamped;
  decision.activation_epoch = e.activation_epoch;
  return decision;
}

void PeeringStateMachine::apply_replica_recovery_decision(
    Effects &fx, const ReplicaRecoveryDecision &decision) {
  if (decision.kind == ReplicaRecoveryDecisionKind::None) {
    return;
  }

  local_info_.image = decision.recovered_image;
  local_info_.committed_seq = decision.committed_seq;
  local_info_.committed_length = primary_length(decision.recovered_image);
  local_info_.last_epoch_started = decision.activation_epoch;
  local_info_.last_interval_started = decision.activation_epoch;
  refresh_recovery_plans_from_current_authority();

  persist(fx);
  publish_stats(fx);
}

void PeeringStateMachine::persist(Effects &fx) {
  fx.push_back(effect::PersistState{
      .pgid = pgid_,
      .info = normalize_pg_info_copy(local_info_),
  });
}

void PeeringStateMachine::publish_stats(Effects &fx) {
  fx.push_back(effect::PublishStats{
      .pgid = pgid_,
      .state = state_,
      .committed_seq = local_info_.committed_seq,
      .authoritative_seq = auth_seq_,
      .committed_length = primary_length(effective_image(local_info_)),
      .image = effective_image(local_info_),
      .authoritative_image = auth_image_,
      .acting_size = acting_.size(),
      .up_size = up_.size(),
  });
}

void PeeringStateMachine::reset_peering_state() {
  peer_info_.clear();
  peers_queried_.clear();
  peers_responded_.clear();
  timed_out_probes_.clear();
  prior_osds_.clear();
  auth_seq_ = 0;
  auth_image_.clear();
  auth_sources_.clear();
  peer_recovery_plans_.clear();
  local_recovery_plan_.clear();
  recovered_.clear();
  need_up_thru_ = false;
  activated_ = false;
  pending_acting_change_ = false;
}

// ── Snapshot / restore ─────────────────────────────────────────────

PeeringStateMachine::Snapshot PeeringStateMachine::snapshot() const {
  auto local_info = normalize_pg_info_copy(local_info_);
  auto peer_info = normalize_peer_info_map(peer_info_);
  auto auth_image = auth_image_;
  auto auth_sources = auth_sources_;
  auto peer_recovery_plans = peer_recovery_plans_;
  auto local_recovery_plan = local_recovery_plan_;
  std::set<osd_id_t> recovery_targets = recovery_targets_from_plans(
      peer_recovery_plans, local_recovery_plan, local_info.committed_seq,
      auth_seq_, whoami_);
  std::set<osd_id_t> recovered = recovered_;
  if (state_ == State::Clean) {
    recovery_targets.clear();
    recovered.clear();
    peer_recovery_plans.clear();
    local_recovery_plan.clear();
  }

  return {
      .state = state_,
      .pgid = pgid_,
      .whoami = whoami_,
      .epoch = epoch_,
      .acting = acting_,
      .up = up_,
      .pool_size = pool_size_,
      .pool_min_size = pool_min_size_,
      .local_info = local_info,
      .auth_seq = auth_seq_,
      .auth_length = primary_length(auth_image),
      .auth_osd = authority_osd_for(auth_sources, primary_object_id),
      .auth_image = auth_image,
      .auth_sources = auth_sources,
      .peer_info = peer_info,
      .peers_queried = peers_queried_,
      .peers_responded = peers_responded_,
      .prior_osds = prior_osds_,
      .recovery_targets = recovery_targets,
      .peer_recovery_plans = peer_recovery_plans,
      .local_recovery_plan = local_recovery_plan,
      .recovered = recovered,
      .timed_out_probes = timed_out_probes_,
      .need_up_thru = need_up_thru_,
      .activated = activated_,
      .pending_acting_change = pending_acting_change_,
      .last_peering_reset = last_peering_reset_,
  };
}

PeeringStateMachine PeeringStateMachine::from_snapshot(const Snapshot &s) {
  PeeringStateMachine sm;
  sm.state_ = s.state;
  sm.pgid_ = s.pgid;
  sm.whoami_ = s.whoami;
  sm.epoch_ = s.epoch;
  sm.acting_ = s.acting;
  sm.up_ = s.up;
  sm.pool_size_ = s.pool_size;
  sm.pool_min_size_ = s.pool_min_size;
  sm.local_info_ = normalize_pg_info_copy(s.local_info);
  sm.auth_seq_ = s.auth_seq;
  sm.auth_image_ =
      !s.auth_image.empty()
          ? s.auth_image
          : (!s.auth_sources.empty()
                 ? authority_image_values(s.auth_sources)
                 : (s.auth_length > 0 ? primary_image(s.auth_length)
                                      : ObjectImage{}));
  sm.auth_sources_ = !s.auth_sources.empty()
                         ? s.auth_sources
                         : authority_from_image(s.auth_osd, sm.auth_image_);
  sm.peer_info_ = normalize_peer_info_map(s.peer_info);
  if (sm.auth_seq_ == 0) {
    sm.auth_seq_ = authoritative_committed_seq(
        known_peer_images(sm.whoami_, sm.local_info_, sm.peer_info_));
  }
  sm.peers_queried_ = s.peers_queried;
  sm.peers_responded_ = s.peers_responded;
  sm.prior_osds_ = s.prior_osds;
  sm.peer_recovery_plans_ = s.peer_recovery_plans;
  sm.local_recovery_plan_ = s.local_recovery_plan;
  if (sm.peer_recovery_plans_.empty() && sm.local_recovery_plan_.empty() &&
      (sm.auth_seq_ > 0 || !sm.auth_image_.empty()) &&
      s.state != State::Clean) {
    sm.refresh_recovery_plans_from_current_authority();
  }
  sm.recovered_ = s.recovered;
  if (sm.state_ == State::Clean) {
    sm.peer_recovery_plans_.clear();
    sm.local_recovery_plan_.clear();
    sm.recovered_.clear();
  }
  sm.timed_out_probes_ = s.timed_out_probes;
  sm.need_up_thru_ = s.need_up_thru;
  sm.activated_ = s.activated;
  sm.pending_acting_change_ = s.pending_acting_change;
  sm.last_peering_reset_ = s.last_peering_reset;
  return sm;
}

} // namespace vermilion::peering
