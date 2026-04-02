/*
 * Vermilion peering state machine.
 *
 * Pure event-driven state machine: process(event) -> effects.
 * No side effects, no IO, no threading, no message sending.
 * The runtime executes the effects.
 *
 * Derived from Ceph's PeeringState (~8300 lines) but radically
 * simplified for append-only + single-writer semantics.
 *
 * Key simplifications vs Ceph:
 * - No full PGLog: peering tracks a committed journal prefix plus an object
 *   image instead of the full log/missing/divergence machinery
 * - No merge_log/rewind_divergent_log: append-only means no divergence
 * - No separate GetLog/GetMissing phases: just collect committed_length
 * - No backfill vs recovery distinction: both are "push data to short replica"
 * - No reservation protocol: runtime handles scheduling
 * - No EC partial writes: out of scope
 * - No snap trim, scrub scheduling, cache tiering: out of scope
 */

#pragma once

#include <map>
#include <set>
#include <vector>

#include "peering_types.h"

namespace vermilion::peering {

class PeeringStateMachine {
public:
  PeeringStateMachine() = default;

  // ── Core interface ─────────────────────────────────────────────

  // Process an event and return the effects to execute.
  // Pure function from the caller's perspective: no internal IO.
  // Runtime contract:
  // - `process()` / `step()` are the safe entry points for raw events because
  //   they apply stale-message guards before dispatch.
  // - `process_validated()` assumes the caller already applied the same guard
  //   rules and should only be used at reducer boundaries that preserve that
  //   invariant.
  // - The returned effect list is ordered program output; async runtimes may
  //   overlap work, but they must preserve the reducer's causal contract and
  //   the per-effect durability requirements documented in `peering_types.h`.
  std::vector<PeeringEffect> process(const PeeringEvent &event);
  // Pure two-phase step API for roadmap alignment:
  // validate first, then reduce.
  StepResult step(const PeeringEvent &event);
  std::vector<PeeringEffect> process_validated(const ValidatedEvent &event);

  // Current state.
  State current_state() const { return state_; }

  // ── Introspection ──────────────────────────────────────────────

  pg_id_t pgid() const { return pgid_; }
  osd_id_t whoami() const { return whoami_; }
  epoch_t current_epoch() const { return epoch_; }
  bool is_primary() const { return acting_.primary() == whoami_; }
  bool is_active() const {
    return state_ == State::Active || state_ == State::Recovering ||
           state_ == State::Clean || state_ == State::ReplicaActive;
  }

  const ActingSet &acting() const { return acting_; }
  const ActingSet &up() const { return up_; }

  // Primary-object compatibility view of the objectwise authority.
  uint64_t authoritative_length() const { return primary_length(auth_image_); }
  journal_seq_t authoritative_seq() const { return auth_seq_; }

  // Peer info collected during peering.
  const std::map<osd_id_t, PeerInfo> &peer_info() const { return peer_info_; }

  // ── Snapshot / restore (for simulation & persistence) ──────────

  struct Snapshot {
    State state;
    pg_id_t pgid;
    osd_id_t whoami;
    epoch_t epoch;
    ActingSet acting;
    ActingSet up;
    int pool_size;
    int pool_min_size;
    PGInfo local_info;
    journal_seq_t auth_seq;
    uint64_t auth_length;
    osd_id_t auth_osd;
    ObjectImage auth_image;
    AuthorityImage auth_sources;
    std::map<osd_id_t, PeerInfo> peer_info;
    std::set<osd_id_t> peers_queried;
    std::set<osd_id_t> peers_responded;
    std::set<osd_id_t> prior_osds;
    std::set<osd_id_t> recovery_targets;
    std::vector<PeerRecoveryPlan> peer_recovery_plans;
    std::vector<ObjRecovery> local_recovery_plan;
    std::set<osd_id_t> recovered;
    std::set<osd_id_t> timed_out_probes;
    bool need_up_thru;
    bool activated;
    bool pending_acting_change;
    epoch_t last_peering_reset;
  };

  struct SnapshotStepResult {
    Snapshot before;
    Snapshot after;
    State from;
    State to;
    std::vector<PeeringEffect> effects;
  };

  Snapshot snapshot() const;
  static PeeringStateMachine from_snapshot(const Snapshot &snap);

  // Snapshot-first pure step API for roadmap alignment.
  // Returns before/after snapshots and the transition boundary.
  static SnapshotStepResult step(const Snapshot &snapshot,
                                 const PeeringEvent &event);
  static SnapshotStepResult
  step_with_validated(const Snapshot &snapshot,
                      const ValidatedEvent &validated_event);

private:
  // ── State ──────────────────────────────────────────────────────

  State state_ = State::Initial;
  pg_id_t pgid_ = 0;
  osd_id_t whoami_ = -1;
  epoch_t epoch_ = 0;

  // Pool replication parameters.
  int pool_size_ = 0;     // desired replicas
  int pool_min_size_ = 0; // minimum to serve IO

  // Acting/up sets from OSDMap.
  ActingSet acting_;
  ActingSet up_;

  // Local PG state.
  PGInfo local_info_;

  // OSDs from prior intervals that might have data (Ceph: PriorSet::probe).
  std::set<osd_id_t> prior_osds_;

  // Peering state: info collected from peers.
  std::map<osd_id_t, PeerInfo> peer_info_;
  std::set<osd_id_t> peers_queried_;
  std::set<osd_id_t> peers_responded_;
  std::set<osd_id_t> timed_out_probes_; // probes that timed out — may have data

  // Objectwise authority and recovery state.
  journal_seq_t auth_seq_ = 0;
  ObjectImage auth_image_;
  AuthorityImage auth_sources_;
  std::vector<PeerRecoveryPlan> peer_recovery_plans_;
  std::vector<ObjRecovery> local_recovery_plan_;
  std::set<osd_id_t> recovered_;

  // Flags.
  bool need_up_thru_ = false;
  bool activated_ = false;
  bool pending_acting_change_ =
      false; // acting change requested, block activation

  // Last peering reset epoch (to detect stale messages).
  epoch_t last_peering_reset_ = 0;

  // ── Event handlers ─────────────────────────────────────────────

  using Effects = std::vector<PeeringEffect>;

  Effects on_initialize(const event::Initialize &e);
  Effects on_advance_map(const event::AdvanceMap &e);
  Effects on_peer_info_received(const event::PeerInfoReceived &e);
  Effects on_peer_query_timeout(const event::PeerQueryTimeout &e);
  Effects on_up_thru_updated(const event::UpThruUpdated &e);
  Effects on_activate_committed(const event::ActivateCommitted &e);
  Effects on_recovery_complete(const event::RecoveryComplete &e);
  Effects on_all_replicas_recovered(const event::AllReplicasRecovered &e);
  Effects on_replica_activate(const event::ReplicaActivate &e);
  Effects on_replica_recovery_complete(const event::ReplicaRecoveryComplete &e);
  Effects on_delete_start(const event::DeleteStart &e);
  Effects on_delete_complete(const event::DeleteComplete &e);

  // ── Internal helpers ───────────────────────────────────────────

  // Transition to a new state, emitting LogTransition effect.
  void transition_to(State new_state, const char *reason, Effects &fx);

  // Common primary peering startup logic.
  void start_peering_primary(const std::vector<osd_id_t> &prior_osds,
                             Effects &fx);

  // Determine which peers to query. Includes acting + up + prior_osds.
  // Equivalent to Ceph's build_prior() + PriorSet::probe.
  std::set<osd_id_t> build_probe_set() const;

  // Send queries to all peers we haven't heard from yet.
  void send_queries(Effects &fx);

  // Check if we have enough peer info to proceed.
  bool have_enough_info() const;

  // Recompute live image authority and recovery planning state.
  void refresh_authority_from_known_peers();
  void refresh_recovery_plans_from_current_authority();
  void refresh_image_state_from_known_peers();
  std::set<osd_id_t> image_recovery_targets() const;
  bool is_image_recovery_target(osd_id_t peer) const;

  enum class InitializeDecisionKind {
    None,
    StartPrimary,
    BecomeReplicaStray,
    BecomeStray,
  };

  struct InitializeDecision {
    InitializeDecisionKind kind = InitializeDecisionKind::None;
    pg_id_t pgid = 0;
    osd_id_t whoami = -1;
    epoch_t epoch = 0;
    ActingSet acting;
    ActingSet up;
    int pool_size = 0;
    int pool_min_size = 0;
    PGInfo local_info;
    std::vector<osd_id_t> prior_osds;
    const char *reason = nullptr;
  };

  // `Initialize` is always processed. It resets all interval-local peering
  // state, installs the supplied map/local metadata, and then chooses one of:
  // - `StartPrimary`: transition into primary peering startup
  // - `BecomeReplicaStray`: transition to `Stray` as an acting replica
  // - `BecomeStray`: transition to `Stray` outside acting
  // Effects: always `UpdateHeartbeats`; primary initialization may also emit
  // `SendQuery` and later primary-side transitions.
  InitializeDecision decide_initialize(const event::Initialize &e) const;
  void apply_initialize_decision(Effects &fx,
                                 const InitializeDecision &decision);

  enum class PeerInfoReceivedDecisionKind {
    None,
    StoreOnly,
    StoreAndChooseActing,
  };

  struct PeerInfoReceivedDecision {
    PeerInfoReceivedDecisionKind kind = PeerInfoReceivedDecisionKind::None;
    osd_id_t from = -1;
    PeerInfo info;
  };

  // `PeerInfoReceived` is processed only when:
  // - the sender is in `peers_queried_`, `acting_`, `up_`, or `prior_osds_`,
  // - and `query_epoch` is zero or not older than `last_peering_reset_`.
  // Otherwise it is ignored.
  //
  // In `GetPeerInfo`, accepted replies either just update peer state
  // (`StoreOnly`) or also trigger `choose_acting()` once enough info is
  // present. In `Down`/`Incomplete`/`WaitUpThru`, accepted replies are stored
  // and immediately re-run `choose_acting()` so peering can recover.
  PeerInfoReceivedDecision
  decide_peer_info_received(const event::PeerInfoReceived &e) const;
  void
  apply_peer_info_received_decision(Effects &fx,
                                    const PeerInfoReceivedDecision &decision);

  enum class AdvanceMapDecisionKind {
    None,
    PublishOnly,
    PoolParamsOnly,
    RetryChooseActing,
    RetryChooseActingAfterPoolChange,
    DownForMinSize,
    RestartPrimary,
    RestartReplica,
    RestartStray,
  };

  struct AdvanceMapDecision {
    AdvanceMapDecisionKind kind = AdvanceMapDecisionKind::None;
    epoch_t epoch = 0;
    ActingSet acting;
    ActingSet up;
    int pool_size = 0;
    int pool_min_size = 0;
    std::vector<osd_id_t> prior_osds;
    bool cancel_recovery = false;
    bool deactivate_pg = false;
    bool retry_choose_acting = false;
    const char *reason = nullptr;
  };

  // `AdvanceMap` is always processed. Depending on interval and pool-parameter
  // changes it may:
  // - publish only,
  // - update pool params only,
  // - retry `choose_acting()`,
  // - transition to `Down` for a tighter `min_size`,
  // - or restart peering as primary / replica stray / stray.
  // Restart paths may emit `CancelRecovery`, `DeactivatePG`,
  // `UpdateHeartbeats`, and then the usual peering-start effects.
  AdvanceMapDecision decide_advance_map(const event::AdvanceMap &e) const;
  void apply_advance_map_decision(Effects &fx,
                                  const AdvanceMapDecision &decision);

  enum class PeerQueryTimeoutDecisionKind {
    None,
    RecordTimeout,
    RecordTimeoutAndChooseActing,
  };

  struct PeerQueryTimeoutDecision {
    PeerQueryTimeoutDecisionKind kind = PeerQueryTimeoutDecisionKind::None;
    osd_id_t peer = -1;
  };

  // `PeerQueryTimeout` matters only in `GetPeerInfo`; otherwise it is ignored.
  // Callers should emit it only for outstanding `SendQuery` targets. Accepted
  // timeouts mark the peer as responded+timed_out so peering can either keep
  // waiting or continue conservatively via `choose_acting()`.
  PeerQueryTimeoutDecision
  decide_peer_query_timeout(const event::PeerQueryTimeout &e) const;
  void
  apply_peer_query_timeout_decision(Effects &fx,
                                    const PeerQueryTimeoutDecision &decision);

  struct DeleteStartDecision {
    bool deactivate_pg = false;
    bool cancel_recovery = false;
  };

  // `DeleteStart` is always processed. It transitions to `Deleting` and emits
  // `DeactivatePG` / `CancelRecovery` first when needed, then `DeletePG`.
  DeleteStartDecision decide_delete_start() const;
  void apply_delete_start_decision(Effects &fx,
                                   const DeleteStartDecision &decision);
  // `DeleteComplete` is currently a reducer no-op. After `DeletePG`
  // succeeds, callers should stop routing normal peering events for the old
  // instance and only re-enter through a fresh `Initialize`.

  struct UpThruDecision {
    bool proceed = false;
  };

  // `UpThruUpdated` is processed only in `WaitUpThru` and only for the exact
  // current epoch. Otherwise it is ignored. Success clears `need_up_thru_`,
  // may advance local interval history, and then calls `try_activate()`.
  UpThruDecision decide_up_thru_updated(const event::UpThruUpdated &e) const;
  void apply_up_thru_decision(Effects &fx, const UpThruDecision &decision);

  struct ActivateCommittedDecision {
    bool persist_activation = false;
  };

  // `ActivateCommitted` is meaningful only while the PG is active-ish
  // (`Active` / `Recovering` / `Clean` / `ReplicaActive`). Otherwise it is
  // ignored. Success flips `activated_` and emits `PersistState`.
  ActivateCommittedDecision decide_activate_committed() const;
  void
  apply_activate_committed_decision(Effects &fx,
                                    const ActivateCommittedDecision &decision);

  enum class ActingDecisionKind {
    None,
    Incomplete,
    Down,
    NeedActingChange,
    NeedUpThru,
    Activate,
  };

  struct ActingDecision {
    ActingDecisionKind kind = ActingDecisionKind::None;
    journal_seq_t auth_seq = 0;
    ObjectImage auth_image;
    AuthorityImage auth_sources;
    const char *reason = nullptr;
    std::vector<osd_id_t> want_acting;
    std::vector<PeerRecoveryPlan> peer_recovery_plans;
    std::vector<ObjRecovery> local_recovery_plan;
  };

  // Extract a pure acting-set decision before mutating state.
  // Requires the current peer census already stored in the reducer.
  // It recomputes authority/recovery plans and then chooses one of:
  // - `Incomplete` / `Down`
  // - `NeedActingChange`
  // - `NeedUpThru`
  // - `Activate`
  // Transition/effect consequences are applied by `apply_acting_decision()`.
  ActingDecision decide_acting() const;
  // Apply a precomputed acting-set decision.
  // Effects:
  // - `PublishStats` on `Incomplete` / `Down`
  // - `RequestActingChange` while waiting for a future `AdvanceMap`
  // - `RequestUpThru` + transition to `WaitUpThru`
  // - `try_activate()` on `Activate`
  void apply_acting_decision(Effects &fx, const ActingDecision &decision);

  enum class ActivationDecisionKind {
    None,
    Down,
    Recovering,
    Clean,
  };

  struct ActivationDecision {
    ActivationDecisionKind kind = ActivationDecisionKind::None;
    const char *reason = nullptr;
    bool clamp_local_to_auth = false;
    std::vector<osd_id_t> activate_replicas;
    std::vector<effect::ScheduleRecovery::Target> recovery_targets;
  };

  // Extract a pure activation/recovery decision before mutating state.
  // Preconditions: invoked only after authority/recovery plans were already
  // chosen. It may refuse activation (`None`), send the PG `Down`, or classify
  // the post-activation state as `Recovering` vs `Clean`.
  ActivationDecision decide_activation() const;
  // Apply a precomputed activation/recovery decision.
  // Transitions:
  // - `Down`
  // - `Active`
  // - optionally immediately to `Recovering` or `Clean`
  // Effects are the ordered activation contract documented on `try_activate()`.
  void apply_activation_decision(Effects &fx,
                                 const ActivationDecision &decision);

  enum class RecoveryProgressDecisionKind {
    None,
    Progress,
    Clean,
  };

  struct RecoveryProgressDecision {
    RecoveryProgressDecisionKind kind = RecoveryProgressDecisionKind::None;
    std::set<osd_id_t> completed_peers;
    bool update_local_to_auth = false;
    const char *clean_reason = nullptr;
  };

  // `RecoveryComplete` is processed only in `Recovering`, only for fresh
  // epochs, and only for actual image-recovery targets. Otherwise it is
  // ignored. Accepted completions update recovered bookkeeping and may finish
  // the PG as `Clean`.
  RecoveryProgressDecision
  decide_recovery_complete(const event::RecoveryComplete &e) const;
  // `AllReplicasRecovered` is processed only in `Recovering` or `Active`, only
  // for fresh epochs, and only when every listed peer is still a current
  // recovery target and the batch exactly covers the remaining targets.
  RecoveryProgressDecision
  decide_all_replicas_recovered(const event::AllReplicasRecovered &e) const;
  void
  apply_recovery_progress_decision(Effects &fx,
                                   const RecoveryProgressDecision &decision);

  enum class ReplicaActivationDecisionKind {
    None,
    Activate,
  };

  struct ReplicaActivationDecision {
    ReplicaActivationDecisionKind kind = ReplicaActivationDecisionKind::None;
    journal_seq_t auth_seq = 0;
    ObjectImage auth_image;
    AuthorityImage auth_sources;
    epoch_t activation_epoch = 0;
    bool advance_history = false;
  };

  // `ReplicaActivate` is processed only when:
  // - local state is `Stray` or `ReplicaActive`,
  // - self is in the acting set,
  // - sender is the acting primary,
  // - `activation_epoch` matches the current epoch
  //   (stale/future raw events are already filtered by `validate_event()`).
  // Otherwise it is ignored.
  //
  // Proof-side support assumption: `auth_info` / `auth_sources` /
  // `authoritative_seq` come from one fresh primary-side authority
  // computation, not a stale cached activation message.
  ReplicaActivationDecision
  decide_replica_activation(const event::ReplicaActivate &e) const;
  void
  apply_replica_activation_decision(Effects &fx,
                                    const ReplicaActivationDecision &decision);

  enum class ReplicaRecoveryDecisionKind {
    None,
    Complete,
  };

  struct ReplicaRecoveryDecision {
    ReplicaRecoveryDecisionKind kind = ReplicaRecoveryDecisionKind::None;
    journal_seq_t committed_seq = 0;
    ObjectImage recovered_image;
    epoch_t activation_epoch = 0;
  };

  // `ReplicaRecoveryComplete` is processed only in `ReplicaActive` and only if
  // it preserves monotonic local progress/history and stays within the current
  // installed authority. Otherwise it is ignored.
  //
  // Proof-side support assumption: the installed replica authority came from a
  // consistent `SendActivate` generated from the primary's latest authority
  // computation.
  ReplicaRecoveryDecision decide_replica_recovery_complete(
      const event::ReplicaRecoveryComplete &e) const;
  void apply_replica_recovery_decision(Effects &fx,
                                       const ReplicaRecoveryDecision &decision);

  // Choose objectwise authority and determine acting/recovery plans.
  // Internal orchestration step reached after peer census changes.
  void choose_acting(Effects &fx);

  // Try to activate the PG (transition to Active).
  // Successful activation emits the effect contract that async runtimes must
  // implement faithfully:
  // - `SendActivate` for each acting replica with the exact chosen authority
  //   snapshot,
  // - `ActivatePG`,
  // - `PersistState`,
  // - `PublishStats`,
  // - and optionally `ScheduleRecovery` if any target is still short.
  void try_activate(Effects &fx);

  // Emit PersistState effect for current state.
  // Callers must treat this as a durability barrier before feeding later
  // peering events back into the reducer.
  void persist(Effects &fx);

  // Emit PublishStats effect.
  // Reporting-only effect; must not feed state back into the reducer.
  void publish_stats(Effects &fx);

  // Clear peering-specific state for a new interval.
  // Keeps local durable PG metadata but drops interval-local peering,
  // authority, and recovery bookkeeping.
  void reset_peering_state();
};

} // namespace vermilion::peering
