/*
 * Vermilion peering state machine types.
 *
 * Events, effects, and state enum for the simplified peering protocol.
 * Designed as a pure state machine: process(event) -> effects.
 *
 * Derived from Ceph's PeeringState but radically simplified for
 * append-only + single-writer semantics (see design.md §21).
 */

#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <variant>
#include <vector>

#include "peer_info.h"

namespace vermilion::peering {

// ── State enum ─────────────────────────────────────────────────────
//
// Ceph has ~35 hierarchical boost::statechart states. Under append-only
// constraints, the state machine collapses to a linear flow:
//
//   Initial → GetPeerInfo → [WaitUpThru] → Active → Recovering → Clean
//                                        → Stray (if replica)
//
// Eliminated states and why:
//   GetLog         → replaced by GetPeerInfo (just collect committed_length)
//   GetMissing     → eliminated (no missing set; length comparison suffices)
//   Backfilling    → merged into Recovering (same operation: push data)
//   WaitLocal/RemoteRecoveryReserved → eliminated (runtime handles scheduling)
//   WaitLocal/RemoteBackfillReserved → eliminated (no separate backfill path)
//   NotRecovering/NotBackfilling     → subsumed by Active
//   Activating     → merged into Active (activation is synchronous from SM's
//   view)

enum class State : uint8_t {
  // Bootstrap states
  Initial, // Just created, no epoch info yet
  Reset,   // Resetting for a new peering interval

  // Peering states (primary only)
  GetPeerInfo, // Querying peers for committed_length (Ceph: GetInfo + GetLog +
               // GetMissing)
  WaitUpThru,  // Waiting for OSDMap to reflect our up_thru

  // Operational states
  Active,     // PG is active, serving IO (may need recovery)
  Recovering, // Pushing data to short replicas
  Clean,      // All replicas fully caught up

  // Non-primary states
  Stray,         // Has PG data but not in current acting set
  ReplicaActive, // Replica in acting set, serving reads

  // Terminal/error states
  Down,       // Not enough peers to form quorum
  Incomplete, // Cannot recover (insufficient data)
  Deleting,   // PG is being removed
};

const char *state_name(State s);

// ── Events (inputs to the state machine) ───────────────────────────
//
// Ceph has ~50 event types. Most relate to PGLog coordination,
// reservation protocols, or features we don't need (snap trim, scrub
// scheduling, EC partial writes, unfound objects).

namespace event {

// New epoch from the monitor. Contains updated acting/up sets.
// Replaces Ceph's AdvMap + ActMap.
struct AdvanceMap {
  epoch_t new_epoch;
  ActingSet new_acting;
  ActingSet new_up;
  int new_pool_size;     // desired replication factor
  int new_pool_min_size; // minimum size to serve IO
  // OSDs from prior intervals (same as Initialize::prior_osds).
  std::vector<osd_id_t> prior_osds;
};

// Initialize this PG on this OSD.
struct Initialize {
  pg_id_t pgid;
  osd_id_t whoami;
  epoch_t epoch;
  ActingSet acting;
  ActingSet up;
  int pool_size;
  int pool_min_size;
  PGInfo local_info; // persisted state from previous interval
  // OSDs from prior intervals that might have data for this PG.
  // Equivalent to Ceph's PastIntervals::PriorSet::probe.
  // Must be populated by the runtime from OSDMap history.
  std::vector<osd_id_t> prior_osds;
};

// Response from a peer with its visible object image.
// Replaces Ceph's MNotifyRec + MLogRec combined.
struct PeerInfoReceived {
  osd_id_t from;
  PeerInfo info;
  // Epoch of the query that triggered this response.
  // Used to discard stale replies from previous intervals.
  // Matches Ceph's pg_notify_t::query_epoch.
  epoch_t query_epoch = 0;
};

// A peer query timed out.
struct PeerQueryTimeout {
  osd_id_t peer;
};

// The OSDMap now reflects our up_thru. Replaces Ceph's ActMap check.
struct UpThruUpdated {
  epoch_t epoch;
};

// Activation committed to durable storage.
struct ActivateCommitted {};

// One replica has finished recovery (caught up to the authoritative image).
struct RecoveryComplete {
  osd_id_t peer;
  epoch_t epoch; // epoch when recovery was initiated — reject stale completions
};

// All replicas have been recovered.
struct AllReplicasRecovered {
  epoch_t epoch; // epoch when recovery was initiated — reject stale
  std::vector<osd_id_t> peers; // peers completed by this batch notification
};

// Request from primary to this replica: "you are in the acting set".
struct ReplicaActivate {
  osd_id_t from;      // sender OSD (must be acting primary)
  PeerInfo auth_info; // authoritative peer image from primary
  epoch_t activation_epoch;
};

// Replica has been recovered (caught up to the authoritative image).
// Sent by the runtime to the replica after data push completes.
struct ReplicaRecoveryComplete {
  uint64_t new_committed_length;
  ObjectImage recovered_image;
  epoch_t activation_epoch;
};

// This PG should be deleted.
struct DeleteStart {};

// Deletion progress.
struct DeleteComplete {};

} // namespace event

using PeeringEvent =
    std::variant<event::Initialize, event::AdvanceMap, event::PeerInfoReceived,
                 event::PeerQueryTimeout, event::UpThruUpdated,
                 event::ActivateCommitted, event::RecoveryComplete,
                 event::AllReplicasRecovered, event::ReplicaActivate,
                 event::ReplicaRecoveryComplete, event::DeleteStart,
                 event::DeleteComplete>;

// ── Effects (outputs from the state machine) ───────────────────────
//
// The runtime executes these. The state machine has zero side effects.
// This is the "reducer" pattern from the design doc.
//
// Ceph's PeeringListener has ~76 virtual methods. We collapse these
// into a small set of concrete effect types.

namespace effect {

// Ask a peer for its image summary. Replaces Ceph's pg_query_t(INFO).
struct SendQuery {
  osd_id_t target;
  pg_id_t pgid;
  epoch_t epoch;
};

// Tell a peer about our state. Replaces Ceph's pg_notify_t.
struct SendNotify {
  osd_id_t target;
  pg_id_t pgid;
  PeerInfo info;
  epoch_t epoch;
};

// Activate a replica. Replaces the MOSDPGLog activation message.
struct SendActivate {
  osd_id_t target;
  pg_id_t pgid;
  PeerInfo auth_info;
  epoch_t activation_epoch;
};

// PG is now active, start serving IO.
struct ActivatePG {
  pg_id_t pgid;
  uint64_t authoritative_length; // the quorum-max committed_length
  ObjectImage authoritative_image;
  epoch_t activation_epoch;
};

// Stop serving IO on this PG.
struct DeactivatePG {
  pg_id_t pgid;
};

// Schedule recovery: push data to short replicas.
// The runtime decides concurrency, bandwidth, and priority.
struct ScheduleRecovery {
  pg_id_t pgid;
  struct Target {
    osd_id_t osd;
    uint64_t peer_length;          // what the peer has
    uint64_t authoritative_length; // what they need
    std::vector<ObjRecovery> recoveries;
  };
  std::vector<Target> targets;
};

// Cancel ongoing recovery.
struct CancelRecovery {
  pg_id_t pgid;
};

// PG is now clean (all replicas caught up).
struct MarkClean {
  pg_id_t pgid;
};

// Persist PG metadata to durable storage.
struct PersistState {
  pg_id_t pgid;
  PGInfo info;
};

// Request up_thru update from the monitor.
struct RequestUpThru {
  epoch_t epoch;
};

// Update heartbeat peer set.
struct UpdateHeartbeats {
  std::vector<osd_id_t> peers;
};

// Publish PG stats to the monitor.
struct PublishStats {
  pg_id_t pgid;
  State state;
  uint64_t committed_length;
  ObjectImage image;
  ObjectImage authoritative_image;
  int acting_size;
  int up_size;
};

// Request that this PG be deleted.
struct DeletePG {
  pg_id_t pgid;
};

// Request acting set change (Ceph's pg_temp). Tells the monitor
// that the current acting set is suboptimal and should be changed.
struct RequestActingChange {
  pg_id_t pgid;
  std::vector<osd_id_t> want_acting; // desired acting set
};

// State transition log (for observability).
struct LogTransition {
  pg_id_t pgid;
  State from;
  State to;
  const char *reason;
};

} // namespace effect

using PeeringEffect =
    std::variant<effect::SendQuery, effect::SendNotify, effect::SendActivate,
                 effect::ActivatePG, effect::DeactivatePG,
                 effect::ScheduleRecovery, effect::CancelRecovery,
                 effect::MarkClean, effect::PersistState, effect::RequestUpThru,
                 effect::RequestActingChange, effect::UpdateHeartbeats,
                 effect::PublishStats, effect::DeletePG, effect::LogTransition>;

// A validated event has stale/epoch checks applied before reducer dispatch.
using ValidatedEvent = PeeringEvent;

// Minimal result carrier for the planned pure-step shape.
// `from`/`to` preserve the state boundary in C++-native form; callers that
// only care about effects can still ignore them.
struct StepResult {
  State from;
  State to;
  std::vector<PeeringEffect> effects;
};

// Apply epoch-guard rules to one raw input event.
// Returns `std::nullopt` when the event is stale for the provided `reset`
// epoch.
std::optional<ValidatedEvent> validate_event(epoch_t reset,
                                             const PeeringEvent &event);

} // namespace vermilion::peering
