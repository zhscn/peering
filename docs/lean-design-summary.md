# Lean Design Summary

## Purpose

This note records the current Lean design boundary for the append-only peering
model extracted from Ceph.

The goal is to formalize a simplified peering state machine under these RADOS
semantic restrictions:

- append-only writes
- single-writer semantics
- no divergence
- no log merge
- no missing-set reconstruction

Under those assumptions, recovery-relevant state collapses to:

- a compact committed journal prefix summary,
- object-image summaries,
- per-object authority sources,

which makes the peering model much smaller than full Ceph peering.

However, PG-wide IO ordering still needs to be explicit. So the intended model
is:

- a minimal append-only `PGJournal` for ordering
- an `ObjectImage` for materialized committed state

See [`pg-journal-model.md`](./pg-journal-model.md).

## Semantic Boundary

The Lean model should preserve the reducer boundary that already exists in C++:

- raw event
- validated event
- pure validated reduction step
- before/after snapshot
- emitted effects

The relevant C++ entry points are:

- `validate_event(reset_epoch, event)`
- `process_validated(validated_event)`
- snapshot-first `step(snapshot, event)`

That boundary is the right place to state invariants and replay/refinement
results.

## Source Hierarchy

### Primary source of truth

The current semantics are defined by the C++ reducer:

- [`peer_info.h`](../cpp/peer_info.h)
- [`peering_types.h`](../cpp/peering_types.h)
- [`peering_state.h`](../cpp/peering_state.h)
- [`peering_state.cc`](../cpp/peering_state.cc)

### Early exploration / legacy reference

The Idris code and earlier replay work are kept as early exploration and
historical reference. They are useful for proof structure, but they are not
maintained as an active semantic model and are not translation targets:

- [`cross_validate.cc`](../cpp/cross_validate.cc)
- [`idris-reference-notes.md`](./idris-reference-notes.md)

The main reusable ideas from that earlier exploration are:

- explicit validated-event boundaries
- a compact semantic state split from bookkeeping
- a reduced observable snapshot for proofs
- a larger replay/debug snapshot only for diagnostics

## What Lean Should Model Exactly First

- a compact PG journal-progress layer
- object-image algebra
- authority computation from known peer images
- recovery-plan derivation from authority sources
- stale/epoch validation guards
- the small primary/replica reducer subset needed for the first proof

The first Lean model should not try to encode every C++ field immediately.

## First Lean State

The first proof-oriented state should keep only fields that affect reducer
decisions:

- state/mode
- current epoch
- journal progress
- acting and up sets
- pool size and min size
- normalized local PG info
- authoritative committed sequence
- known peer infos
- queried/responded peers
- prior-interval probe set
- timed-out probes
- authoritative image
- authoritative source map
- peer recovery plans
- local recovery plan
- recovered peers
- `needUpThru`
- `pendingActingChange`
- `lastPeeringReset`

That state now exists in executable form in
[`Peering/Machine.lean`](../Peering/Machine.lean).
One implementation detail is now fixed intentionally: `peerInfo` is stored in a
deterministic `TreeMap`, not a list, so authority-source tie-breaking matches
the C++ reducer's ordered peer iteration instead of depending on message
arrival order.

## First Reducer Slice

The smallest useful event subset is:

- `Initialize`
- `PeerInfoReceived`
- `PeerQueryTimeout`
- `UpThruUpdated`
- `ReplicaActivate`
- `ReplicaRecoveryComplete`
- `RecoveryComplete`
- `AllReplicasRecovered`

`AdvanceMap` should come immediately after that first cut, because interval
changes and `min_size` handling are the first major control-flow complication.

Lean should keep a single `Recovering` state in this first reducer. There is
currently no need to reintroduce a separate Ceph-style `Backfill` state or a
recovery-mode split in the semantic core.

## First Invariant Layer

The first useful invariants should be reduced image-safety properties:

- local image is within authority
- local committed journal progress is at most authoritative committed progress
- acting peer images are within authority
- peer recovery plans match current authority-local gaps
- local recovery plan matches current authority-local gaps
- accepted recovery progress is monotone and never rolls local image or journal
  progress backward

These are strong enough to matter semantically and small enough to prove early.

Right after that, the Lean invariant layer should add journal-prefix monotonicity
for explicit per-PG ordering.

## Equality And Replay

Replay should compare reduced semantic projections before comparing full
snapshots.

The intended layering is:

- full C++ replay/debug snapshot
- smaller semantic snapshot
- normalized semantic snapshot
- semantic equality or refinement relation

This matches both the earlier Idris exploration and the current structure of
[`cross_validate.cc`](../cpp/cross_validate.cc).

When replay disagrees, the workflow should be soundness-first:

- isolate the first mismatching step
- compare normalized semantic projections
- recompute semantic checks independently from the observed snapshot
- classify the issue as parser/projection bug, Lean mismatch, C++ bug, or
  semantic-spec ambiguity

See [`replay-triage.md`](./replay-triage.md).

## Current Lean Status

The repo now has a working Lean scaffold:

- [`Peering/Types.lean`](../Peering/Types.lean)
- [`Peering/Image.lean`](../Peering/Image.lean)
- [`Peering/Machine.lean`](../Peering/Machine.lean)
- [`Peering/Invariants.lean`](../Peering/Invariants.lean)
- [`Peering/Replay.lean`](../Peering/Replay.lean)
- [`PeeringReplay.lean`](../PeeringReplay.lean)

Current coverage:

- core Lean data types exist
- compact journal-progress fields now exist in `Types.lean`
- the first image-algebra layer exists
- source-aware recovery-gap and recovery-plan helpers now exist in `Image.lean`
- an executable reducer skeleton now exists in `Machine.lean`
- the reducer now uses a deterministic map-backed `peerInfo` representation
  instead of list-order semantics
- a first explicit invariant layer now exists in `Invariants.lean`
- one-step preservation theorems now exist for `Initialize`,
  `PeerInfoReceived`, `PeerQueryTimeout`, `UpThruUpdated`,
  `ActivateCommitted`, `RecoveryComplete`, `AllReplicasRecovered`, and
  `AdvanceMap`
- snapshot-sensitive one-step preservation now exists for
  `ReplicaActivate` and `ReplicaRecoveryComplete`
- those preservation results are lifted through the handler,
  `reduceValidated`, and `step` boundaries for the currently supported subset
- a first supported trace/reachability layer now exists, including empty-start
  and initialize-headed trace corollaries
- checker soundness is now proved for `snapshotImageInvariant?`,
  `snapshotImageClean?`, and `snapshotImageRecovering?`
- a first structured JSONL replay parser/checker now exists in `Replay.lean`
- the checked-in `peering-replay` executable validates JSONL traces directly
- successful supported replay from the empty cursor now yields theorem-level
  `ImageInvariant` facts on the Lean side
- basic algebra lemmas are proved
- the project builds with `lake build`
- GitHub Actions now runs the C++ trace generator plus Lean replay under the
  `lean-core` event profile
- current `lean-core` replay is green against the extracted C++ reducer,
  including randomized fuzz runs over structured JSONL traces

Project status:

- C++ is the executable semantic source of truth
- Lean is the maintained formalization path
- Idris is deprecated and kept only as early exploration/reference material
- the scoped reduced proof project is complete on the current replay-facing
  semantic surface

Optional extensions:

- stronger reachable-state reasoning beyond explicit supported-trace witnesses
- cleaner unification between the current replay-facing theorem layer and the
  generic reachable-state/trace layer
- broader replay/refinement theorems beyond the current supported replay
  surface

## Current Conclusion

For the current repo scope, there is no required next proof step. The compact
append-only peering model, the supported one-step and trace-level safety
theorems, checker soundness, and the first replay-facing theorem layer are all
in place.

If development resumes, the right direction is extension work rather than
completion work:

1. fold the replay-facing theorem layer back into cleaner generic
   reachable-state statements
2. broaden replay/refinement theorems beyond the current supported replay
   surface
3. widen the proved surface only when additional C++ paths become
   caller-critical
