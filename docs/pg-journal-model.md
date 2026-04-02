# PGJournal + ObjectImage Model

## Why this model

The append-only blobstore still needs an explicit ordering for IOs within a PG.

So the semantic model should not be:

- only objectwise committed lengths

It should be:

- a PG-scoped append-only journal for ordering
- an objectwise committed image for recovery and safety reasoning

This keeps the useful simplification relative to Ceph while avoiding the
mistake of pretending that object `0` or any other distinguished object can
stand in for a real PG-level commit order.

## Core semantic split

### `PGJournal`

The journal is the ordering layer.

Each committed operation in a PG gets a monotonically increasing sequence
number.

Minimal shape:

- `seq`
- `epoch`
- object id
- operation payload summary
- resulting committed object length, or append delta

The journal does not need full Ceph `PGLog` machinery:

- no divergent log rewrites
- no merge-log protocol
- no missing-set reconstruction
- no rollback-based reconciliation

It only needs prefix semantics.

### `ObjectImage`

The image is the materialized committed state summary:

- object id -> committed visible length

This remains the natural structure for:

- authority computation
- recovery-gap computation
- prefix reasoning
- recovery planning

### Replica progress

Each replica should expose both:

- journal progress
- materialized image progress

Minimal useful state:

- `committedSeq`
- `appliedSeq` or `checkpointedSeq`
- `image`

Current extracted reducer surface:

- `PeerInfo.committed_seq`
- `PGInfo.committed_seq`
- `authoritative_seq` in activation and recovery effects
- objectwise `auth_sources` for recovery and replica activation

## Peering interpretation

Under this model, peering does not choose a single global authority object.
Instead:

- journal prefix agreement determines ordered commit knowledge
- object image summarizes the committed materialized state
- recovery is coordinated from the authoritative committed prefix and the
  resulting image gaps

That means:

- the primary is a coordinator chosen by CRUSH/acting policy
- the primary is not selected from a distinguished data object
- authority is defined by committed journal prefix and derived image state

## Recovery interpretation

Recovery should be driven by the committed prefix, then expressed as object
gaps.

In practice:

1. compare replica committed journal prefixes
2. determine the authoritative committed prefix
3. derive the resulting authoritative image
4. compute peer and local recovery gaps from that image

The current extracted reducer already follows that direction:

- recovery plans carry per-object source OSDs
- replica activation carries the authoritative source map
- the acting primary remains the coordinator, not the implicit data source

So objectwise authority and data source selection are explicit in the model.

## Recovery states

The semantic core does not currently need a separate `Backfill` state.

For this append-only model, both:

- incremental catch-up of a short replica
- full rebuild of a very short or empty replica

are still just recovery toward the authoritative `(committedSeq, image,
authSources)` state.

So the current recommendation is:

- keep one `Recovering` state in the reducer
- do not reintroduce Ceph's `Backfill` split in the semantic core
- only add a recovery-mode tag later if the runtime grows materially different
  protocol steps for full rebuild versus incremental catch-up

## Minimal semantic types

Lean does not need to implement the full journal payload first.

The first proof-oriented journal types can stay small:

- `JournalSeq`
- `JournalEntryMeta`
- `JournalPrefix`
- `ReplicaProgress`

Example conceptual records:

```text
JournalSeq := Nat

JournalEntryMeta :=
  { seq : JournalSeq
  , epoch : Epoch
  , obj : ObjectId
  , newLength : Length
  }

ReplicaProgress :=
  { committedSeq : JournalSeq
  , appliedSeq : JournalSeq
  , image : ObjectImage
  }
```

The important property is that `image` is derived from a committed journal
prefix, not that Lean stores all concrete payload bytes.

## First safety properties

This model suggests the following first properties:

- committed journal sequence numbers are monotone
- accepted events never roll back committed prefix knowledge
- local image is consistent with local committed prefix
- local image is within authoritative image
- peer recovery plans correspond to authoritative image gaps
- activation is only allowed when the acting set has a sufficient authoritative
  committed prefix

## Current implementation consequence

Lean now treats ordering and image state as separate but linked:

- `Types.lean` now has the first compact journal progress and source-aware
  recovery fields
- `Image.lean` now has authority-based recovery-gap helpers
- `Machine.lean` now has the first executable reducer and replay-aligned
  snapshot/effect boundary
- `Invariants.lean` now includes the first image-safety and recovery-plan
  invariants as executable checks and propositions
- supported one-step preservation now covers the current `lean-core` proof
  surface, including `Initialize`, `AdvanceMap`, the primary-side progress
  handlers, and the replay-driven replica-side handlers under their stated
  support conditions
- supported traces from the empty start state now preserve the image-safety
  invariant
- successful supported replay now connects back to theorem-level
  `ImageInvariant` facts on the Lean side
- replay/refinement should compare a reduced semantic snapshot containing both
  committed prefix progress and derived image state

Broader replay/refinement statements and wider event coverage remain optional
extension work, not unfinished prerequisites for the current scoped project.
