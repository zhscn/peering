# Roadmap: Lean Formalization Of The Append-Only Peering State Machine

## High-Level Goal

The goal is to extract a peering state machine from Ceph and verify a
simplified version of it in Lean 4 under a restricted RADOS IO model:

- append-only writes
- single-writer semantics
- no divergence
- no log merge
- no missing-set reconstruction

Under those restrictions, the recovery-relevant history collapses to
an explicit journal prefix plus object-image summaries, which makes the
peering model much smaller and more theorem-friendly than full Ceph peering.

One important refinement now applies:

- objectwise committed lengths are not enough by themselves for PG-wide IO
  ordering
- the model should therefore include an explicit PG-scoped append-only journal
  for operation ordering
- object images remain the right summary for recovery and safety reasoning

This project is not about verifying arbitrary Ceph source code directly. It is
about proving properties of the extracted simplified reducer and checking its
alignment with the existing C++ implementation.

## Core Model Boundary

The semantic boundary is now clear and should stay stable:

- raw event
- validated event
- pure reducer step
- before/after snapshot
- emitted effects

In C++, this boundary already exists:

- `validate_event(reset_epoch, event)`
- `process_validated(validated_event)`
- snapshot-first `step(snapshot, event)`

Lean should preserve that shape.

## Simplifying Assumptions

- each PG still has an explicit append-only commit order
- append-only object images are the semantic payload
- missing objects mean visible length `0`
- authority is represented by:
  - authoritative committed journal sequence
  - objectwise maximum visible length
  - per-object authority source
- recovery plans are just objectwise authority-minus-local gaps
- stale event filtering happens before reducer logic
- the reducer is pure and effect-emitting
- the semantic core keeps one `Recovering` state
- no separate `Backfill` state is needed unless the runtime later grows a
  materially different protocol for full rebuild versus incremental catch-up

In other words, the target model is:

- `PGJournal` for ordering
- `ObjectImage` for materialized committed state

not just object images alone.

## Current Source Of Truth

### Primary source

The current reducer semantics live in the C++ files:

- [`peer_info.h`](/home/zhscn/code/peering-lean/cpp/peer_info.h)
- [`peering_types.h`](/home/zhscn/code/peering-lean/cpp/peering_types.h)
- [`peering_state.h`](/home/zhscn/code/peering-lean/cpp/peering_state.h)
- [`peering_state.cc`](/home/zhscn/code/peering-lean/cpp/peering_state.cc)

### Early exploration / legacy reference

These are kept as early exploration material and historical reference. They are
not maintained as an active semantic model and are not translation targets:

- [`cross_validate.cc`](/home/zhscn/code/peering-lean/cpp/cross_validate.cc)
- [`idris/src/Peering/ObjectImage.idr`](/home/zhscn/code/peering-lean/idris/src/Peering/ObjectImage.idr)
- [`idris/src/Peering/Types.idr`](/home/zhscn/code/peering-lean/idris/src/Peering/Types.idr)
- [`idris/src/Peering/ImageMachine.idr`](/home/zhscn/code/peering-lean/idris/src/Peering/ImageMachine.idr)
- [`idris/src/Peering/ImageProcess.idr`](/home/zhscn/code/peering-lean/idris/src/Peering/ImageProcess.idr)
- [`idris/src/Peering/ImageInvariants.idr`](/home/zhscn/code/peering-lean/idris/src/Peering/ImageInvariants.idr)
- [`idris/src/Peering/ImageRefinement.idr`](/home/zhscn/code/peering-lean/idris/src/Peering/ImageRefinement.idr)

Those modules are still useful mainly for:

- the reduced semantic snapshot design
- the validated-event boundary
- invariant decomposition
- replay/refinement layering

## Current Status

### Already done

- The Ceph peering logic has been extracted into a heavily simplified C++
  reducer.
- The C++ implementation already separates validation from reduction.
- The C++ implementation already exposes snapshot-first stepping APIs.
- The C++ implementation now carries explicit journal progress:
  - `committed_seq` in peer and PG summaries,
  - `authoritative_seq` in activation/recovery effects and snapshots.
- Authority and recovery are now based on:
  - journal prefix progress,
  - object images,
  - per-object authority sources.
- Recovery plans now carry explicit source OSDs for object gaps.
- Replica activation now carries the full authority source map, not just a
  collapsed image summary.
- `cross_validate.cc` now emits structured replay/debug traces:
  - JSONL step records by default,
  - legacy text output behind a compatibility flag,
  - journal progress fields,
  - per-object recovery sources,
  - source-aware replica-activation data,
  - recomputed semantic checks.
- A Lean project now exists and builds successfully with `lake build`.
- The first Lean modules are in place:
  - [`Peering/Types.lean`](/home/zhscn/code/peering-lean/Peering/Types.lean)
  - [`Peering/Image.lean`](/home/zhscn/code/peering-lean/Peering/Image.lean)
- The Lean type/image layer now includes:
  - compact journal-progress fields,
  - source-aware object recovery records,
  - source-aware recovery-plan scaffolding.
- The first Lean-oriented design notes are in place:
  - [`docs/lean-design-summary.md`](/home/zhscn/code/peering-lean/docs/lean-design-summary.md)
  - [`docs/idris-reference-notes.md`](/home/zhscn/code/peering-lean/docs/idris-reference-notes.md)

Idris status:

- the Idris codebase is deprecated as an active model
- it is kept only as early exploration and historical proof/replay reference
- current maintained semantics are the extracted C++ reducer plus Lean

### In progress

- settling the first compact Lean semantic state
- preserving the validated-event boundary in Lean
- moving from the type/image layer to a small executable reducer subset in
  `Machine.lean`

### Not done yet

- `Machine.lean`
- explicit Lean invariants over reachable semantic state
- replay parsing and comparison against the updated C++ output shape
- refinement/simulation theorems

## Lean Scope Right Now

The Lean effort should proceed in this order:

1. compact journal-progress model
2. image algebra
3. compact semantic state
4. validation + reducer subset
5. invariant definitions
6. one-step preservation proofs
7. trace/reachability layer
8. replay/refinement layer

This keeps the project proof-oriented and avoids pulling replay and refinement
concerns into the core reducer too early.

## Immediate Next Milestone

The next concrete milestone is still:

- implement `Machine.lean`
- define `validateEvent`
- define `reduceValidated`
- define `step`
- support a small event subset
- prove one meaningful image-safety preservation theorem

The first event subset should stay small:

- `Initialize`
- `PeerInfoReceived`
- `PeerQueryTimeout`
- `UpThruUpdated`
- `ReplicaActivate`
- `ReplicaRecoveryComplete`
- `RecoveryComplete`
- `AllReplicasRecovered`

`AdvanceMap` should be added immediately after that first reducer milestone,
because interval changes and `min_size` logic are where the model starts to
interact with more realistic peering control flow.

No separate `Backfill` state should be introduced at this stage. The semantic
core should keep a single `Recovering` state and model both partial catch-up
and full rebuild as recovery against the authoritative `(seq, image, sources)`
state.

## First Proof Target

The first proof target should be a reduced image-safety invariant, not a full
Ceph-style global theorem.

Start with propositions corresponding to:

- local committed journal progress is at most the authoritative committed
  journal progress
- local image is within authority
- acting peer images are within authority
- peer recovery plans match the current authority/image gaps
- local recovery plan matches the current authority/image gap
- accepted recovery progress never rolls local image or journal progress
  backward

This is the smallest useful theorem layer that still matches the real reducer
semantics.

Immediately after that, add prefix-order properties for the explicit PG
journal.

## Replay Strategy

Replay should compare semantic projections before comparing full snapshots.

The intended layering is:

- full C++ replay/debug snapshot
- smaller semantic snapshot
- normalized semantic snapshot
- semantic equality / refinement check

The earlier Idris exploration already illustrated why replay should not demand
full structural equality over every bookkeeping field.

Disagreement handling should follow a soundness-first workflow:

- localize the first mismatching step
- compare reduced semantic snapshots, not the full debug surface
- recompute semantic checks independently from the observed snapshot
- classify the mismatch as parser/projection bug, Lean mismatch, C++ bug, or
  spec ambiguity before changing implementations

See [`docs/replay-triage.md`](/home/zhscn/code/peering-lean/docs/replay-triage.md).

## Non-Goals

For now, do not try to do any of the following:

- verify full Ceph peering
- verify arbitrary C++ source details line-by-line
- model log merge, divergence repair, or missing-set reconstruction
- prove liveness/fairness early
- revive Idris as a co-equal maintained model
- copy the Idris encoding mechanically into Lean
- overuse intrinsic/dependent encodings before the reducer boundary is stable

## Success Criteria

The first successful Lean version should provide:

- a compact semantic model of the extracted append-only peering reducer
- an explicit PG-scoped append-only ordering model
- machine-checked image-safety proofs
- a clean reduced snapshot for replay comparison
- a path toward trace-level refinement against the C++ implementation

The standard is:

clarity of semantic boundaries, correctness of the simplified append-only
model, and maintainability of the proof development.
