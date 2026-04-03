# Peering

This repository contains a reduced append-only model of Ceph peering with two
maintained pieces:

- a C++ reducer and replay trace generator in [`cpp/`](cpp)
- a Lean 4 formalization and replay checker in [`Peering/`](Peering)

The project goal is narrow on purpose: prove storage-safety properties for the
reduced semantic model, not verify full Ceph peering end to end.

## AI Declaration

This repository includes material generated or edited with AI assistance,
including code, proofs, comments, and documentation. Treat the repository as
an engineering artifact that still requires human review, testing, and
validation before operational use.

## Status

The scoped proof project is complete for the current `lean-core` surface:

- the reduced semantic model is implemented in C++ and formalized in Lean
- the Lean side proves the main image-safety invariant over the supported
  event surface
- supported traces from the empty start state preserve that invariant
- executable replay checks are connected back to theorem-level facts
- replay from C++ traces is kept green in CI and large randomized local fuzz
  runs

This is the right current claim:

- the C++ reducer is replay-validated against the Lean model on the current
  `lean-core` surface
- the reducer has been stress-tested with large randomized traces while also
  checking the C++ executable invariant and Lean replay alignment
- this is strong evidence that the extracted C++ reducer can be kept aligned
  with the Lean proof on the scoped surface

It is not the right claim to say the whole C++ implementation is proved. What
is not claimed here:

- full Ceph correctness
- unrestricted proof coverage for every `full`-profile replay trace
- liveness or fairness
- proof of the async runtime or effect executor
- divergence repair, log merge, missing-set reconstruction, or full backfill
  semantics

## Guarantees

On the supported `lean-core` surface, the Lean proof establishes an
image-safety invariant over the reduced semantic snapshot.

At a high level, it guarantees:

- authority is derived coherently from the current known peer images
- the authoritative image, authoritative source map, and authoritative
  committed sequence agree with each other
- the local PG state never claims committed progress beyond authority
- the local materialized image is always a prefix of the authoritative image
- acting replicas never claim progress or image data beyond authority
- peer recovery plans are exactly the plans recomputed from authority and the
  current acting replica gaps
- the local recovery plan is exactly the plan recomputed from authority and the
  local gap

The proof also defines and relates the stronger states:

- `ImageClean`: no remaining peer or local recovery work, and local plus acting
  replicas match authority
- `ImageRecovering`: the base invariant still holds, but some local or replica
  gap remains

For the current scope, the strongest honest summary is:

- supported one-step events preserve the invariant
- supported traces from the empty start snapshot preserve the invariant
- successful supported replay traces from the C++ reducer yield theorem-level
  invariant facts on the Lean side

## Storage View

From the storage point of view, this proof is about not inventing or
mis-ordering committed state.

What it means operationally:

- the reducer never accepts local committed journal progress beyond the current
  authority
- the reducer never treats local object state as containing bytes beyond the
  authoritative image
- the reducer never treats acting replicas as more up to date than authority
- recovery work is always computed from explicit byte gaps against authority,
  not from ad hoc guesses
- local and replica recovery plans stay synchronized with the same
  authority/source computation

For a storage engineer, the key mental model is:

- `authSeq` is the authoritative committed journal prefix
- `authImage` is the authoritative committed object image
- `authSources` says which replica currently backs each authoritative object
  extent
- `peerRecoveryPlans` and `localRecoveryPlan` are derived obligations needed to
  bring short replicas or the local PG up to authority

So the theorem is not just “some abstract invariant holds.” It says the reducer
keeps the committed storage view internally coherent while peering, remapping,
activating replicas, and scheduling recovery on the supported surface.

## Real Ceph Mapping

This reducer is intentionally smaller than full Ceph peering, but it keeps the
same correctness-critical control shape.

Additional states still matter to Ceph engineers reading the code:

- `Down` and `Incomplete` still accept late peer info in the reduced model,
  matching the real need to recover from stalled peering
- `Deleting` is modeled in C++, but it is outside the current proof-focused
  `lean-core` surface
- interval changes and acting-set changes are handled through `AdvanceMap`,
  which is part of the proved surface

What is simplified away relative to real Ceph:

- no divergent logs
- no log merge
- no missing-set reconstruction
- no separate semantic model for full backfill versus incremental catch-up
- append-only journal/storage assumptions

That simplification is deliberate. The model keeps the part of peering that is
most important for storage-safety reasoning: selecting authority, constraining
local and replica state to that authority, and deriving exact recovery work.
The fuller algorithmic description is in the next section.

## Textbook Overview

This section is the shortest useful “what is this state machine actually
doing?” description for an engineer who knows Ceph peering but has not read the
Lean proof.

### Core reduction

Full Ceph peering has to deal with divergent logs, missing-set reconstruction,
log merge, and the distinction between incremental catch-up and full backfill.
This model deliberately removes those cases by assuming append-only committed
storage.

Under that assumption, the semantic state of a PG can be reduced to:

- a committed journal prefix
- a committed materialized object image
- an object-by-object authority/source map

That is why the model can focus on authority selection and recovery-gap
derivation instead of full log reconciliation.

### Main semantic question

The central question in peering is:

- what state is authoritative for this PG right now?

In this model, authority is recomputed from the current known peer images:

- `authSeq`: authoritative committed journal prefix
- `authImage`: authoritative committed object image
- `authSources`: which peer currently backs each authoritative object extent

Once authority is fixed, recovery work is not guessed. It is derived exactly as
the gap between authority and the current local/replica images.

### Snapshot contents

The reduced snapshot keeps the pieces that matter for reducer decisions:

- control state: `Initial`, `GetPeerInfo`, `WaitUpThru`, `Active`,
  `Recovering`, `Clean`, `Stray`, `ReplicaActive`, plus `Down`,
  `Incomplete`, and `Deleting`
- local PG progress: committed seq, committed image, peering history
- placement inputs: `acting`, `up`, pool size, `min_size`
- peer knowledge: `peer_info`, queried/responded peers, prior-interval peers
- authority state: `authSeq`, `authImage`, `authSources`
- work state: `peerRecoveryPlans`, `localRecoveryPlan`, `recoveryTargets`

### Primary-side algorithm

The primary-side control flow is:

1. `Initial -> GetPeerInfo`
   Start peering and query peers in the acting set, up set, and prior set.
2. `GetPeerInfo`
   Accumulate peer reports and recompute the best authoritative state from the
   known peer images.
3. `GetPeerInfo -> WaitUpThru | Active`
   If peering history must advance first, wait for `up_thru`. Otherwise
   activate directly.
4. `WaitUpThru -> Active`
   Once history is sufficiently current, continue peering.
5. `Active -> Recovering | Clean`
   If all acting replicas already match authority, the PG is clean. Otherwise
   compute exact recovery plans.
6. `Recovering -> Clean`
   Recovery progress events discharge those plans until no authority gap
   remains.

### Replica-side algorithm

The replica-side control flow is:

1. `Initial -> Stray`
   The replica exists but is not yet activated for the current interval.
2. `Stray -> ReplicaActive`
   `ReplicaActivate` installs the authority chosen by the primary and computes
   any needed local recovery work.
3. `ReplicaActive`
   The replica remains bound to that authority and reports completion through
   `ReplicaRecoveryComplete`.

The important runtime contract is that `ReplicaActivate` must carry one fresh,
internally consistent authority snapshot from the primary. The proof does not
cover arbitrary stale or partially reconstructed activation payloads.

### Recovery semantics

Recovery is modeled as exact storage work, not a vague state transition:

- a short acting replica gets a per-object recovery plan derived from
  authority
- the local PG gets its own recovery plan from the same authority
- each recovery record is a concrete byte-range obligation

This is what makes the model storage-oriented rather than merely control-flow
oriented.

### What the proof means here

The theorem does not say “peering eventually succeeds.” It says:

- the machine never invents committed progress beyond authority
- the machine never lets local or replica image state exceed authority
- the machine keeps recovery plans synchronized with the same authority
  computation
- those facts survive all supported steps and traces from startup

So the append-only peering proof is best read as a storage-safety theorem for
authority selection and recovery scheduling, not as a full distributed-system
correctness theorem.

## Repo Layout

- [`cpp/`](cpp): executable source of truth for the reduced state machine
- [`Peering/`](Peering): Lean model, invariants, and replay parser/checker
- [`PeeringReplay.lean`](PeeringReplay.lean): Lean replay executable entrypoint
- [`scripts/replay_fuzz.py`](scripts/replay_fuzz.py): randomized replay driver
- [`docs/`](docs): design notes, proof scope, and replay triage guidance
- [`roadmap.md`](roadmap.md): current project scope and status

## Profiles

The replay generator has two event profiles:

- `lean-core`: the proof-aligned subset currently covered by the main Lean
  theorem layer
- `full`: a broader randomized C++ fuzz surface used for implementation stress
  testing

Use `lean-core` when you want replay and proofs to line up directly. Use
`full` when you want broader bug-finding coverage in the C++ implementation.

## Prerequisites

- CMake 3.20+
- a C++23 compiler
- Lean 4 via `elan` / `lake`
- Python 3

The C++ build fetches third-party dependencies through CMake
(`glaze`, `fmt`, and `CLI11`).

## Build

```bash
cmake -S . -B build -G Ninja
cmake --build build --target cross_validate
lake build
lake build peering-replay
```

## Quick Start

Generate one replay trace from the C++ reducer:

```bash
./build/cpp/cross_validate --profile lean-core --seed 1 --events 25 > trace.jsonl
```

Replay that trace in Lean:

```bash
./.lake/build/bin/peering-replay trace.jsonl
```

Or pipe directly from C++ to Lean:

```bash
./build/cpp/cross_validate --profile lean-core --seed 1 --events 25 | ./.lake/build/bin/peering-replay -
```

Run randomized replay fuzzing:

```bash
python3 scripts/replay_fuzz.py \
  --profile lean-core \
  --cycles 20 \
  --event-range 32 256 \
  --stop-on-first-failure \
  --require-cpp-image-invariant
```

To stress a wider C++ surface, switch to `--profile full`.

A larger local validation run that now passes cleanly is:

```bash
./scripts/replay_fuzz.py \
  --cycles 1024 \
  --event-range 1024 32768 \
  --profile lean-core \
  --stop-on-first-failure \
  --rebuild \
  --require-cpp-image-invariant \
  --jobs 8
```

That command is evidence for alignment, not a replacement for proof.

## CI

GitHub Actions builds the C++ and Lean targets, runs randomized `lean-core`
fuzzing, runs randomized `full`-profile fuzzing, and uploads replay artifacts
only on failure.

See [`.github/workflows/ci.yml`](.github/workflows/ci.yml).

## Where To Read Next

- [`docs/lean-design-summary.md`](docs/lean-design-summary.md): current design
  boundary and proof status
- [`docs/pg-journal-model.md`](docs/pg-journal-model.md): append-only journal
  model and storage-view intuition
- [`docs/replay-triage.md`](docs/replay-triage.md): how to debug replay
  mismatches
- [`roadmap.md`](roadmap.md): scoped goals, non-goals, and optional follow-on
  work
