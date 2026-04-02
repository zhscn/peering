# Replay Triage Workflow

## Goal

Replay disagreement is a soundness and design-debugging signal, not just an
implementation mismatch.

When Lean replay disagrees with C++, the first-class question is:

- did we expose a design error,
- a C++ bug,
- a Lean modeling mismatch,
- or a replay/parser/projection bug?

The workflow should be set up to answer that question at the first diverging
step.

## Maintained roles

- C++ is the executable source of truth for current implementation behavior.
- Lean is the maintained formalization target.
- Replay exists to test semantic agreement and to expose soundness/design
  errors early.

This means disagreement should not be resolved by assuming Lean is wrong
automatically.

## Comparison target

Replay should compare a reduced normalized semantic snapshot, not the entire
C++ debug surface.

The first comparison target should include:

- state
- epoch
- acting and up
- local committed sequence
- authoritative sequence
- authoritative image
- authority sources
- peer recovery plans
- local recovery plan
- soundness-relevant flags such as `needUpThru`

Debug-only or order-sensitive fields should be normalized away unless they are
part of the semantic contract.

## Soundness-first workflow

1. Find the first mismatching step.
2. Compare the parsed raw event and observed snapshot boundary.
3. Compare the reduced normalized semantic snapshot only.
4. Recompute semantic checks independently from the observed snapshot.
5. Classify the mismatch before changing either implementation.

Only the first diverging step should drive diagnosis. Later differences are
usually fallout.

## Classification

### Parser or projection bug

Signs:

- the C++ step is internally coherent,
- but Lean parsed the event or snapshot incorrectly,
- or normalization lost/kept the wrong information.

Fix:

- repair the replay format, parser, or normalization layer.

### Lean modeling mismatch

Signs:

- C++ before/event/after snapshots are coherent,
- recomputed semantic checks agree with C++,
- Lean produces a different semantic next state.

Fix:

- repair `validateEvent`, `reduceValidated`, or the Lean semantic projection.

### C++ bug

Signs:

- the C++ after-state violates recomputed semantic checks or documented
  invariants,
- Lean preserves the intended invariant and disagrees with the emitted C++
  state,
- or the emitted C++ effects conflict with the reduced semantic snapshot.

Fix:

- repair the extracted reducer or tighten its snapshot/effect boundary.

### Spec ambiguity

Signs:

- both C++ and Lean are plausible,
- but the docs do not pin down the intended behavior tightly enough.

Fix:

- strengthen the semantic contract before choosing which implementation to
  change.

## Independent checks

Replay should be triangulated with independent executable checks:

- C++ step result
- C++ semantic recomputation from snapshot
- Lean replay result
- invariant checker over the reduced semantic snapshot

Typical outcomes:

- C++ step matches recomputation, Lean disagrees:
  likely Lean mismatch.
- C++ step violates recomputation or invariant checks:
  likely C++ bug or design bug.
- both implementations disagree with the documented semantic contract:
  design/spec error.

## Expected tooling shape

The intended toolchain is:

- [`cross_validate.cc`](/home/zhscn/code/peering-lean/cpp/cross_validate.cc)
  generates structured before/event/after traces
- Lean replay parses those traces
- Lean compares normalized semantic snapshots
- mismatch output reports the first failing step with a focused semantic diff

The preferred trace format is structured JSONL. Legacy text output can remain
available only as a compatibility path for older exploratory tooling.

The current Lean replay path already handles the checked-in `lean-core`
boundary and is kept green with CI plus randomized fuzzing. So replay work is
now mostly about localizing proof/design issues quickly, not about repairing a
known unstable bridge.

The replay output should make it easy to inspect:

- before snapshot
- event
- expected observed after snapshot
- Lean-computed after snapshot
- recomputed invariant/soundness checks

## Design rule

Soundness checks come before alignment work.

If replay exposes that the extracted reducer violates the intended append-only
semantic contract, the right response is to fix the design or implementation,
not to force Lean to mimic the bug.
