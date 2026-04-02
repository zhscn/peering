# Idris Legacy Notes

## Status

The Idris code in [`idris/`](../idris) is
deprecated as an active model.

It is kept only as:

- early exploration of the simplified peering model
- historical reference for proof decomposition ideas
- historical reference for replay/refinement layering

It is not maintained for semantic consistency with the current extracted C++
reducer.

## Current maintained path

The maintained semantic path is:

- C++ reducer as executable source of truth
- Lean as the active formalization target

If C++ and Idris disagree, C++ wins unless the project explicitly revives Idris
for a bounded purpose.

## What is still worth reusing

The old Idris work is still useful for high-level ideas:

- validated-event boundary
- reduced semantic snapshot versus larger debug snapshot
- invariant decomposition
- replay/refinement layering

Those are architectural references only. They should not be treated as a
current executable or formal specification.

## Replay policy

Replay and cross-validation should now target Lean, not Idris.

The intended workflow is:

- generate traces from [`cross_validate.cc`](../cpp/cross_validate.cc)
- parse them into Lean
- compare normalized semantic snapshots in Lean against the C++ trace output

Mismatch handling is described in
[`replay-triage.md`](./replay-triage.md).

Updating Idris to keep pace with the current C++ reducer is not required.
