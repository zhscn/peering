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
- replay from C++ traces is kept green in CI

What is not claimed here:

- full Ceph correctness
- unrestricted proof coverage for every `full`-profile replay trace
- liveness or fairness
- divergence repair, log merge, missing-set reconstruction, or full backfill
  semantics

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
