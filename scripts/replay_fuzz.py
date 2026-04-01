#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import os
import random
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


@dataclass
class RunConfig:
    cycle: int
    seed: int
    event: int


@dataclass
class FailureRecord:
    config: RunConfig
    cross_validate_returncode: int
    replayer_returncode: int
    cross_validate_stderr: str
    replayer_stderr: str
    trace_path: str | None


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Run cross_validate with random seeds, pipe each trace to "
            "the Lean replayer, and report failing configurations."
        )
    )
    parser.add_argument(
        "--cycles",
        type=int,
        default=10,
        help="Number of random replay runs to execute.",
    )
    parser.add_argument(
        "--event",
        type=int,
        default=25,
        help="Fixed maximum number of generated events per cycle.",
    )
    parser.add_argument(
        "--event-range",
        nargs=2,
        type=int,
        default=None,
        metavar=("MIN", "MAX"),
        help="Inclusive random range for generated events per cycle.",
    )
    parser.add_argument(
        "--cross-validate",
        type=Path,
        default=Path("build/cpp/cross_validate"),
        help="Path to the cross_validate executable.",
    )
    parser.add_argument(
        "--replayer",
        type=Path,
        default=Path(".lake/build/bin/peering-replay"),
        help="Path to the Lean replay executable.",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=None,
        help="Fixed cross_validate seed for every cycle. If omitted, each cycle gets a fresh random seed.",
    )
    parser.add_argument(
        "--stop-on-first-failure",
        action="store_true",
        help="Stop immediately after the first failing cycle.",
    )
    parser.add_argument(
        "--save-failure-traces",
        type=Path,
        default=None,
        help="Directory where failing traces and a summary JSON file are written.",
    )
    parser.add_argument(
        "--rebuild",
        action="store_true",
        help="Rebuild cross_validate and peering-replay before fuzzing.",
    )
    return parser


def ensure_executable(path: Path, label: str) -> None:
    if not path.exists():
        raise FileNotFoundError(f"{label} does not exist: {path}")
    if not path.is_file():
        raise FileNotFoundError(f"{label} is not a file: {path}")
    if not os.access(path, os.X_OK):
        raise FileNotFoundError(f"{label} is not executable: {path}")


def run_checked(
    cmd: Sequence[str],
    *,
    env: dict[str, str] | None = None,
    cwd: Path | None = None,
    label: str,
) -> None:
    result = subprocess.run(
        list(cmd),
        capture_output=True,
        text=True,
        check=False,
        env=env,
        cwd=cwd,
    )
    if result.returncode == 0:
        return
    if result.stdout.strip():
        print(
            result.stdout,
            file=sys.stderr,
            end="" if result.stdout.endswith("\n") else "\n",
        )
    if result.stderr.strip():
        print(
            result.stderr,
            file=sys.stderr,
            end="" if result.stderr.endswith("\n") else "\n",
        )
    raise RuntimeError(f"{label} failed with exit code {result.returncode}")


def rebuild_targets(repo_root: Path) -> None:
    print("Rebuilding cross_validate and peering-replay...", flush=True)
    run_checked(
        ["cmake", "-S", ".", "-B", "build", "-DCMAKE_BUILD_TYPE=Release"],
        cwd=repo_root,
        label="cmake configure",
    )
    build_env = dict(os.environ)
    build_env["CCACHE_DISABLE"] = "1"
    run_checked(
        ["cmake", "--build", "build", "--target", "cross_validate"],
        cwd=repo_root,
        env=build_env,
        label="cmake build cross_validate",
    )
    run_checked(
        ["lake", "build", "peering-replay"],
        cwd=repo_root,
        label="lake build peering-replay",
    )


def run_cycle(
    config: RunConfig,
    cross_validate: Path,
    replayer: Path,
    failure_dir: Path | None,
) -> tuple[bool, FailureRecord | None]:
    cross_validate_cmd = [
        str(cross_validate),
        "--profile",
        "lean-core",
        "--seed",
        str(config.seed),
        "--events",
        str(config.event),
    ]
    cross_validate_result = subprocess.run(
        cross_validate_cmd,
        capture_output=True,
        text=True,
        check=False,
    )

    trace = cross_validate_result.stdout
    replayer_result = subprocess.run(
        [str(replayer), "-"],
        input=trace,
        capture_output=True,
        text=True,
        check=False,
    )

    success = cross_validate_result.returncode == 0 and replayer_result.returncode == 0
    if success:
        return True, None

    trace_path = None
    if failure_dir is not None:
        failure_dir.mkdir(parents=True, exist_ok=True)
        trace_file = (
            failure_dir / f"failure-cycle-{config.cycle:04d}-seed-{config.seed}.jsonl"
        )
        trace_file.write_text(trace, encoding="utf-8")
        trace_path = str(trace_file)

    return False, FailureRecord(
        config=config,
        cross_validate_returncode=cross_validate_result.returncode,
        replayer_returncode=replayer_result.returncode,
        cross_validate_stderr=cross_validate_result.stderr,
        replayer_stderr=replayer_result.stderr,
        trace_path=trace_path,
    )


def report_failures(failures: Sequence[FailureRecord]) -> None:
    print("\nFailures:")
    for failure in failures:
        config = failure.config
        print(
            f"- cycle={config.cycle} seed={config.seed} "
            f"event={config.event} "
            f"profile=lean-core "
            f"cross_validate_rc={failure.cross_validate_returncode} "
            f"replayer_rc={failure.replayer_returncode}"
        )
        if failure.trace_path is not None:
            print(f"  trace: {failure.trace_path}")
        if failure.cross_validate_stderr.strip():
            print("  cross_validate stderr:")
            for line in failure.cross_validate_stderr.strip().splitlines():
                print(f"    {line}")
        if failure.replayer_stderr.strip():
            print("  replayer stderr:")
            for line in failure.replayer_stderr.strip().splitlines():
                print(f"    {line}")


def save_failure_summary(failures: Sequence[FailureRecord], failure_dir: Path) -> None:
    failure_dir.mkdir(parents=True, exist_ok=True)
    summary_path = failure_dir / "failures.json"
    payload = []
    for failure in failures:
        item = asdict(failure)
        item["config"] = asdict(failure.config)
        payload.append(item)
    summary_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"failure summary: {summary_path}")


def choose_cycle_size(
    rng: random.Random,
    *,
    fixed: int,
    bounds: tuple[int, int] | None,
    label: str,
) -> int:
    if bounds is None:
        return fixed
    minimum, maximum = bounds
    if minimum <= 0 or maximum <= 0:
        raise ValueError(f"{label} min/max must be positive")
    if minimum > maximum:
        raise ValueError(f"{label} min must be <= max")
    return rng.randint(minimum, maximum)


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parent.parent

    cross_validate = args.cross_validate
    replayer = args.replayer
    if not cross_validate.is_absolute():
        cross_validate = repo_root / cross_validate
    if not replayer.is_absolute():
        replayer = repo_root / replayer

    try:
        if args.cycles <= 0:
            raise ValueError("--cycles must be positive")
        if args.event <= 0:
            raise ValueError("--event must be positive")
        if args.rebuild:
            rebuild_targets(repo_root)
        ensure_executable(cross_validate, "cross_validate")
        ensure_executable(replayer, "replayer")
    except (FileNotFoundError, RuntimeError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 2

    rng: random.Random = random.SystemRandom()
    failures: list[FailureRecord] = []
    seen_configs: set[tuple[int, int]] = set()

    for cycle in range(1, args.cycles + 1):
        try:
            event = choose_cycle_size(
                rng,
                fixed=args.event,
                bounds=tuple(args.event_range)
                if args.event_range is not None
                else None,
                label="event",
            )
        except ValueError as exc:
            print(str(exc), file=sys.stderr)
            return 2
        if args.seed is not None:
            seed = args.seed
        else:
            while True:
                seed = rng.randrange(0, 2**63)
                dedup_key = (seed, event)
                if dedup_key not in seen_configs:
                    seen_configs.add(dedup_key)
                    break
        config = RunConfig(
            cycle=cycle,
            seed=seed,
            event=event,
        )
        print(
            f"[{cycle}/{args.cycles}] "
            f"seed={config.seed} event={config.event} profile=lean-core",
            flush=True,
        )
        ok, failure = run_cycle(
            config=config,
            cross_validate=cross_validate,
            replayer=replayer,
            failure_dir=args.save_failure_traces,
        )
        if ok:
            print("  ok", flush=True)
            continue

        print("  failure", flush=True)
        assert failure is not None
        failures.append(failure)
        if args.stop_on_first_failure:
            break

    if failures:
        report_failures(failures)
        if args.save_failure_traces is not None:
            save_failure_summary(failures, args.save_failure_traces)
        return 1

    print(f"\nAll {args.cycles} cycles passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
