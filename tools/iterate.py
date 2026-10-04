#!/usr/bin/env python3
"""One lane iteration: run what the change reaches, report the red set's delta.

    python3 tools/iterate.py --since REV [--fast] [--image-set SHA] [--jobs N]
                             [--native LOG_OR_DIR ...] [--certify RUN_DIR ...]

The loop of planning/design/iteration-architecture-2026-10-04.md section 5,
for the part that runs here: the `make check` steps the diff from REV can
reach (`make check-lane CHECK_CHANGED_SINCE=REV`, `check-fast-lane` with
`--fast`), which replays every unreached verdict from the store and runs the
rest; then `tools/reds.py collect` over the result (and any native module
logs or certify runs named), the delta against the previous build/reds.json,
and for each red of another kind the diff reaches (a test case, a book) the
narrowest command that produces its verdict -- printed, never started: an
overlay runs on a build box through the integrator, a certify through the
farm.  FN_VERDICT_STORE is passed through, so a shared store serves it.

Exit 0 when no reached step is red and no red is new; the table says the rest.
This is a lane's loop, not a gate: a READY and the batch's FORCE=1 pass are
live runs of their own (docs/testing.md "What make check is").
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import reds  # noqa: E402


def run_checks(since: str, fast: bool, jobs: int) -> int:
    target = "check-fast-lane" if fast else "check-lane"
    command = ["make", target, f"CHECK_CHANGED_SINCE={since}"]
    if jobs:
        command.append(f"CHECK_JOBS={jobs}")
    print("iterate: " + " ".join(command), flush=True)
    return subprocess.run(command, cwd=ROOT).returncode


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--since", required=True, metavar="REV",
                        help="the base the change is measured from (a sha, origin/dev, HEAD)")
    parser.add_argument("--fast", action="store_true", help="check-fast-lane instead of check-lane")
    parser.add_argument("--jobs", type=int, default=0)
    parser.add_argument("--image-set", default="", metavar="SHA",
                        help="the published set an overlay command should name")
    parser.add_argument("--native", nargs="*", default=[], metavar="LOG_OR_DIR",
                        help="native module logs to read reds from (fetched run logs)")
    parser.add_argument("--certify", nargs="*", default=[], metavar="RUN_DIR")
    parser.add_argument("--no-checks", action="store_true",
                        help="only collect, compare and select; run no step")
    args = parser.parse_args(argv)

    previous = reds.DEFAULT_OUT
    kept = previous.with_suffix(".previous.json")
    if previous.is_file():
        shutil.copy(previous, kept)
    code = 0 if args.no_checks else run_checks(args.since, args.fast, args.jobs)

    current = reds.collect(ROOT / "build" / "check-steps",
                           Path(os.environ.get("FN_VERDICT_STORE") or reds.check_steps.DEFAULT_CACHE),
                           args.native, args.certify)
    previous.parent.mkdir(parents=True, exist_ok=True)
    previous.write_text(json.dumps(current, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    new_reds = 0
    if kept.is_file():
        old = json.loads(kept.read_text(encoding="utf-8"))
        appeared, fixed, same = reds.delta(old, current)
        new_reds = len(appeared)
        print(f"\niterate: reds {old['head']} -> {current['head']}: {new_reds} new, "
              f"{len(fixed)} fixed, {same} unchanged")
        for red in appeared:
            print("NEW" + reds.line_of(red))
        for red in fixed:
            print("FIXED" + reds.line_of(red))
    else:
        print(f"\niterate: reds at {current['head']}: {len(current['reds'])} (first collection)")

    others = [(red, why) for red, why in reds.affected(current, args.since, args.image_set)
              if red["kind"] != "check-step"]
    if others:
        print(f"\niterate: {len(others)} red(s) of other kinds the diff reaches; run each where it runs:")
        for red, why in others:
            print(reds.line_of(red, why))
            print(f"      run: {reds.narrowest(red, args.image_set)}")
    return 1 if (code or new_reds) else 0


if __name__ == "__main__":
    raise SystemExit(main())
