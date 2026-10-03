#!/usr/bin/env python3
"""Rank native FN_TRACE spans and compare matched log observations.

Process allocation samples include other threads and nested spans. Never
interpret their sum as unique allocation, peak residency, retained heap or
GC volume. An isolated-process tag is the probe caller's assertion.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

PREFIX = "FN_TRACE "


def analyze(path: Path) -> dict:
    groups = {}
    summaries = []
    with path.open(encoding="utf-8", errors="replace") as stream:
        for number, line in enumerate(stream, 1):
            if not line.startswith(PREFIX):
                continue
            try:
                event = json.loads(line[len(PREFIX):])
                if event["type"] == "summary":
                    summaries.append(event)
                    continue
                if event["type"] != "span":
                    raise ValueError("unknown trace record type")
                key = (event["phase"], event["allocation_scope"])
                duration = event["duration_us"]
                allocation = event["allocated_bytes"]
                if (not isinstance(duration, int) or duration < 0
                        or (allocation is not None and (not isinstance(allocation, int) or allocation < 0))):
                    raise ValueError("invalid span measurement")
                row = groups.setdefault(key, dict(phase=key[0], allocation_scope=key[1],
                    samples=0, duration_us_inclusive=0, max_duration_us=0,
                    allocation_samples=0, allocated_bytes_inclusive=0, max_allocated_bytes=0,
                    outcomes=Counter()))
                row["samples"] += 1
                row["duration_us_inclusive"] += duration
                row["max_duration_us"] = max(row["max_duration_us"], duration)
                row["outcomes"][event["outcome"]] += 1
                if allocation is not None:
                    row["allocation_samples"] += 1
                    row["allocated_bytes_inclusive"] += allocation
                    row["max_allocated_bytes"] = max(row["max_allocated_bytes"], allocation)
            except (KeyError, TypeError, ValueError) as error:
                raise ValueError(f"{path}:{number}: invalid FN_TRACE record: {error}") from error
    rows = list(groups.values())
    for row in rows:
        row["mean_allocated_bytes"] = (row["allocated_bytes_inclusive"] / row["allocation_samples"]
                                       if row["allocation_samples"] else None)
        row["mean_duration_us"] = row["duration_us_inclusive"] / row["samples"]
    rows.sort(key=lambda row: (row["mean_allocated_bytes"] or 0, row["mean_duration_us"]), reverse=True)
    return dict(log=str(path), phases=rows, summaries=summaries,
                scope="Inclusive samples: overlapping process/nested deltas are not unique allocation, retained heap or GC volume.")


def compare(current: dict, baseline: dict) -> list[dict]:
    old = {(r["phase"], r["allocation_scope"]): r for r in baseline["phases"]}
    result = []
    for row in current["phases"]:
        before = old.get((row["phase"], row["allocation_scope"]))
        if before:
            a, b = row["mean_allocated_bytes"], before["mean_allocated_bytes"]
            result.append(dict(phase=row["phase"], allocation_scope=row["allocation_scope"],
                               mean_allocated_bytes_delta=a - b if a is not None and b is not None else None,
                               mean_duration_us_delta=row["mean_duration_us"] - before["mean_duration_us"],
                               samples=(before["samples"], row["samples"])))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--compare", type=Path, help="baseline under matched source/runtime/profile/workload conditions")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    try:
        report = analyze(args.log)
        if args.compare:
            report["comparisons"] = compare(report, analyze(args.compare))
    except (OSError, ValueError) as error:
        parser.error(str(error))
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(report["scope"])
        print("phase scope samples mean-us max-us mean-allocated max-allocated outcomes")
        for row in report["phases"]:
            allocation = "disabled" if row["mean_allocated_bytes"] is None else f'{row["mean_allocated_bytes"]:.1f}'
            print(f'{row["phase"]} {row["allocation_scope"]} {row["samples"]} '
                  f'{row["mean_duration_us"]:.1f} {row["max_duration_us"]} {allocation} '
                  f'{row["max_allocated_bytes"]} {dict(row["outcomes"])}')
        for summary in report["summaries"]:
            print(f'samples: attempts={summary["attempts"]} recorded={summary["recorded"]} '
                  f'dropped={summary["dropped"]} incomplete={summary.get("incomplete", 0)} every={summary["sample_every"]}')
        for row in report.get("comparisons", []):
            print(f'comparison {row["phase"]} {row["allocation_scope"]}: '
                  f'mean-allocated delta={row["mean_allocated_bytes_delta"]}, '
                  f'mean-us delta={row["mean_duration_us_delta"]:.1f}, samples={row["samples"]}')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
