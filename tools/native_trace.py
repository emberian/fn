#!/usr/bin/env python3
"""Rank native FN_TRACE spans and compare matched log observations.

Process allocation samples include other threads and nested spans. Never
interpret their sum as unique allocation, peak residency, retained heap or
GC volume. An isolated-process tag is the probe caller's assertion.

Decision rows (`{"v":2,"type":"decision",...}`, host/native/trace.lisp, one per
traced `fnn-call` return; books/decision-trace.lisp) are read here too, and
nowhere else: this is the one parser.  A decision row is a view over a decision
ACL2 already made: its `inputs` and `outcome` are ACL2's bounded records (a
natural, a lowercase word, or a list of those).  The `decision-summary` line
that ends every drain carries the counters, and `attempts = recorded + dropped
+ sampled_out` in every one (DT-5).
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

PREFIX = "FN_TRACE "
DECISION_CLASSES = ("verdict", "refusal", "tariff", "schedule", "plan")


def _record(value, where):
    """A bounded record: a natural, a word, or a list of those, two deep."""
    def atom(x):
        return (isinstance(x, int) and not isinstance(x, bool) and 0 <= x < 1 << 64) or isinstance(x, str)
    if atom(value):
        return value
    if isinstance(value, list) and len(value) <= 8:
        for item in value:
            if not atom(item) and not (isinstance(item, list) and len(item) <= 8 and all(atom(y) for y in item)):
                break
        else:
            return value
    raise ValueError(f"{where} is not a bounded record")


def decision_row(event: dict) -> dict:
    """Validate one `type: decision` line; the row, unchanged."""
    if event.get("v") != 2:
        raise ValueError("unsupported decision schema version")
    if not isinstance(event.get("seq"), int) or event["seq"] < 1:
        raise ValueError("decision seq must be a positive integer")
    if event.get("class") not in DECISION_CLASSES:
        raise ValueError("unknown decision class")
    if not isinstance(event.get("point"), str) or not event["point"]:
        raise ValueError("decision point must be a name")
    for key in ("start_us", "duration_us"):
        if not isinstance(event.get(key), int) or event[key] < 0:
            raise ValueError(f"decision {key} must be a natural")
    for key in ("operation", "connection_generation"):
        if event.get(key) is not None and not isinstance(event[key], int):
            raise ValueError(f"decision {key} must be a natural or null")
    if not isinstance(event.get("inputs"), list):
        raise ValueError("decision inputs must be a list")
    _record(event["inputs"], "decision inputs")
    _record(event.get("outcome"), "decision outcome")
    return event


def decision_summary(event: dict) -> dict:
    keys = ("attempts", "recorded", "dropped", "sampled_out", "live", "next")
    if any(not isinstance(event.get(k), int) or event[k] < 0 for k in keys):
        raise ValueError("decision summary counters must be naturals")
    if event["attempts"] != event["recorded"] + event["dropped"] + event["sampled_out"]:
        raise ValueError("decision counters do not balance: attempts != recorded + dropped + sampled_out")
    return event


def decisions_from_text(text: str):
    """(rows, summaries) of the decision lines in TEXT; any other line is skipped."""
    rows, summaries = [], []
    for number, line in enumerate(text.splitlines(), 1):
        if not line.startswith(PREFIX):
            continue
        try:
            event = json.loads(line[len(PREFIX):])
            kind = event.get("type")
            if kind == "decision":
                rows.append(decision_row(event))
            elif kind == "decision-summary":
                summaries.append(decision_summary(event))
        except (ValueError, TypeError, AttributeError) as error:
            raise ValueError(f"line {number}: invalid FN_TRACE decision record: {error}") from error
    return rows, summaries


def analyze(path: Path) -> dict:
    groups = {}
    summaries = []
    decision_groups = {}
    decision_summaries = []
    with path.open(encoding="utf-8", errors="replace") as stream:
        for number, line in enumerate(stream, 1):
            if not line.startswith(PREFIX):
                continue
            try:
                event = json.loads(line[len(PREFIX):])
                if event["type"] == "summary":
                    summaries.append(event)
                    continue
                if event["type"] == "decision":
                    decision_row(event)
                    key = (event["point"], event["class"])
                    group = decision_groups.setdefault(key, dict(
                        point=key[0], **{"class": key[1]}, calls=0, duration_us=0, outcomes=Counter()))
                    group["calls"] += 1
                    group["duration_us"] += event["duration_us"]
                    group["outcomes"][json.dumps(event["outcome"])] += 1
                    continue
                if event["type"] == "decision-summary":
                    decision_summaries.append(decision_summary(event))
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
    decisions = sorted(decision_groups.values(), key=lambda g: (g["point"], g["class"]))
    for group in decisions:
        group["mean_duration_us"] = group["duration_us"] / group["calls"]
    return dict(log=str(path), phases=rows, summaries=summaries,
                decisions=decisions, decision_summaries=decision_summaries,
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
        for group in report["decisions"]:
            print(f'decision {group["point"]} {group["class"]} calls={group["calls"]} '
                  f'mean-us={group["mean_duration_us"]:.1f} outcomes={dict(group["outcomes"])}')
        for summary in report["decision_summaries"]:
            print(f'decisions: attempts={summary["attempts"]} recorded={summary["recorded"]} '
                  f'dropped={summary["dropped"]} sampled-out={summary["sampled_out"]}')
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
