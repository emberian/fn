#!/usr/bin/env python3
"""Rank native FN_TRACE spans and compare matched log observations.

Process allocation samples include other threads and nested spans. Never
interpret their sum as unique allocation, peak residency, retained heap or
GC volume. An isolated-process tag is the probe caller's assertion.

Span rows with `"v":2` carry the per-request cost columns (cpu_us, gc_us,
gc_count, read_octets, write_octets, syscalls, rss_kib), each with its scope;
`requests` rolls the top-level spans of one (connection, operation) up.

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


COST_COLUMNS = ("cpu_us", "gc_us", "gc_count", "read_octets", "write_octets", "syscalls")
COST_SCOPES = dict(cpu_scope=("thread", "process"), gc_scope=("process",),
                   io_scope=("thread",), rss_scope=("process",))


def span_cost(event: dict) -> dict | None:
    """The v2 per-request cost columns of one span row (host/native/trace.lisp,
    program section 2b), validated; None for a row without `v`.  Each column's
    scope is part of the row: cpu_us is thread scope where the host can say so,
    gc_us and gc_count are process-wide, the octet and syscall counters are the
    serving thread's, rss_kib is the process (NULL when not sampled)."""
    if "v" not in event:
        return None
    if event["v"] != 2:
        raise ValueError("invalid span measurement: unsupported span schema version")
    for key in COST_COLUMNS:
        value = event.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(f"invalid span measurement: {key}")
    for key, allowed in COST_SCOPES.items():
        if event.get(key) not in allowed:
            raise ValueError(f"invalid span measurement: {key}")
    rss = event.get("rss_kib")
    if rss is not None and (not isinstance(rss, int) or isinstance(rss, bool) or rss < 0):
        raise ValueError("invalid span measurement: rss_kib")
    return {key: event[key] for key in COST_COLUMNS} | dict(rss_kib=rss)


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
    requests = {}
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
                cost = span_cost(event)
                row = groups.setdefault(key, dict(phase=key[0], allocation_scope=key[1],
                    samples=0, duration_us_inclusive=0, max_duration_us=0,
                    allocation_samples=0, allocated_bytes_inclusive=0, max_allocated_bytes=0,
                    outcomes=Counter(), **{c + "_inclusive": 0 for c in COST_COLUMNS},
                    cost_samples=0, max_rss_kib=None, cpu_scope=None))
                row["samples"] += 1
                row["duration_us_inclusive"] += duration
                row["max_duration_us"] = max(row["max_duration_us"], duration)
                row["outcomes"][event["outcome"]] += 1
                if cost:
                    row["cost_samples"] += 1
                    row["cpu_scope"] = event["cpu_scope"]
                    for c in COST_COLUMNS:
                        row[c + "_inclusive"] += cost[c]
                    if cost["rss_kib"] is not None:
                        row["max_rss_kib"] = max(row["max_rss_kib"] or 0, cost["rss_kib"])
                    # One request is every top-level span of one (connection,
                    # operation) pair: the mux reads, steps, renders and writes
                    # a command in separate event-loop turns, each its own span.
                    if event.get("parent_id") is None and event.get("operation_id") is not None:
                        request = requests.setdefault(
                            (event.get("connection_id"), event["operation_id"]),
                            dict(connection_id=event.get("connection_id"),
                                 operation_id=event["operation_id"], spans=0, duration_us=0,
                                 phases=[], **{c: 0 for c in COST_COLUMNS}))
                        request["spans"] += 1
                        request["duration_us"] += duration
                        request["phases"].append(event["phase"])
                        for c in COST_COLUMNS:
                            request[c] += cost[c]
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
                requests=sorted(requests.values(), key=lambda r: (r["connection_id"] or 0, r["operation_id"])),
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
        for row in report["requests"]:
            print(f'request conn={row["connection_id"]} op={row["operation_id"]} spans={row["spans"]} '
                  f'us={row["duration_us"]} cpu-us={row["cpu_us"]} gc-us={row["gc_us"]} gc={row["gc_count"]} '
                  f'read={row["read_octets"]} write={row["write_octets"]} syscalls={row["syscalls"]}')
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
