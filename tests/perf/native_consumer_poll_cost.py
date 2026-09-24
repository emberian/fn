"""Temporary real-owner poll timing fixture; no cursor/event byte synthesis.

Run with FN_NATIVE_DEVELOPER_HOST pointing to a source-matched image.
The frozen image and this exact script must be recorded with the result.
"""

import json
import os
from pathlib import Path
import statistics
import sys
import time

ROOT = Path.cwd()
if not (ROOT / "tests" / "test_native_consumer_e2.py").is_file():
    raise SystemExit("run from the fn repository root")
sys.path.insert(0, str(ROOT))

from tests.test_native_consumer_e2 import NativeConsumerE2Tests


def main():
    image = Path(os.environ["FN_NATIVE_DEVELOPER_HOST"])
    if not image.is_file():
        raise SystemExit("missing native image")
    case = NativeConsumerE2Tests("test_durable_scope_ack_and_unrelated_article")
    case.setUp()
    try:
        node = case.node("indexed-cost")
        owner = case.start_owner(node)
        case.bootstrap(node)
        case.register(node, "low", node["base"] / "low-initial.fncu")
        case.register(node, "high", node["base"] / "high-initial.fncu")

        # ACL2-owned neutral Store events; the helper never constructs a
        # cursor or decides which journal positions they consume.
        for i in range(144):
            case.register(node, f"temporary-{i:03d}",
                          node["base"] / f"temp-{i}.fncu")

        for i in range(8):
            cursor = node["base"] / f"advance-{i}.fncu"
            report = node["base"] / f"advance-{i}.event"
            case.consumer("poll", node, "high", cursor, report)
            if report.read_bytes() != b"":
                raise AssertionError("neutral-only poll returned article")
            case.consumer("ack", node, cursor)

        low_before = case.status(node, "low")
        high_before = case.status(node, "high")
        if low_before[0] != 0 or high_before[0] < 128:
            raise AssertionError((low_before, high_before))
        if high_before[2] < 16:
            raise AssertionError("insufficient journal tail for full high window")

        samples = {"low": [], "high": []}
        for i in range(20):
            for label in ("low", "high") if i % 2 == 0 else ("high", "low"):
                cursor = node["base"] / f"measure-{label}-{i}.fncu"
                report = node["base"] / f"measure-{label}-{i}.event"
                started = time.perf_counter_ns()
                case.consumer("poll", node, label, cursor, report)
                elapsed = time.perf_counter_ns() - started
                if report.read_bytes() != b"" or not cursor.read_bytes().startswith(b"fncu\x01"):
                    raise AssertionError("unexpected measured poll result")
                samples[label].append(elapsed / 1e6)

        low_after = case.status(node, "low")
        high_after = case.status(node, "high")
        if low_after != low_before or high_after != high_before:
            raise AssertionError("poll mutated durable consumer progress")
        case.stop_owner(owner)
        print(json.dumps({
            "image": str(image),
            "low_status": low_before,
            "high_status": high_before,
            "iterations_per_position": 20,
            "low_ms": samples["low"],
            "high_ms": samples["high"],
            "median_low_ms": statistics.median(samples["low"]),
            "median_high_ms": statistics.median(samples["high"]),
            "max_low_ms": max(samples["low"]),
            "max_high_ms": max(samples["high"]),
        }, sort_keys=True))
    finally:
        case.doCleanups()


if __name__ == "__main__":
    sys.exit(main())
