#!/usr/bin/env python3
"""Merge the peak memory native modules recorded into tests/native_peaks.json.

    python3 tools/native_peaks.py LOGDIR [LOGDIR ...] [--table tests/native_peaks.json]

Each LOGDIR is a hbox_native run's logs/ directory.  A module's log carries
the one FN_TEST_BUDGET_RESULT line tools/test_budget.py --one prints, with
"peak_mib" (its scope's memory.peak).  The table keeps the largest peak seen
per module; tools/test_budget.py derives a module's MemoryMax from it
(PEAK_FACTOR times, at least 4G) when the module declares none.
"""
import json
from pathlib import Path
import sys

PREFIX = "FN_TEST_BUDGET_RESULT "


def peaks(logdir: Path) -> dict[str, float]:
    found: dict[str, float] = {}
    for log in sorted(logdir.glob("test-*.log")):
        for line in log.read_text(errors="replace").splitlines():
            if line.startswith(PREFIX):
                try:
                    record = json.loads(line[len(PREFIX):])
                except ValueError:
                    continue
                if "peak_mib" in record and record.get("module"):
                    found[record["module"]] = max(found.get(record["module"], 0.0),
                                                  float(record["peak_mib"]))
    return found


def main(argv: list[str]) -> int:
    table = Path(__file__).resolve().parent.parent / "tests" / "native_peaks.json"
    args = list(argv)
    if "--table" in args:
        i = args.index("--table")
        table = Path(args[i + 1])
        del args[i:i + 2]
    merged = json.loads(table.read_text()) if table.is_file() else {}
    for logdir in args:
        for module, peak in peaks(Path(logdir)).items():
            merged[module] = max(merged.get(module, 0.0), peak)
    table.write_text(json.dumps(dict(sorted(merged.items())), indent=1) + "\n")
    print(f"native_peaks: {len(merged)} modules in {table}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
