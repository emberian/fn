#!/usr/bin/env python3
"""Read completed certify records using the certifier's actual verdict rule.

Run on the build host. Read-only: never runs ACL2, changes the candidate or stops its build. A process
exit is not certification. Plain completed books can be reported before the
final manifest; unfinished/multi-wave records remain pending.
"""
from __future__ import annotations

import argparse
import hashlib
import inspect
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import certify_books


def snapshot(tree, run):
    passed, failed, pending = [], [], []
    rows = []
    for path in run.glob("*.active.json"):
        try:
            row = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            pending.append(dict(record=path.name, reason="record not readable yet"))
            continue
        rows.append(row)
    for row in sorted(rows, key=lambda r: (r.get("started_monotonic", 0)
                                         + r.get("elapsed_seconds", 0), r["book"])):
        book = row["book"]
        # The certifier's multi-wave collector owns its combined output.
        if row.get("status") != "exited" or row.get("wave") is not None:
            pending.append(dict(book=book, reason="unfinished or multi-wave"))
            continue
        if time.monotonic() < row["started_monotonic"] + row["elapsed_seconds"] + 1:
            pending.append(dict(book=book, reason="allow final log write"))
            continue
        driver = run / (book.replace("/", "--") + ".certify.lsp")
        try:
            source = driver.read_text()
            output = (run / row["log"]).read_text(errors="replace")
        except OSError:
            pending.append(dict(book=book, reason="driver/log unavailable"))
            continue
        marker = re.search(re.escape(certify_books.SUCCESS_PREFIX) + r"([a-zA-Z0-9_-]+) ", source)
        if marker is None:
            pending.append(dict(book=book, reason="fresh driver nonce unavailable"))
            continue
        verdict, reasons = certify_books.book_result(
            book, output, row["exit_code"], marker.group(1),
            (tree / (book + ".cert")).is_file())
        if verdict == "passed":
            passed.append(book)
        else:
            failed.append(dict(book=book, reasons=reasons, log=row["log"],
                               process_exit=row["exit_code"], started_utc=row["started_utc"]))
    return dict(passed=len(passed), failed=failed, pending=pending,
                verdict_rule="tools.certify_books.book_result",
                verdict_rule_sha256=hashlib.sha256(inspect.getsource(
                    certify_books.book_result).encode()).hexdigest(),
                scope="completed plain records only; not a complete-run certification manifest")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tree", type=Path, required=True)
    parser.add_argument("--run", type=Path, required=True)
    args = parser.parse_args()
    result = snapshot(args.tree.resolve(), args.run.resolve())
    print(json.dumps(result, indent=2))
    return 1 if result["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
