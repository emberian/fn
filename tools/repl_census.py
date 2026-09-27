#!/usr/bin/env python3
"""Every failing form of one book, in one REPL session, in seconds.

    python3 tools/repl_census.py tests/acl2/acceptance-tests [--name S] [--tail N]

`proof_repl.py start` stops at the first form ACL2 refuses; a test book red
after an interface change usually has one fixture failure that cascades and
several independent ones, and learning them one farm run (or one restart) at
a time is the slow loop.  This starts a session over BOOK (its certified
dependencies from the cache, as `start` does), then sends every form after
the first refused one, continuing past failures, and prints each failing
form's line, head and the tail of what ACL2 said.  It ends the session.

Runs where proof_repl runs (persvati or hbox, never ACL2 on the laptop);
each form is capped at 120 s like any `send`.  Exit 0 when the book loads
clean, 1 when a form failed, 2 when the session could not start.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import proof_repl as pr  # noqa: E402

MARKS = ("ACL2 Error", "HARD ACL2", "Assertion failed", "ACL2 Halted")


def repl(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(Path(__file__).with_name("proof_repl.py")), *args],
                          capture_output=True, text=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("book", help="books/NAME or tests/acl2/NAME, no .lisp")
    ap.add_argument("--name", default=None, help="session name (default census-BASENAME)")
    ap.add_argument("--tail", type=int, default=900, help="characters of ACL2 output per failure")
    a = ap.parse_args()
    name = a.name or "census-" + Path(a.book).name
    repl("stop", name)
    started = repl("start", name, a.book, "--limit", "120")
    state_path = pr.session_dir(name) / "state.json"
    if not state_path.exists():
        print(started.stdout[-1500:] + started.stderr[-1500:])
        return 2
    state = json.loads(state_path.read_text())
    text = (pr.ROOT / f"{a.book}.lisp").read_text(encoding="utf-8")
    spans = pr.spans(text)
    n = len(state["loaded"])
    print(f"START loaded {n} of {len(spans)}; stopped_at {state['stopped_at']}")
    if not state["ready"]:
        print(started.stdout[-1500:] + started.stderr[-1500:])
        return 2
    failures = 0
    try:
        if state["stopped_at"] is None:
            print("ALL GREEN")
            return 0
        failures = 1
        print(f"FAIL #{n} line {text[:spans[n][0]].count(chr(10)) + 1} "
              f"{text[spans[n][0]:spans[n][1]].strip().splitlines()[0][:100]}")
        print("   " + str(state["error"])[-a.tail:].replace("\n", "\n   "))
        for i in range(n + 1, len(spans)):
            form = text[spans[i][0]:spans[i][1]]
            if form.lstrip().startswith("(in-package"):
                continue
            r = repl("send", name, form, "--limit", "120")
            out = r.stdout + r.stderr
            if any(m in out for m in MARKS):
                failures += 1
                print(f"FAIL #{i} line {text[:spans[i][0]].count(chr(10)) + 1} "
                      f"{form.strip().splitlines()[0][:100]}", flush=True)
                print("   " + out[-a.tail:].replace("\n", "\n   "))
        print(f"DONE failures={failures}")
        return 1
    finally:
        repl("stop", name)


if __name__ == "__main__":
    sys.exit(main())
