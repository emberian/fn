#!/usr/bin/env python3
"""Run every step of `make check`, then say which failed.

`make` stops a recipe at its first failing line, so one sibling's red step
(a stale harness arity, a generated file behind) hid every check after it:
flip-bridge, flip-tests-green and readme each lost a round to that on
2026-09-27.  Each line of the `check` recipe now runs through this wrapper,
which prints the step, runs it with its output passing straight through,
records its exit status, its time and its first finding, and exits 0 so the
next step runs.  The recipe's last line prints the table and exits 1 when any
step failed:

    python3 tools/check_steps.py begin build/check-steps
    python3 tools/check_steps.py run build/check-steps -- python3 tools/x.py --strict
    python3 tools/check_steps.py summary build/check-steps

An interrupt (Ctrl-C) still stops the whole check.  The first finding is a
reading aid picked from the step's output; the verdict is the exit status.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time

RESULTS = "results.jsonl"
# A line that names a finding, strongest first: a nonzero finding count, a
# named failure; then anything that reads like trouble.
STRONG = re.compile(r"\b[1-9]\d* (?:findings?|failures?|errors?)\b|\bUNDEFINED\b|\bNEW\b|"
                    r"(?i:\bfail(?:ed|ure|s)?\b|\berror\b|traceback|refused|mismatch|"
                    r"called with)")
FINDING = re.compile(r"(?i)\b(fail\w*|error|refus\w*|stale|missing|mismatch|violat\w*|"
                     r"traceback|not (?:found|generated|current|green))\b")


def step_name(command: list[str]) -> str:
    """`tools/cite_check.py --summary` -> `cite_check`; `-m unittest -q X` -> `X`."""
    words = [word for word in command[1:] if not word.startswith("-")] or command
    if "-m" in command:
        after = command[command.index("-m") + 1:]
        names = [word for word in after if not word.startswith("-")]
        return names[-1] if names else "python -m"
    first = Path(words[0]).name
    return first[:-3] if first.endswith(".py") else first


def first_finding(lines: list[str]) -> str:
    """The first line that reads like a finding, else the last line printed."""
    printed = [line.strip() for line in lines if line.strip()]
    for pattern in (STRONG, FINDING):
        for line in printed:
            if pattern.search(line):
                return line[:160]
    return printed[-1][:160] if printed else ""


def begin(directory: Path) -> int:
    shutil.rmtree(directory, ignore_errors=True)
    directory.mkdir(parents=True, exist_ok=True)
    return 0


def run(directory: Path, command: list[str]) -> int:
    directory.mkdir(parents=True, exist_ok=True)
    name = step_name(command)
    print(f"== {name}: {shlex.join(command)}", flush=True)
    started = time.monotonic()
    captured: list[str] = []
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, bufsize=1, errors="replace")
    except OSError as error:
        code, captured = 127, [f"cannot run: {error}"]
        print(captured[0])
    else:
        assert process.stdout is not None
        try:
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                captured.append(line)
            code = process.wait()
        except KeyboardInterrupt:
            process.kill()
            process.wait()
            raise
    record = {"step": name, "command": shlex.join(command), "exit": code,
              "seconds": round(time.monotonic() - started, 1),
              "finding": first_finding(captured) if code else ""}
    with open(directory / RESULTS, "a", encoding="utf-8") as results:
        results.write(json.dumps(record) + "\n")
    if code < 0 and -code == 2:  # the step itself was interrupted
        raise KeyboardInterrupt
    return 0


def read_results(directory: Path) -> list[dict]:
    try:
        text = (directory / RESULTS).read_text(encoding="utf-8")
    except OSError:
        return []
    return [json.loads(line) for line in text.splitlines() if line.strip()]


def summary(directory: Path) -> int:
    rows = read_results(directory)
    if not rows:
        print(f"check: no step recorded under {directory}")
        return 1
    width = max(len(row["step"]) for row in rows)
    failed = [row for row in rows if row["exit"] != 0]
    print(f"\n== check: {len(rows)} steps, {len(failed)} failed")
    for row in rows:
        verdict = "ok" if row["exit"] == 0 else f"exit {row['exit']}"
        line = f"  {row['step']:{width}}  {verdict:8} {row['seconds']:7.1f} s"
        if row["exit"] != 0 and row["finding"]:
            line += f"  {row['finding']}"
        print(line)
    return 1 if failed else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="action", required=True)
    for action in ("begin", "summary"):
        p = sub.add_parser(action)
        p.add_argument("directory")
    p = sub.add_parser("run", help="one step: DIRECTORY -- COMMAND ...")
    p.add_argument("directory")
    p.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    directory = Path(args.directory)
    if args.action == "begin":
        return begin(directory)
    if args.action == "summary":
        return summary(directory)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("run needs a command after --")
    try:
        return run(directory, command)
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    os.environ.setdefault("PYTHONUNBUFFERED", "1")
    raise SystemExit(main())
