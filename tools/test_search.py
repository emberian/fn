#!/usr/bin/env python3
"""Run one ACL2 `test?` counterexample search and say what it actually did.

`test?` prints "Test? succeeded. No counterexamples were found." when it never
tested anything: for a conjecture over a function that takes a stobj (or a
constrained function without an attachment) Cgen skips testing completely and
says so only in its verbose output (P6 on hbox, 2026-10-11: fn-ptx-step and
the rest).  It also reports "proved" for a conjecture whose hypotheses no
generated example satisfied.  Most of fn's keystones are over stobjs, so the
final "Test?" line is not evidence of a search (COUNTEREXAMPLE rule 6.6).

This runs `test?` at verbosity level 3, reads Cgen's own summary, and prints
exactly one line:

    SEARCHED <m> examples 0 counterexamples (<n> tested, <u> unique)   exit 0
    COUNTEREXAMPLE <first binding>                                     exit 1
    SKIPPED <reason>                                                   exit 2

It never prints SEARCHED unless Cgen's summary says at least one example
satisfied the hypotheses and none falsified the conclusion.  The full verbose
transcript is written to --log (default: a fresh file under
build/test-search/) and its path goes to stderr.

    python3 tools/test_search.py --book books/heap-figure \\
        '(implies (natp x) (<= 0 (fnn-figure x)))'

ACL2 is `$FN_ACL2`, defaulting on a farm box to that box's launcher
(`acl2_slots.apply_box_defaults`), and runs under the tree's slot pool with the
certification environment.  acl2s/cgen must be certified for that launcher
(hbox: planning/hbox-acl2s-cgen-2026-10-11.md).
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import acl2_slots  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
BEGIN = "FN-TEST-SEARCH-BEGIN"
END = "FN-TEST-SEARCH-END"

SEARCHED, COUNTEREXAMPLE, SKIPPED = 0, 1, 2

SUMMARY = re.compile(
    r"We tested (\d+) examples? across (\d+) subgoals?, of which (\d+) "
    r"\((\d+) unique\) satisfied the hypotheses, and found (\d+) "
    r"counterexamples? and (\d+) witness")
SKIP_NOTE = re.compile(r"Skipping testing[^.]*\.")
ERROR = re.compile(r"(HARD ACL2 ERROR|ACL2 Error)[^\n]*")


def driver(statement: str, books: list[str], setup: str) -> str:
    """The ACL2 input: cgen, the books, the setup events, then one test?."""
    lines = ['(include-book "acl2s/cgen/top" :dir :system :ttags :all)']
    for book in books:
        path = Path(book)
        if not path.is_absolute():
            path = ROOT / path
        name = str(path)
        if name.endswith(".lisp"):
            name = name[: -len(".lisp")]
        lines.append(f'(include-book "{name}" :ttags :all)')
    if setup:
        lines.append(setup)
    lines += [
        "(acl2s-defaults :set testing-enabled t)",
        "(acl2s-defaults :set verbosity-level 3)",
        f'(cw "~%{BEGIN}~%")',
        f"(test? {statement})",
        f'(cw "~%{END}~%")',
        "(good-bye)",
    ]
    return "\n".join(lines) + "\n"


def flat(text: str) -> str:
    return " ".join(text.split())


def first_binding(text: str) -> str | None:
    """The first ` -- (...)` form after Cgen's counterexample header, read to
    its balancing parenthesis."""
    marker = text.find("-- (")
    if marker < 0:
        return None
    start = marker + len("-- ")
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return text[start:index + 1]
    return None


def classify(transcript: str) -> tuple[int, str]:
    """One verdict from a verbose transcript; never SEARCHED without a summary
    showing satisfied hypotheses and zero counterexamples."""
    start = transcript.find(BEGIN)
    if start < 0:
        error = ERROR.search(transcript)
        detail = f": {flat(error.group(0))}" if error else ""
        return SKIPPED, f"setup did not reach test?{detail}"
    preamble = transcript[:start]
    error = ERROR.search(preamble)
    if error:
        return SKIPPED, f"setup failed before test?: {flat(error.group(0))}"
    body = transcript[start + len(BEGIN):]
    finish = body.find(END)
    if finish < 0:
        return SKIPPED, "test? did not complete (no end marker)"
    body = body[:finish]
    text = flat(body)

    falsified = "Test? found a counterexample" in text
    summary = SUMMARY.search(text)
    if falsified or (summary and int(summary.group(5)) > 0):
        after = text.split("Here are counterexamples:", 1)
        binding = first_binding(after[1]) if len(after) > 1 else None
        return COUNTEREXAMPLE, binding or "(binding not printed)"
    skip = SKIP_NOTE.search(text)
    if skip:
        return SKIPPED, skip.group(0)
    if summary is None:
        error = ERROR.search(body)
        if error:
            return SKIPPED, f"test? failed: {flat(error.group(0))}"
        said = re.search(r"Test\? [^.]*\.", text)
        return SKIPPED, ("no Cgen/testing summary"
                         + (f" (test? said: {said.group(0)})" if said else ""))
    tested, _subgoals, satisfied, unique = (int(summary.group(i)) for i in (1, 2, 3, 4))
    if satisfied == 0:
        return SKIPPED, f"0 of {tested} tested examples satisfied the hypotheses"
    return SEARCHED, (f"{satisfied} examples 0 counterexamples "
                      f"({tested} tested, {unique} unique)")


VERDICT = {SEARCHED: "SEARCHED", COUNTEREXAMPLE: "COUNTEREXAMPLE", SKIPPED: "SKIPPED"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("statement", help="the conjecture, one ACL2 term")
    parser.add_argument("--book", action="append", default=[],
                        help="a book to include first, relative to the tree root "
                             "(repeatable)")
    parser.add_argument("--setup", type=Path, default=None,
                        help="a file of ACL2 events to run after the books")
    parser.add_argument("--timeout", type=float, default=900.0, metavar="SECONDS")
    parser.add_argument("--log", type=Path, default=None,
                        help="where to keep the verbose transcript")
    arguments = parser.parse_args(argv)

    acl2_slots.apply_box_defaults()
    acl2 = acl2_slots.configured_acl2()
    setup = arguments.setup.read_text(encoding="utf-8") if arguments.setup else ""
    text = driver(arguments.statement, arguments.book, setup)
    log = arguments.log
    if log is None:
        directory = ROOT / "build" / "test-search"
        directory.mkdir(parents=True, exist_ok=True)
        handle, name = tempfile.mkstemp(prefix="test-search-", suffix=".log",
                                        dir=directory)
        os.close(handle)
        log = Path(name)
    try:
        completed = acl2_slots.run([acl2], "test-search", input=text, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   timeout=arguments.timeout)
        transcript = completed.stdout
        verdict, detail = classify(transcript)
    except subprocess.TimeoutExpired as expired:
        transcript = expired.stdout or ""
        if isinstance(transcript, bytes):
            transcript = transcript.decode("utf-8", "replace")
        verdict, detail = SKIPPED, f"timed out after {arguments.timeout:g}s"
    except OSError as error:
        transcript = ""
        verdict, detail = SKIPPED, f"could not run ACL2 at {acl2!r}: {error}"
    log.write_text(text + "\n;; ---- transcript ----\n" + transcript, encoding="utf-8")
    print(f"test_search: transcript {log}", file=sys.stderr)
    print(f"{VERDICT[verdict]} {detail}")
    return verdict


if __name__ == "__main__":
    sys.exit(main())
