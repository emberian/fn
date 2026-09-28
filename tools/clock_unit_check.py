#!/usr/bin/env python3
"""tools/clock_unit_check.py -- clock arithmetic goes through books/clock-unit.lisp.

A clock observation (books/clock.lisp) is unit-less by shape.  Two bugs came
from arithmetic on its fields at a call site that assumed a unit the reading
did not have: bug M1 (PRF-374: a stopped node's invitation expiry added
milliseconds to a seconds stamp, so every code was born expired) and PRF-378
(fn-cfg-account-livep compared a seconds stamp with a millisecond expiry,
so a configuration record's :account-expired never fired).  books/clock-unit
names a reading's unit (fn-clock-reading) and does the conversion once
(fn-clock-reading-latest-milliseconds, fn-clock-seconds-in-milliseconds).

WHAT IT FLAGS.  A form whose operator is arithmetic or an order comparison
(+ - * / floor ceiling truncate round mod rem min max < <= > >= =) with a
direct argument that is a field of an observation -- (fn-clock-wall X),
(fn-clock-wall-error X), (fn-clock-monotonic X), optionally under nfix or
ifix -- in any book or host file except books/clock.lisp and
books/clock-unit.lisp.  Source-level, no ACL2; comments, strings and
theorem statements (defthm, defthmd, thm, assert-event) are skipped.  A site that only moves a field (passes it to a function, stores
it) is not arithmetic and is not flagged.

THE BASELINE, tools/clock_unit_baseline.json, holds the count of such sites
per file today.  It only shrinks: a file over its count, or a file not in
the baseline with a site, fails; a file UNDER its count also fails until the
baseline is lowered (`--write-baseline', which refuses to raise any count).
Route a site through clock-unit (a tagged reading and its millisecond
upper end) and lower the count.

    python3 tools/clock_unit_check.py                  # the lint (make check)
    python3 tools/clock_unit_check.py --list           # every site
    python3 tools/clock_unit_check.py --write-baseline # after a site is routed
"""
import argparse
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINE = os.path.join(ROOT, "tools", "clock_unit_baseline.json")
EXEMPT = {"books/clock.lisp", "books/clock-unit.lisp"}
ARITH = {"+", "-", "*", "/", "floor", "ceiling", "truncate", "round", "mod",
         "rem", "min", "max", "<", "<=", ">", ">=", "="}
FIELDS = {"fn-clock-wall", "fn-clock-wall-error", "fn-clock-monotonic"}
WRAPPERS = {"nfix", "ifix"}


def tokens(text):
    """Yield (token, line) for parens and atoms; skip comments, strings,
    block comments and character literals."""
    i, n, line = 0, len(text), 1
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
        elif c in " \t\r\f":
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("#|", i):
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("|#", i):
                    depth -= 1
                    i += 2
                elif text.startswith("#|", i):
                    depth += 1
                    i += 2
                else:
                    if text[i] == "\n":
                        line += 1
                    i += 1
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                elif text[i] == "\n":
                    line += 1
                i += 1
            i += 1
            yield ("<string>", line)
        elif text.startswith("#\\", i):
            i += 3
            while i < n and text[i] not in " \t\r\n()":
                i += 1
            yield ("<char>", line)
        elif c in "()":
            yield (c, line)
            i += 1
        elif c in "'`,":
            i += 1
            if i < n and text[i] == "@":
                i += 1
        else:
            j = i
            while j < n and text[j] not in " \t\r\n()\";":
                j += 1
            yield (text[i:j].lower(), line)
            i = j


def forms(text):
    """Parse into nested lists of (atom, line) leaves; lists carry their
    opening line as ('(', line, [children])."""
    stack = [("(", 0, [])]
    for tok, line in tokens(text):
        if tok == "(":
            stack.append(("(", line, []))
        elif tok == ")":
            if len(stack) > 1:
                done = stack.pop()
                stack[-1][2].append(done)
        else:
            stack[-1][2].append((tok, line))
    while len(stack) > 1:
        done = stack.pop()
        stack[-1][2].append(done)
    return stack[0][2]


def head(node):
    if isinstance(node, tuple) and len(node) == 3 and node[0] == "(" and node[2]:
        first = node[2][0]
        if len(first) == 2:
            return first[0]
    return None


def is_field(node):
    h = head(node)
    if h in FIELDS:
        return True
    if h in WRAPPERS and len(node[2]) == 2:
        return head(node[2][1]) in FIELDS
    return False


# A theorem states arithmetic about a reading; it computes nothing.
STATEMENTS = {"defthm", "defthmd", "thm", "defrule", "assert-event"}


def sites_in(nodes, out):
    for node in nodes:
        if len(node) != 3:
            continue
        h = head(node)
        if h in STATEMENTS:
            continue
        if h in ARITH and any(is_field(arg) for arg in node[2][1:]):
            out.append((node[1], h))
        sites_in(node[2], out)


def scan(root=ROOT):
    found = {}
    for top in ("books", "host"):
        base = os.path.join(root, top)
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
            for name in sorted(filenames):
                if not name.endswith(".lisp"):
                    continue
                path = os.path.join(dirpath, name)
                rel = os.path.relpath(path, root)
                if rel in EXEMPT:
                    continue
                with open(path, encoding="utf-8", errors="replace") as f:
                    text = f.read()
                if "fn-clock-" not in text:
                    continue
                out = []
                sites_in(forms(text), out)
                if out:
                    found[rel] = out
    return found


def load_baseline(path=BASELINE):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f).get("sites", {})
    except FileNotFoundError:
        return {}


def judge(found, baseline):
    problems = []
    for rel in sorted(set(found) | set(baseline)):
        have = len(found.get(rel, []))
        allowed = baseline.get(rel, 0)
        if have > allowed:
            lines = ", ".join("{}:{} ({})".format(rel, l, op) for l, op in found[rel])
            problems.append("{}: {} raw clock arithmetic site(s), baseline {}: {}".format(
                rel, have, allowed, lines))
        elif have < allowed:
            problems.append("{}: {} site(s), baseline {}: lower it "
                            "(tools/clock_unit_check.py --write-baseline)".format(
                                rel, have, allowed))
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--write-baseline", action="store_true")
    ap.add_argument("--root", default=ROOT)
    args = ap.parse_args(argv)
    found = scan(args.root)
    baseline_path = os.path.join(args.root, "tools", "clock_unit_baseline.json")
    baseline = load_baseline(baseline_path)
    if args.list:
        for rel in sorted(found):
            for line, op in found[rel]:
                print("{}:{}: ({} ... fn-clock-...)".format(rel, line, op))
    if args.write_baseline:
        grown = [rel for rel in found
                 if len(found[rel]) > baseline.get(rel, 0) and baseline]
        if grown:
            print("clock_unit_check: refused: the baseline only shrinks; grown: "
                  + ", ".join(sorted(grown)), file=sys.stderr)
            return 1
        doc = ("tools/clock_unit_check.py: raw arithmetic on a clock observation's "
               "fields outside books/clock-unit.lisp, counted per file (PRF-378). "
               "Only shrinks: route a site through fn-clock-reading and lower its count.")
        with open(baseline_path, "w", encoding="utf-8") as f:
            json.dump({"_doc": doc,
                       "sites": {rel: len(found[rel]) for rel in sorted(found)}},
                      f, indent=1, sort_keys=False)
            f.write("\n")
        print("clock_unit_check: wrote {} files, {} sites".format(
            len(found), sum(len(v) for v in found.values())))
        return 0
    problems = judge(found, baseline)
    for p in problems:
        print("clock_unit_check: " + p, file=sys.stderr)
    total = sum(len(v) for v in found.values())
    if problems:
        return 1
    print("clock_unit_check: {} raw clock arithmetic site(s) in {} file(s), all baselined".format(
        total, len(found)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
