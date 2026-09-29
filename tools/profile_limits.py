#!/usr/bin/env python3
"""The runtime profile's limits: one table, read from books/profile-limits.lisp.

`*fn-profile-limits*' (books/profile-limits.lisp) is the single source of
every runtime profile figure: SBCL's thread-local storage and control stack,
the thread counts, the per-thread runtime, the collection trigger's cap, the
default connection capacity, the alert thresholds and the public exposure
defaults.  The books define their constants from it (`fn-profile-limit'),
the raw host reads those constants, the image build prints the launcher's
figures from it, and everything else reads it HERE, without evaluating
anything (the ledger's reader; the table is a literal):

    python3 tools/profile_limits.py get stack-kib        # 1024
    python3 tools/profile_limits.py --json               # every row
    python3 tools/profile_limits.py --check              # exit 1 on a finding
    python3 tools/profile_limits.py --write              # regenerate the regions

DOCUMENTATION states a figure through a generated span

    <!--limit:fixed-threads-->12<!--/limit-->
    <!--limit:fixed-threads + mux-loops + control-clients-->30<!--/limit-->
    <!--limit:stack-kib,-->1,024<!--/limit-->            (`,': thousands commas)

(a sum or difference of rows and integers), invisible when the Markdown is
rendered; `--write' rewrites each span's text from the table and `--check'
refuses one that differs.  REGION_FILES names the files that carry spans.

KNOWN COPIES (`COPIES') are the places a literal copy of a row used to live
(a launcher, a host constant, a test); `--check' refuses each if the literal
is back.  A copy that must stay (a toolchain's path name, an operator's own
policy file) is not listed and is named in the record instead.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

BOOK = "books/profile-limits.lisp"
REGION_FILES = ("docs/operator-internals.md", "docs/operator.md", "specs/host.md",
                "specs/nntp.md")
SPAN = re.compile(r"<!--limit:([a-z0-9+\-, ]+?)-->(.*?)<!--/limit-->")
# (file, pattern): a literal copy that must not come back.
COPIES = (
    ("tools/build_native_host.sh", r"FN_TLS_LIMIT:-65536"),
    ("host/native/mux.lisp", r"\(defconstant \+fnn-mux-loops\+ \d"),
    ("host/native/mux.lisp", r"\(defconstant \+fnn-mux-fixed-threads\+ \d"),
    ("host/native/io.lisp", r"\(defparameter \+fnn-gc-nursery-octets\+ \(\* \d"),
    ("books/heap-reservation.lisp", r"\(defconst \*fn-heap-(stack-octets|fixed-threads|default-stack-kib|mux-loops)\* \(?\d"),
    ("books/connection-budget.lisp", r"\(defconst \*fn-cbud-thread-runtime-octets\* \d"),
    ("books/native-control.lisp", r"\(defconst \*fn-nctrl-max-active-clients\* \d"),
    ("books/native-config.lisp", r"\(defconst \*fn-ncfg-default-(max-connections|headroom-min-percent|refusal-rate-per-minute|cooldown-seconds)\* \d"),
    ("books/public-exposure.lisp", r"\(defconst \*fn-exp-public-(per-address|steps|idle|first|auth-failures|posts)\* \d"),
    ("tests/test_native_image_floor.py", r"SMALL_STACK_KIB = \d"),
    ("tests/test_build_native_host.py", r"--tls-limit 65536"),
    ("tools/build_local_acl2.sh", r"--tls-limit 65536"),
    ("tools/cut_release.sh", r"--tls-limit 65536"),
)


def rows(root: Path = ROOT) -> dict[str, dict]:
    """KEY -> {value, unit, meaning}, in the table's order."""
    text = (root / BOOK).read_text(encoding="utf-8")
    for form, _line in ledger.Reader(text).top_level():
        if (ledger.head(form) == "defconst" and len(form) >= 3
                and str(form[1]).lower() == "*fn-profile-limits*"):
            value = form[2]
            if ledger.head(value) == "quote":
                value = value[1]
            out: dict[str, dict] = {}
            for row in value:
                key, number, unit, meaning = row
                out[str(key).lower().lstrip(":")] = {
                    "value": int(number), "unit": unit, "meaning": meaning}
            return out
    raise SystemExit("profile_limits: *fn-profile-limits* not found in " + BOOK)


def get(key: str, root: Path = ROOT) -> int:
    return rows(root)[key]["value"]


def _tokens(expr: str) -> list[str]:
    return expr.rstrip(",").split()


def _terms_ok(expr: str, table: dict[str, dict]) -> str | None:
    """The first token that is neither a row, an integer nor + or -, or None."""
    tokens = _tokens(expr)
    for index, token in enumerate(tokens):
        if index % 2:
            if token not in ("+", "-"):
                return token
        elif not token.isdigit() and token not in table:
            return token
    return None if len(tokens) % 2 else "(a trailing operator)"


def evaluate(expr: str, table: dict[str, dict]) -> str:
    tokens = _tokens(expr)
    total, sign = 0, 1
    for index, token in enumerate(tokens):
        if index % 2:
            sign = 1 if token == "+" else -1
            continue
        value = int(token) if token.isdigit() else table[token]["value"]
        total += sign * value
    return "{:,}".format(total) if expr.endswith(",") else str(total)


def regions(root: Path, table: dict[str, dict], write: bool) -> list[str]:
    problems: list[str] = []
    for relative in REGION_FILES:
        path = root / relative
        if not path.is_file():
            problems.append("{}: missing".format(relative))
            continue
        text = path.read_text(encoding="utf-8")
        spans = 0

        def fix(match: re.Match) -> str:
            nonlocal spans
            spans += 1
            expr, shown = match.group(1), match.group(2)
            bad = _terms_ok(expr, table)
            if bad is not None:
                problems.append("{}: <!--limit:{}--> names no row {}".format(relative, expr, bad))
                return match.group(0)
            want = evaluate(expr, table)
            if shown != want:
                if not write:
                    problems.append("{}: <!--limit:{}--> says {} and the table says {}".format(
                        relative, expr, shown, want))
                return "<!--limit:{}-->{}<!--/limit-->".format(expr, want)
            return match.group(0)

        new = SPAN.sub(fix, text)
        if spans == 0:
            problems.append("{}: carries no <!--limit:...--> span".format(relative))
        if write and new != text:
            path.write_text(new, encoding="utf-8")
    return problems


def copies(root: Path) -> list[str]:
    problems: list[str] = []
    for relative, pattern in COPIES:
        path = root / relative
        if path.is_file() and re.search(pattern, path.read_text(encoding="utf-8")):
            problems.append("{}: a literal copy of a profile limit is back ({}); read "
                            "books/profile-limits.lisp instead".format(relative, pattern))
    return problems


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", nargs="?", choices=["get"])
    parser.add_argument("key", nargs="?")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)
    table = rows()
    if args.command == "get":
        if args.key not in table:
            print("profile_limits: no row {}".format(args.key), file=sys.stderr)
            return 2
        print(table[args.key]["value"])
        return 0
    if args.json:
        print(json.dumps(table, indent=2))
        return 0
    problems = regions(ROOT, table, args.write) + copies(ROOT)
    print("profile_limits: {} rows; {} finding(s)".format(len(table), len(problems)))
    for problem in problems:
        print("  " + problem)
    return 1 if (args.check and problems) else 0


if __name__ == "__main__":
    raise SystemExit(main())
