#!/usr/bin/env python3
"""The ACL2 system books fn's toolchain certifies, and whether a box has them.

Q7h (d27-representation, 2026-09-29): `std/lists/nthcdr' and `take' had no
certificate on either box, so a lane's `(include-book "std/lists/nthcdr" :dir
:system)' loaded the source uncertified in proof_repl and the farm refused it;
the lane routed around it with a local lemma.  The system books are part of
the toolchain, not of a lane: this is the one list, every box certifies it,
and `make check' fails on a box that lacks one.

    python3 tools/system_books.py list               # one book per line
    python3 tools/system_books.py check [--acl2 L]   # 0 all certified, 1 missing named, 2 NOT RUN
    python3 tools/system_books.py certify [--acl2 L] [--jobs 2]

THE LIST is every `(include-book "X" :dir :system)' in books/, tests/acl2/ and
host/ (read, not hand-kept: a new system include joins the toolchain the day
it is written) plus TOOLCHAIN_EXTRA, the std/lists books lanes reach for
(nthcdr, take, len, nth).  tools/build_local_acl2.sh certifies the same list
for the laptop's ACL2.

THE BOX'S BOOKS are those of the ACL2 the launcher runs: the `--core'
argument of its exec line names `<acl2>/saved_acl2.core', and the books are
`<acl2>/books/'.  The launcher is --acl2, else $FN_ACL2; with neither, `check'
prints NOT RUN and exits 2 (uncertain is not green).  `certify' runs ACL2's
own books Makefile (`make -C BOOKS ACL2=L X.cert ...', the missing ones only,
two jobs: it runs outside tools/acl2_slots.py's pool) and then checks again.
"""
from __future__ import annotations

import argparse
import os
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = ("books", "tests/acl2", "host")
TOOLCHAIN_EXTRA = ("std/lists/nthcdr", "std/lists/take", "std/lists/len", "std/lists/nth")
SYSTEM_INCLUDE = re.compile(r'\(include-book\s+"([^"]+)"\s+:dir\s+:system', re.I)


def tree_includes(root: Path = ROOT) -> set[str]:
    found: set[str] = set()
    for directory in SOURCES:
        for path in sorted((root / directory).rglob("*.lisp")):
            text = path.read_text(encoding="utf-8", errors="replace")
            text = re.sub(r";[^\n]*", "", text)
            found.update(SYSTEM_INCLUDE.findall(text))
    return found


def books(root: Path = ROOT) -> list[str]:
    return sorted(tree_includes(root) | set(TOOLCHAIN_EXTRA))


def launcher(given: str | None) -> Path | None:
    configured = given or os.environ.get("FN_ACL2", "")
    if not configured:
        return None
    candidate = (Path(configured).expanduser() if os.sep in configured
                 else Path(shutil.which(configured) or "/nonexistent"))
    return candidate if candidate.is_file() else None


def books_dir(launcher_path: Path) -> Path | None:
    """`<acl2>/books' of the saved core the launcher's exec line names."""
    text = launcher_path.read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        if not line.lstrip().startswith("exec "):
            continue
        words = shlex.split(line.replace("${SBCL_USER_ARGS}", "").replace('"$@"', ""))
        if "--core" in words and words.index("--core") + 1 < len(words):
            core = Path(words[words.index("--core") + 1])
            return core.parent / "books"
    return None


def missing(directory: Path, wanted: list[str]) -> list[str]:
    return [book for book in wanted if not (directory / f"{book}.cert").is_file()]


def check(given: str | None, wanted: list[str]) -> tuple[int, str]:
    found = launcher(given)
    if found is None:
        return 2, ("system_books: NOT RUN: no ACL2 launcher (--acl2 or FN_ACL2); "
                   "the toolchain's system books are unchecked")
    directory = books_dir(found)
    if directory is None or not directory.is_dir():
        return 2, f"system_books: NOT RUN: {found} names no saved core with a books/ beside it"
    absent = missing(directory, wanted)
    if absent:
        return 1, (f"system_books: {len(absent)} of {len(wanted)} toolchain system books "
                   f"have no certificate in {directory}: {', '.join(absent)}; "
                   f"run tools/system_books.py certify --acl2 {found}")
    return 0, f"system_books: all {len(wanted)} toolchain system books certified in {directory}"


def certify(given: str | None, wanted: list[str], jobs: int) -> int:
    found = launcher(given)
    directory = books_dir(found) if found else None
    if found is None or directory is None:
        print("system_books: NOT RUN: no ACL2 launcher with a books/ directory", file=sys.stderr)
        return 2
    absent = missing(directory, wanted)
    if absent:
        command = ["make", "-C", str(directory), "-j", str(jobs), f"ACL2={found}",
                   "USE_QUICKLISP=0", *[f"{book}.cert" for book in absent]]
        print("system_books: " + " ".join(shlex.quote(w) for w in command), flush=True)
        done = subprocess.run(command)
        if done.returncode != 0:
            print(f"system_books: make exited {done.returncode}", file=sys.stderr)
            return 1
    status, line = check(str(found), wanted)
    print(line)
    return status


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("list")
    for name in ("check", "certify"):
        one = sub.add_parser(name)
        one.add_argument("--acl2")
        if name == "certify":
            one.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args(argv)
    wanted = books()
    if args.command == "list":
        print("\n".join(wanted))
        return 0
    if args.command == "check":
        status, line = check(args.acl2, wanted)
        print(line)
        return status
    return certify(args.acl2, wanted, args.jobs)


if __name__ == "__main__":
    sys.exit(main())
