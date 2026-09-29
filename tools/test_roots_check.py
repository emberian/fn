#!/usr/bin/env python3
"""Every tests/acl2/*-tests.lisp is a certification root (Q7j).

limits-live-3 (2026-09-29) found six test books in no Makefile list: no
`make certify`, no farm `--affected-by` and no batch cite ever reached them,
and open-frontier-tests had never certified.  A test book included by
another root is certified inside that root, but nothing names it, so its
own witnesses read as covered while no run cites them; the rule is simple:
each test book is a root of ACL2_BOOKS.

    python3 tools/test_roots_check.py          # exit 1 naming each orphan
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import ledger  # noqa: E402


def orphans(root: Path = ROOT, roots: list[str] | None = None) -> list[str]:
    """The test books under ROOT that are not Makefile roots, sorted."""
    listed = set(roots if roots is not None else ledger.makefile_roots())
    return sorted(f"tests/acl2/{path.stem}"
                  for path in (root / "tests" / "acl2").glob("*-tests.lisp")
                  if f"tests/acl2/{path.stem}" not in listed)


def main() -> int:
    found = orphans()
    if found:
        for book in found:
            print(f"test_roots_check: {book}.lisp is not in the Makefile's "
                  "ACL2_BOOKS: nothing certifies or cites it; add it there "
                  "(after the books it tests)")
        return 1
    count = len(list((ROOT / "tests" / "acl2").glob("*-tests.lisp")))
    print(f"test_roots_check: all {count} tests/acl2/*-tests.lisp are certification roots")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
