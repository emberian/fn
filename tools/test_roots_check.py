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


# Test books known red that cannot be roots until their owner repairs them:
# each names the failure, so the exception is a work item, not a hiding place.
# The check prints every one on each run.
KNOWN_RED = {
    "tests/acl2/accounts-wire-tests":
        "red at dev e78a6645d (hbox certify-20260929T045858Z-3350988): the "
        "assert-event after *awt-381* (a redeem-wait session's PASS answers "
        "no effects) fails; the auth/redeem semantics moved under it while it "
        "was in no Makefile list",
}


def orphans(root: Path = ROOT, roots: list[str] | None = None) -> list[str]:
    """The test books under ROOT that are not Makefile roots, sorted."""
    listed = set(roots if roots is not None else ledger.makefile_roots()) | set(KNOWN_RED)
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
    listed = set(ledger.makefile_roots())
    for book, reason in sorted(KNOWN_RED.items()):
        if book in listed:
            print(f"test_roots_check: {book} is a root now: drop it from KNOWN_RED")
            return 1
        print(f"test_roots_check: KNOWN RED, not a root yet: {book}: {reason}")
    count = len(list((ROOT / "tests" / "acl2").glob("*-tests.lisp")))
    print(f"test_roots_check: {count - len(KNOWN_RED)} of {count} tests/acl2/*-tests.lisp "
          f"are certification roots; {len(KNOWN_RED)} known red (above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
