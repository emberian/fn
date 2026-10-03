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
    "tests/acl2/post-identity-captured-agent-join-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-classification-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-digest-block-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-groups-refinement-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-hash-choice-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-hash-domain-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-hash-entry-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-hash-refinement-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-holder-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-payload-refinement-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-refinement-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-source-completion-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-source-continuation-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-source-pair-context-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-source-parser-context-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-source-trace-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/post-identity-captured-tests":
        "stage 0 (04ff9b99b) took the FNCE consumer-authority kinds out of the wire-event grammar and these out of the roots; a root again when post-identity-captured is rebased on fn-cpe-eventp",
    "tests/acl2/consumer-account-adoption-tests":
        "stage 0 (D46, 04ff9b99b) parked the account-adoption chain off the served start; a root again when that chain returns",
    "tests/acl2/consumer-account-auth-tests":
        "stage 0 (D46, 04ff9b99b) parked the account-adoption chain off the served start; a root again when that chain returns",
}

# A test book whose first lines carry `; UNHOOKED <who> (<date>): <why>` was
# taken out of the roots on purpose (lane cert-roots, 2026-10-02): the header
# is its named reason, printed on every run like a KNOWN_RED entry.
UNHOOKED = "; UNHOOKED"


def unhooked(root: Path = ROOT) -> dict[str, str]:
    """The test books whose header says why they are not roots."""
    out = {}
    for path in (root / "tests" / "acl2").glob("*-tests.lisp"):
        with path.open(encoding="utf-8") as stream:
            for _ in range(3):
                line = stream.readline()
                if line.startswith(UNHOOKED):
                    out[f"tests/acl2/{path.stem}"] = line[len(UNHOOKED):].strip()
                    break
    return out


def orphans(root: Path = ROOT, roots: list[str] | None = None) -> list[str]:
    """The test books under ROOT that are not Makefile roots, sorted."""
    listed = (set(roots if roots is not None else ledger.makefile_roots()) | set(KNOWN_RED)
              | set(unhooked(root)))
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
    excused = {**unhooked(), **KNOWN_RED}
    for book, reason in sorted(excused.items()):
        if book in listed:
            print(f"test_roots_check: {book} is a root now: drop it from KNOWN_RED "
                  "or its UNHOOKED header")
            return 1
        print(f"test_roots_check: KNOWN RED, not a root yet: {book}: {reason}")
    count = len(list((ROOT / "tests" / "acl2").glob("*-tests.lisp")))
    print(f"test_roots_check: {count - len(excused)} of {count} tests/acl2/*-tests.lisp "
          f"are certification roots; {len(excused)} known red or unhooked (above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
