#!/usr/bin/env python3
"""Every books/**/*.lisp belongs to a Makefile certification root's closure.

Unlike test_roots_check's direct-root rule for test witnesses, a production
book may be included by a root. EXCLUDED entries are work items with reasons,
printed on every run; an unlisted orphan makes this check exit 1.
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import ledger  # noqa: E402


# The seat assigns exclusions, each with a reason naming its outstanding work.
_P_DRAFTS = (
    "P's unrooted drafts (coordinator ruling 10-11, Fungus seam 9): post-identity-captured stays off the roots until it is rebased on fn-cpe-eventp (its tests are KNOWN_RED in tools/test_roots_check.py)")
_C_ROUTED = (
    'never certified of record; found by A18 10-12; routed to seat C (coordinator 10-12): root it with a certify of record, or delete it')
_ORPHAN = (
    'outside every Makefile root at dev 402b65786 (first run of this check, 10-12); repair item BOOK-ROOTS-ORPHANS: its owner roots it with a certify of record or deletes it')
P, C, O = _P_DRAFTS, _C_ROUTED, _ORPHAN
EXCLUDED: dict[str, str] = {
    "books/acceptance-binding-held-gate.lisp": O,
    "books/acceptance-binding.lisp": O,
    "books/account-adoption-operation-source.lisp": O,
    "books/account-adoption-result.lisp": O,
    "books/account-adoption-turn-continuation.lisp": O,
    "books/account-config-generation-cursor.lisp": O,
    "books/account-config-history-cursor.lisp": O,
    "books/account-replay-source.lisp": O,
    "books/arena-reader-bound.lisp": O,
    "books/bp-received-raw-source.lisp": O,
    "books/bp-segmented-wire-job.lisp": O,
    "books/bp-wire-canonical-cursor.lisp": O,
    "books/bp-wire-primary-cursor.lisp": O,
    "books/consumer-account-durable-outcome-state.lisp": O,
    "books/consumer-authority-carried-fold.lisp": O,
    "books/consumer-authority-carried-result.lisp": O,
    "books/consumer-configured-authority-event.lisp": O,
    "books/consumer-configured-authority-replay.lisp": O,
    "books/consumer-configured-control-event.lisp": O,
    "books/consumer-control-row-cursor.lisp": O,
    "books/control-config-projection.lisp": O,
    "books/held-composite-fields.lisp": O,
    "books/history-config-completion.lisp": O,
    "books/history-config-journal-state.lisp": O,
    "books/index-backing-publication-row-carry.lisp": O,
    "books/index-backing-row-carry.lisp": O,
    "books/index-backing-served-producer-carry.lisp": O,
    "books/index-incoming-request.lisp": O,
    "books/owner-catalog-root-recovery.lisp": O,
    "books/owner-report-writer-entry.lisp": O,
    "books/page-maintenance-lease.lisp": O,
    "books/page-read-bindings-transaction.lisp": O,
    "books/post-identity-captured-agent-join.lisp": P,
    "books/post-identity-captured-classification.lisp": P,
    "books/post-identity-captured-digest-block.lisp": P,
    "books/post-identity-captured-groups-refinement.lisp": P,
    "books/post-identity-captured-hash-choice.lisp": P,
    "books/post-identity-captured-hash-domain.lisp": P,
    "books/post-identity-captured-hash-entry.lisp": P,
    "books/post-identity-captured-hash-refinement.lisp": P,
    "books/post-identity-captured-holder.lisp": P,
    "books/post-identity-captured-payload-refinement.lisp": P,
    "books/post-identity-captured-refinement.lisp": P,
    "books/post-identity-captured-source-completion.lisp": P,
    "books/post-identity-captured-source-context.lisp": P,
    "books/post-identity-captured-source-continuation.lisp": P,
    "books/post-identity-captured-source-pair-context.lisp": P,
    "books/post-identity-captured-source-parser-context.lisp": P,
    "books/post-identity-captured-source-trace.lisp": P,
    "books/post-identity-captured.lisp": P,
    "books/recovery-file-turn.lisp": O,
    "books/recovery-open-origin.lisp": O,
    "books/recovery-page-file-controller.lisp": O,
    "books/served-catalog-group-low-cost.lisp": C,
    "books/snapshot-initial-custody.lisp": O,
    "books/snapshot-initial-request.lisp": O,
}


def coverage(root: Path = ROOT, roots: list[str] | None = None) -> tuple[set[str], set[str]]:
    """(All production book paths, paths in the roots' local include closure)."""
    books = {}
    for directory in ("books", "host", "tests/acl2"):
        for path in sorted((root / directory).rglob("*.lisp")):
            relative = path.relative_to(root).as_posix()
            books[relative] = ledger.analyze_book(path, relative)
    listed = roots if roots is not None else ledger.makefile_roots()
    return ({path for path in books if path.startswith("books/")},
            ledger.root_closure(books, listed))


def main(root: Path = ROOT, roots: list[str] | None = None,
         excluded: dict[str, str] | None = None) -> int:
    excluded = EXCLUDED if excluded is None else excluded
    books, covered = coverage(root, roots)
    failed = False
    for book, reason in sorted(excluded.items()):
        print(f"book_roots_check: EXCLUDED: {book}: {reason}")
        if not isinstance(reason, str) or not reason.strip():
            print(f"book_roots_check: {book} has no exclusion reason")
            failed = True
        if book not in books or book in covered:
            print(f"book_roots_check: {book} is absent or covered now: drop it from EXCLUDED")
            failed = True
    orphans = sorted(books - covered - excluded.keys())
    for book in orphans:
        print(f"book_roots_check: {book} is outside the Makefile roots' closure "
              "and has no EXCLUDED work item")
    print(f"book_roots_check: {len(books & covered)} of {len(books)} books/**/*.lisp "
          f"are covered; {len(excluded)} excluded; {len(orphans)} unlisted orphan(s)")
    return 1 if failed or orphans else 0


if __name__ == "__main__":
    raise SystemExit(main())
