#!/usr/bin/env python3
"""Warn when a `certified` proof target lacks current, compatible evidence.

Event identity and ownership come from the ledger's parser and curated event
map. Certification verdicts and include-closure compatibility come from
green_check, which in turn uses certs' manifest pass rule. This is a read-only
claim audit, not an ACL2 run, guard audit, or saved-image qualification.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import green_check  # noqa: E402
import ledger  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]


def event_owners(proofs: list[dict], curated: dict, tree: ledger.Tree
                 ) -> tuple[dict[str, set[str]], list[str]]:
    """Find the actual books for certified targets' curated ACL2 events."""
    targets = {row.get("id"): row for row in curated.get("targets", [])}
    owners: dict[str, set[str]] = {}
    warnings: list[str] = []
    for proof in proofs:
        if proof.get("status") != "certified":
            continue
        ident = str(proof.get("id", "<missing-id>"))
        declared = proof.get("events") or []
        events = targets.get(ident, {}).get("events") or []
        expected = [event.get("name") for event in events]
        if not events:
            warnings.append(f"{ident}: no curated ACL2 events for certified status")
        if declared != expected:
            warnings.append(f"{ident}: proofs.json events differ from the curated event map")
        books: set[str] = set()
        for event in events:
            name = event.get("name")
            kind = event.get("kind", "theorem")
            if kind == "theorem":
                definition = tree.theorems.get(name)
                if definition is None:
                    warnings.append(f"{ident}: cited theorem {name!r} is absent")
                    continue
                if name in tree.suspects:
                    warnings.append(f"{ident}: cited theorem {name!r} is SUSPECT")
                book = definition.book
            elif kind == "guarded-function":
                definition = tree.functions.get(name)
                if definition is None:
                    book = tree.constrained.get(name)
                    if book is None:
                        warnings.append(f"{ident}: cited guarded function {name!r} is absent")
                        continue
                else:
                    book = definition.book
                    if definition.guard_status != "verified":
                        warnings.append(f"{ident}: cited function {name!r} has guard "
                                        f"status {definition.guard_status}")
            else:
                warnings.append(f"{ident}: event {name!r} has unknown kind {kind!r}")
                continue
            if book not in tree.closure:
                warnings.append(f"{ident}: event {name!r} is outside Makefile root closure")
            books.add(book.removesuffix(".lisp"))
        owners[ident] = books
    return owners, warnings


def evidence_warnings(owners: dict[str, set[str]], report: dict) -> list[str]:
    """Apply green_check's exact current include-closure verdict per owner."""
    records = report.get("books_by_verdict", {})
    warnings: list[str] = []
    for ident, books in owners.items():
        for book in sorted(books):
            record = records.get(book)
            if record is None:
                warnings.append(f"{ident}: {book} has no closure evidence record")
            elif record["verdict"] != "green":
                warnings.append(f"{ident}: {book} has {record['verdict']} evidence "
                                f"at its current source digest; {record.get('note', '')}")
            elif record.get("deps_moved_since"):
                warnings.append(f"{ident}: {book} has no compatible current "
                                "include-closure evidence; moved: "
                                + ", ".join(record["deps_moved_since"]))
    return warnings


def audit() -> tuple[int, int, list[str]]:
    root = ROOT
    proofs = json.loads((root / "planning/proofs.json").read_text(encoding="utf-8"))["proofs"]
    curated = json.loads((root / "planning/proof-events.json").read_text(encoding="utf-8"))
    tree = ledger.load_tree()
    owners, warnings = event_owners(proofs, curated, tree)
    books = sorted(set().union(*owners.values())) if owners else []
    report = green_check.audit(root, roots=books) if books else {"books_by_verdict": {}}
    warnings.extend(evidence_warnings(owners, report))
    return len(owners), len(books), warnings


def main() -> int:
    try:
        targets, books, warnings = audit()
    except (OSError, ValueError, KeyError, TypeError,
            green_check.certs.UnreadableBook) as error:
        print(f"certified-claims: evidence unavailable: {error}")
        return 0
    print(f"certified-claims: {targets} certified targets, {books} event books; "
          f"{len(warnings)} warning(s). Archived manifests are scoped evidence, "
          "not certificates in this tree or native image qualification.")
    for warning in warnings:
        print(f"WARNING certified-claims: {warning}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
