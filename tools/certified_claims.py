#!/usr/bin/env python3
"""Fail when a `certified` proof target lacks current, compatible evidence.

Event identity and ownership come from the ledger's parser and curated event
map. Certification verdicts and include-closure compatibility come from
green_check, which in turn uses certs' manifest pass rule. In addition, each
`certified` row's event books must each be green at these bytes
(green_check.green_at_these_bytes: green_check's verdict at the current source
digest and include closure, from an archived manifest under
planning/evidence/manifests/) -- the one meaning of "certified", from which
tools/ledger.py generates the status (row R2); a manifest a row cites is
provenance and must exist. Any warning or failure exits 1. `--explain PRF-xxx` prints, for one
row, each event, its book, the book's current digest, and the newest manifest
that certified that digest. This is a read-only claim audit, not an ACL2 run,
guard audit, or saved-image qualification.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs  # noqa: E402
import evidence_manifests  # noqa: E402
import green_check  # noqa: E402
import ledger  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]


def cited_manifests(proof: dict) -> list[str]:
    """The archived manifest paths a registry row cites as evidence."""
    prefix = evidence_manifests.ARCHIVE_REL + "/"
    return [str(item) for item in proof.get("evidence") or []
            if str(item).startswith(prefix)]


def certifies(manifest: dict, book: str, digest: str, listing: list[str]
              ) -> tuple[bool, str]:
    """Whether one manifest certified `book` at `digest` and its closure."""
    if (manifest.get("book_results") or {}).get(book) != "passed":
        return False, "does not record it passed"
    sources = manifest.get("source_digests_sha256") or {}
    recorded = sources.get(book + ".lisp") if isinstance(sources, dict) else None
    if recorded != digest:
        return False, (f"certified digest {str(recorded)[:12]}, "
                       f"current {digest[:12]} (stale digest)")
    moved = certs.closure_drift(listing, sources)
    if moved:
        return False, "include closure moved: " + ", ".join(moved)
    return True, "certified at current digest and closure"


def current_state(root: Path, book: str) -> tuple[str, list[str]]:
    return (certs.content_hash(root / (book + ".lisp")),
            certs.closure_listing(certs.closure(root, book)))


def uncited_books(root: Path, books, tracked_only: bool = True) -> list[str]:
    """The BOOKS no committed manifest certified at their current digest and closure.

    `certifies` is the rule `manifest_failures` holds a registry row's cited
    run to; a book installed from the certificate cache satisfies ACL2 but
    not this, when the run that certified it never had its manifest
    committed (batch AY, 2026-09-28: the union cite installed 15 books so,
    and green_check and certified_claims still owed them until a
    --recertify run).  `tracked_only` reads the archive's git-tracked
    manifests (a tree with no git reads every archived one).
    """
    tracked = evidence_manifests.tracked_manifests(root) if tracked_only else set()
    passed: dict[str, list[dict]] = {}
    for _, manifest in evidence_manifests.load_all_archived(
            root, tracked_only=bool(tracked)):
        for book, verdict in (manifest.get("book_results") or {}).items():
            if verdict == "passed":
                passed.setdefault(book, []).append(manifest)
    uncited: list[str] = []
    for book in books:
        try:
            digest, listing = current_state(root, book)
        except (OSError, ValueError, certs.UnreadableBook):
            uncited.append(book)
            continue
        if not any(certifies(manifest, book, digest, listing)[0]
                   for manifest in passed.get(book, [])):
            uncited.append(book)
    return uncited


def manifest_failures(proofs: list[dict], owners: dict[str, set[str]],
                      root: Path = ROOT, report: dict | None = None) -> list[str]:
    """A certified row's event books are each green at these bytes.

    One meaning (row R2): green_check's verdict at the book's current digest
    and include closure, from an archived manifest
    (green_check.green_at_these_bytes), the rule tools/ledger.py generates
    the status from.  A manifest the row cites is provenance: it must exist
    and be readable, but citing is not what certifies.
    """
    rows = {str(proof.get("id")): proof for proof in proofs}
    if report is None:
        books = sorted(set().union(*owners.values())) if owners else []
        report = green_check.audit(root, roots=books) if books else {"books_by_verdict": {}}
    records = report.get("books_by_verdict", {})
    failures: list[str] = []
    for ident, books in sorted(owners.items()):
        for relative in cited_manifests(rows.get(ident, {})):
            if not evidence_manifests.evidence_store.exists(root, relative):
                failures.append(f"{ident}: cited manifest {relative} is absent")
                continue
            try:
                json.loads(evidence_manifests.evidence_store.read_text(root, relative))
            except (OSError, ValueError) as error:
                failures.append(f"{ident}: cited manifest {relative} is unreadable: {error}")
        for book in sorted(books):
            record = records.get(book)
            if not green_check.green_at_these_bytes(record):
                note = (record or {}).get("note", "no verdict")
                if record and record.get("verdict") == "green" and not record.get("certified_archived"):
                    note = "green only in an unarchived local manifest; commit it (evidence_manifests.py add)"
                failures.append(f"{ident}: {book} is not green at these bytes: {note}")
    return failures


def explain(ident: str, root: Path = ROOT) -> list[str]:
    """Each event of one row, its book, current digest and newest certifier."""
    proofs = json.loads((root / "planning/proofs.json").read_text(encoding="utf-8"))["proofs"]
    curated = json.loads((root / "planning/proof-events.json").read_text(encoding="utf-8"))
    row = next((proof for proof in proofs if proof.get("id") == ident), None)
    if row is None:
        raise KeyError(f"no proof target {ident}")
    tree = ledger.load_tree()
    target = next((item for item in curated.get("targets", [])
                   if item.get("id") == ident), {})
    runs = green_check.manifests(root)
    cited = {Path(item).stem for item in cited_manifests(row)}
    lines = [f"{ident}: status={row.get('status')} cited-manifests="
             + (", ".join(sorted(cited)) or "none")]
    for event in target.get("events") or []:
        name, kind = event.get("name"), event.get("kind", "theorem")
        table = tree.theorems if kind == "theorem" else tree.functions
        definition = table.get(name)
        book = (definition.book if definition is not None
                else tree.constrained.get(name))
        if book is None:
            lines.append(f"  {name} ({kind}): definition absent")
            continue
        book = book.removesuffix(".lisp")
        digest, listing = current_state(root, book)
        newest = "none"
        for run, manifest in reversed(runs):
            if certifies(manifest, book, digest, listing)[0]:
                newest = run.run_id + (" (cited)" if run.run_id in cited else " (not cited)")
                break
        lines.append(f"  {name} ({kind}): book={book} digest={digest} "
                     f"newest-certifying-manifest={newest}")
    return lines


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
    return len(owners), len(books), warnings, manifest_failures(proofs, owners, root, report)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--explain", metavar="PRF-xxx",
                        help="print each event, its book, current digest and newest "
                             "certifying manifest for one row")
    args = parser.parse_args(argv)
    try:
        if args.explain:
            print("\n".join(explain(args.explain)))
            return 0
        targets, books, warnings, failures = audit()
    except evidence_manifests.evidence_store.EvidenceUnavailable as error:
        print(f"certified-claims: UNAVAILABLE: committed evidence cannot be read: {error}")
        return evidence_manifests.evidence_store.EXIT_UNAVAILABLE
    except (OSError, ValueError, KeyError, TypeError,
            green_check.certs.UnreadableBook) as error:
        print(f"certified-claims: evidence unavailable: {error}")
        return 2
    print(f"certified-claims: {targets} certified targets, {books} event books; "
          f"{len(warnings)} warning(s), {len(failures)} manifest-citation failure(s). "
          "Archived manifests are scoped evidence, "
          "not certificates in this tree or native image qualification.")
    for warning in warnings:
        print(f"WARNING certified-claims: {warning}")
    for failure in failures:
        print(f"FAIL certified-claims: {failure}")
    return 1 if warnings or failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
