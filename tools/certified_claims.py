#!/usr/bin/env python3
"""Fail when a `certified` proof target lacks current, compatible evidence.

Event identity and ownership come from the ledger's parser and curated event
map. Certification verdicts and include-closure compatibility come from
green_check, which in turn uses certs' manifest pass rule. In addition, each
`certified` row must cite, in its `evidence` list, at least one archived
manifest under planning/evidence/manifests/, every cited manifest must exist,
and for every event's defining book some cited manifest must record that book
`passed` with the book's current source digest and an undrifted include
closure. Any warning or failure exits 1. `--explain PRF-xxx` prints, for one
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


def manifest_failures(proofs: list[dict], owners: dict[str, set[str]],
                      root: Path = ROOT) -> list[str]:
    """A certified row names the archived run that certified each event book."""
    rows = {str(proof.get("id")): proof for proof in proofs}
    failures: list[str] = []
    for ident, books in sorted(owners.items()):
        cited = cited_manifests(rows.get(ident, {}))
        if not cited:
            failures.append(f"{ident}: cites no manifest under "
                            f"{evidence_manifests.ARCHIVE_REL}/")
            continue
        loaded: list[tuple[str, dict]] = []
        for relative in cited:
            path = root / relative
            if not path.is_file():
                failures.append(f"{ident}: cited manifest {relative} is absent")
                continue
            try:
                value = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError) as error:
                failures.append(f"{ident}: cited manifest {relative} is unreadable: {error}")
                continue
            if isinstance(value, dict):
                loaded.append((Path(relative).stem, value))
        for book in sorted(books):
            digest, listing = current_state(root, book)
            reasons = []
            for run_id, value in loaded:
                ok, why = certifies(value, book, digest, listing)
                if ok:
                    break
                reasons.append(f"{run_id} {why}")
            else:
                detail = "; ".join(reasons) or "no readable cited manifest"
                failures.append(f"{ident}: no cited manifest certified {book} at its "
                                f"current digest {digest[:12]}: {detail}")
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
    return len(owners), len(books), warnings, manifest_failures(proofs, owners, root)


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
