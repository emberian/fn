#!/usr/bin/env python3
"""Reproducible proof-engineering census, using the assurance ledger parser.

The census is source inventory, not admission/certification evidence. Known
generator expansions are those ledger.py models; opaque macro/make-event bodies
and system books are explicitly outside this event-level inventory. Reviewers
write result JSON keyed by book or event id; untouched entries stay unvisited.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

import ledger

STATES = {"inspected", "no-change", "candidate", "tested", "blocked", "unvisited"}


def literal_theorems(value: object) -> set[str]:
    """Names written in literal defthm forms, including nested local wrappers."""
    if not isinstance(value, list):
        return set()
    names = set()
    if len(value) > 1 and str(value[0]) in {"defthm", "defthmd", "defrule"} and isinstance(value[1], ledger.Sym):
        names.add(str(value[1]))
    for item in value:
        names.update(literal_theorems(item))
    return names


def hint_features(value: object) -> dict:
    """Screen every modeled hint; features are leads, never cost estimates."""
    counts = Counter()
    def visit(term):
        if isinstance(term, ledger.Sym):
            if str(term) in {":in-theory", ":use", ":expand", ":induct", ":cases", ":nonlinearp", ":do-not-induct"}:
                counts[str(term)] += 1
        elif isinstance(term, list):
            if term and str(term[0]) in {"enable", "disable", "e/d"}:
                counts[str(term[0])] += 1
                if str(term[0]) == "enable":
                    counts["enabled_items"] += len(term) - 1
                elif str(term[0]) == "e/d" and len(term) > 1 and isinstance(term[1], list):
                    counts["enabled_items"] += len(term[1])
            for item in term:
                visit(item)
    visit(value)
    return dict(counts)


def family(path: str) -> str:
    name = Path(path).stem
    if name.startswith(("bp-", "dtn", "ltp", "tcpcl", "peer", "replication", "inventory", "batch", "contact")):
        return "transport"
    if name.startswith(("byte-", "store-", "page-", "payload-", "checkpoint", "arena-", "retention", "reservation", "journal", "extent", "segment", "log-")):
        return "persistence"
    if name.startswith(("owner", "nntp", "served", "web", "http", "account", "auth", "admin", "operator", "connection", "session", "reader")):
        return "served"
    return "foundations"


def census(root: Path) -> dict:
    tree = ledger.load_tree(lazy=True)
    all_lisp = {p.relative_to(root).as_posix() for directory in ("books", "host", "tests/acl2")
                for p in (root / directory).rglob("*.lisp")}
    books = dict(tree.books)
    for path in sorted(all_lisp - books.keys()):
        books[path] = ledger.analyze_book(root / path, path)
    rows = []
    for path, book in sorted(books.items()):
        events = []
        text = (root / path).read_text()
        literal_names = literal_theorems([form for form, _ in ledger.Reader(text).top_level()])
        for theorem in book.theorems:
            events.append({"id": f"{path}:{theorem.line}:theorem:{theorem.name}",
                           "kind": "theorem", "name": theorem.name,
                           "line": theorem.line, "local": theorem.local,
                           "generator_origin": theorem.name not in literal_names,
                           "hint_features": hint_features(theorem.hints),
                           "status": "unvisited"})
        for fn in book.functions:
            # Raw Common Lisp definitions are not ACL2 admission events.
            if fn.program or path.startswith("host/native/"):
                continue
            events.append({"id": f"{path}:{fn.line}:admission-guard:{fn.name}",
                           "kind": "admission-guard", "name": fn.name,
                           "line": fn.line, "local": fn.local,
                           "generator_origin": fn.generated,
                           "guard_source_status": fn.guard_status,
                           "status": "unvisited"})
        # Explicit verification is a proof attempt separate from admission.
        for occurrence, name in enumerate(book.verify_guards):
            events.append({"id": f"{path}:verify-guards:{occurrence}:{name}",
                           "kind": "verify-guards", "name": name,
                           "occurrence": occurrence,
                           "status": "unvisited"})
        rows.append({"book": path, "family": family(path), "sha256": hashlib.sha256((root / path).read_bytes()).hexdigest(),
                     "source_class": "certifiable-book" if path in tree.books else "raw-host" if path.startswith("host/") else "nested-support",
                     "status": "unvisited", "events": events,
                     "verify_guards": book.verify_guards,
                     "local_book_includes": book.includes,
                     "exported_theory_forms": len(book.in_theory_forms),
                     "system_includes": book.system_includes,
                     "source_read_error": book.read_error,
                     "macro_definitions": sorted(book.macro_bodies)})
    inventoried = {r["book"] for r in rows}
    return {"schema": 1, "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
            "ledger_parser_sha256": hashlib.sha256((root / "tools/ledger.py").read_bytes()).hexdigest(),
            "census_tool_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope": "ledger-modelled project named theorem and logic-mode admission/guard events; source inventory only",
            "exclusions": {"system_book_events": "external ACL2 books are referenced, not expanded",
                           "opaque_generators": "ledger models supported fn generators; arbitrary make-event and macros are not evaluated",
                           "other_lisp_files": sorted(all_lisp - inventoried),
                           "raw_common_lisp_definitions": "host/native function definitions are not ACL2 admission events; parsed theorems/verify-guards retained if any"},
            "books": rows}


def overlay(data: dict, paths: list[Path]) -> None:
    records = {row["book"]: row for row in data["books"]}
    records.update({event["id"]: event for row in data["books"] for event in row["events"]})
    allowed = {"id", "status", "reason", "evidence", "source_sha256", "review_scope"}
    for path in paths:
        for item in json.loads(path.read_text()):
            key, status = item["id"], item["status"]
            if key not in records or status not in STATES:
                raise ValueError(f"invalid result in {path}: {key} {status}")
            unknown = item.keys() - allowed
            if unknown:
                raise ValueError(f"result overwrites source facts in {path}: {sorted(unknown)}")
            record = records[key]
            if "book" in record and status == "tested":
                if item.get("source_sha256") != record["sha256"]:
                    raise ValueError(f"book-wide tested result needs matching source_sha256: {key}")
            record.update({k: v for k, v in item.items()
                           if k in {"status", "reason", "evidence", "review_scope"}})
            if "source_sha256" in item:
                record["review_source_sha256"] = item["source_sha256"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--results", type=Path, action="append", default=[])
    args = parser.parse_args()
    data = census(ledger.ROOT)
    overlay(data, args.results)
    data["summary"] = {"books": len(data["books"]),
                       "families": dict(Counter(r["family"] for r in data["books"])),
                       "book_statuses": dict(Counter(r["status"] for r in data["books"])),
                       "event_kinds": dict(Counter(e["kind"] for r in data["books"] for e in r["events"])),
                       "event_statuses": dict(Counter(e["status"] for r in data["books"] for e in r["events"]))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(data["summary"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
