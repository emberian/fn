#!/usr/bin/env python3
"""Widen only the five named C mutation fences after a live source cut.

The fixture pins complete original file identities. --check reverses the five
structural edits and requires byte-for-byte recovery of those originals.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import lisp_rewrite as lr


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tools/fixtures/csnapshot_mutation_fences_before.json"
CORE_OLD = "(equal (mv-nth 0 (fn2-csnapshot-state fn2-core)) *fn2-csnapshot-phase-held*)"
CHILD_OLD = "(= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)"
CORE_NEW = """(stobj-let ((fn2-csnapshot (fn2-core-csnapshot fn2-core)))
  (closed) (fn2-csnapshot-source-closed-p fn2-csnapshot) closed)"""
CHILD_NEW = "(fn2-csnapshot-source-closed-p fn2-csnapshot)"
SPECS = {
    "books/machines-c-bind.lisp": ("fn2-successor-stage", CHILD_OLD, CHILD_NEW),
    "books/machines-c-groups.lisp": ("fn2-groups-genesis", CORE_OLD, CORE_NEW),
    "books/machines-c-sealer-events.lisp": (
        ("fn2-sealer-step", CORE_OLD, CORE_NEW),
        ("fn2-sealer-ready", CORE_OLD, CORE_NEW),
    ),
    "books/startup-genesis.lisp": ("fn2-startup-name-contextp", CORE_OLD, CORE_NEW),
}


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8", "surrogateescape")).hexdigest()


def scoped_match(parsed: lr.Parsed, function: str, pattern: str) -> lr.Match:
    head = "fn2-succ-wrap" if function == "fn2-successor-stage" else "defun"
    definitions = lr.match(f"({head} {function} ?*body)", parsed.forms)
    if len(definitions) != 1:
        raise ValueError(f"{function}: expected one definition, found {len(definitions)}")
    definition = definitions[0]
    matches = [m for m in lr.match(pattern, parsed.forms)
               if definition.start <= m.start and m.end <= definition.end]
    if len(matches) != 1:
        raise ValueError(f"{function}: expected one predicate, found {len(matches)}")
    return matches[0]


def splice(text: str, specs: tuple[tuple[str, str, str], ...], forward: bool) -> str:
    parsed = lr.parse(text)
    edits = []
    for function, old, new in specs:
        found = scoped_match(parsed, function, old if forward else new)
        replacement = new if forward else old
        if "\n" in replacement:
            column = found.start - (text.rfind("\n", 0, found.start) + 1)
            replacement = replacement.replace("\n", "\n" + " " * column)
        edits.append((found.start, found.end, replacement))
    return lr.write(text, edits)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if args.apply == args.check:
        ap.error("choose exactly one of --apply or --check")
    identity = json.loads(FIXTURE.read_text())
    for relative, raw in SPECS.items():
        path = ROOT / relative
        specs = (raw,) if isinstance(raw[0], str) else raw
        text = path.read_text(encoding="utf-8", errors="surrogateescape")
        record = identity[relative]
        if args.apply:
            if digest(text) != record["before_sha256"]:
                raise ValueError(f"{relative}: original identity changed")
            changed = splice(text, specs, True)
            path.write_text(changed, encoding="utf-8", errors="surrogateescape")
            record["after_sha256"] = digest(changed)
        else:
            if digest(text) != record["after_sha256"]:
                raise ValueError(f"{relative}: rewritten identity changed")
            if digest(splice(text, specs, False)) != record["before_sha256"]:
                raise ValueError(f"{relative}: edit did not recover fixed original")
    if args.apply:
        FIXTURE.write_text(json.dumps(identity, indent=2) + "\n")
    print("five scoped mutation fences: identity verified")


if __name__ == "__main__":
    main()
