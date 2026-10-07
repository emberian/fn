#!/usr/bin/env python3
"""File a TEETH-OWED repair item for each keystone the teeth gate calls new
and untoothed (tools/keystone_emit.py, the finding "KEYSTONE is new (not in
the base ...) and has no generated teeth").

The coordinator's ruling (CONVERGE-2 row 32): such a keystone does not block,
but each needs an owed record.  The record is the repair item
planning/repair/items/TEETH-OWED-<KEYSTONE UPPERCASED>.json (category
`teeth-owed`, field `keystone` the exact name); the gate reads the open ones
(keystone_emit.owed_items) and counts those keystones as owed instead of
failing on them.  The item leaves the list when its state is closed
(landed, refuted, duplicate); the gate demands that once teeth exist.

    python3 tools/teeth_owed_file.py            # the plan: what would be filed
    python3 tools/teeth_owed_file.py --write    # file it

Only that one class is handled.  A name the tool cannot file is REFUSED with a
named reason and listed as the residual (exit 1); nothing else is touched.
Idempotent: a keystone with an open item is left alone.  Owner: the lane the
book's header names ("(lane NAME"), else "unassigned".
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "planning/repair"))
import keystone_emit  # noqa: E402
import ledger  # noqa: E402
import repair  # noqa: E402

HEAD_CHARS = 200


def item_id(name: str) -> str:
    return "TEETH-OWED-" + name.upper()


def book_owner(root: Path, book: str) -> str:
    """The lane a book's header comment names, else `unassigned`."""
    try:
        text = (root / book).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return "unassigned"
    for line in text.splitlines()[:40]:
        match = re.search(r"\(lane ([A-Za-z0-9][A-Za-z0-9_-]*)", line)
        if match:
            return match.group(1)
    return "unassigned"


def theorem_sites(tree: ledger.Tree) -> dict[str, "ledger.Theorem"]:
    sites: dict[str, ledger.Theorem] = {}
    for _, book in sorted(tree.books.items()):
        for theorem in book.theorems:
            if not theorem.local:
                sites.setdefault(theorem.name.lower(), theorem)
    return sites


def plan(current: dict[str, dict], base: dict | None, sites: dict, open_items: dict,
         root: Path, closed_ids: dict[str, str] | None = None) -> tuple[list[dict], list[tuple[str, str]], list[str]]:
    """(items to file, refusals as (name, reason), names already filed)."""
    if base is None:
        return [], [("*", "no protected base: the gate fails closed, so there is no "
                          "`new` class to file")], []
    to_file: list[dict] = []
    refused: list[tuple[str, str]] = []
    present: list[str] = []
    for name in keystone_emit.untoothed_new(current, base):
        entry = current[name]
        if name in open_items:
            present.append(name)
            continue
        if item_id(name) in (closed_ids or {}):
            refused.append((name, f"{item_id(name)} exists in state "
                                  f"{closed_ids[item_id(name)]}: reopen it by hand "
                                  f"(repair.py set), the tool never overwrites an item"))
            continue
        if not entry.get("registry"):
            refused.append((name, "not a registry keystone (only a registry event is a "
                                  "keystone; an owed row with no defteeth is another class)"))
            continue
        if entry.get("owed_by"):
            refused.append((name, f"owed by {entry['owed_by']} ({entry.get('owed_in')}) with no "
                                  f"defteeth: a different class, the generator's own debt"))
            continue
        theorem = sites.get(name.lower())
        if theorem is None:
            refused.append((name, "no non-local defthm/defthmd of that name in books/ "
                                  "or tests/acl2/ (a generated event?): no book:line to cite"))
            continue
        head = keystone_emit.render(theorem.statement)
        head = head if len(head) <= HEAD_CHARS else head[:HEAD_CHARS] + " ..."
        to_file.append({
            "id": item_id(name), "state": "open", "category": keystone_emit.OWED_CATEGORY,
            "keystone": name, "file": theorem.book, "line": theorem.line,
            "owner": book_owner(root, theorem.book), "severity": "low",
            "source": "TEETH-GATE",
            "title": f"{name} is a new registry keystone with no generated teeth: declare "
                     f"(defteeth {name} ...) in a tests/acl2 book",
            "detail": f"keystone {name}; {theorem.book}:{theorem.line}; statement: {head}; "
                      f"owed because it is absent from the teeth gate's protected base and "
                      f"no defteeth declares it (CONVERGE-2 ruling 5: owed, not blocking). "
                      f"Close with state=landed once the defteeth lands.",
            "notes": []})
    return to_file, refused, present


def existing_states(directory: Path) -> dict[str, str]:
    """id -> state of every item file in DIRECTORY."""
    states: dict[str, str] = {}
    for path in sorted(directory.glob("*.json")):
        try:
            item = json.loads(path.read_text(encoding="utf-8"))
        except ValueError:
            continue
        states[str(item.get("id"))] = str(item.get("state"))
    return states


def file_items(items: list[dict], directory: Path) -> None:
    repair.ITEMS = str(directory)
    for item in items:
        repair.save(item)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help="file the items (default: plan)")
    arguments = parser.parse_args(argv)
    tree = ledger.load_tree(lazy=True)
    current = keystone_emit.obligations(tree, {})
    base, why = keystone_emit.base_manifest()
    if base is None:
        print(f"teeth_owed_file: {why}")
        return 1
    to_file, refused, present = plan(current, base, theorem_sites(tree),
                                     keystone_emit.owed_items(), keystone_emit.ROOT,
                                     existing_states(keystone_emit.OWED_ITEMS))
    if arguments.write:
        file_items(to_file, keystone_emit.OWED_ITEMS)
    for item in to_file:
        print(f"teeth_owed_file: {'filed' if arguments.write else 'would file'} "
              f"{item['id']} (owner {item['owner']}, {item['file']}:{item['line']})")
    print(f"teeth_owed_file: {len(to_file)} {'filed' if arguments.write else 'to file'}, "
          f"{len(present)} already owed, {len(refused)} refused")
    for name, reason in refused:
        print(f"teeth_owed_file: REFUSED {name}: {reason}")
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main())
