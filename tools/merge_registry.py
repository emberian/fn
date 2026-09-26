#!/usr/bin/env python3
"""Git merge driver for fn's id-keyed JSON registries.

    git config merge.fn-registry.name "fn registry rows, id-keyed three-way"
    git config merge.fn-registry.driver \
        "python3 /Users/ember/dev/fn/tools/merge_registry.py %O %A %B %P"

`.gitattributes` routes planning/proofs.json, planning/requirements.json,
planning/proof-events.json and tests/scenarios/catalog.json here.  Each is an
object whose one list of rows carries an `id` per row.  A text merge
conflicts whenever two branches append rows at the same end of that list,
which is every merge of two lanes that each took an id: 65 conflicted merges
on 2026-09-25/26, resolved by hand or by build/coordinator/merge_*.py run one
file at a time (friction review 2026-09-26 section 7).  This is those
scripts' rule, once, for all four files:

* rows are matched by `id`; ours keep their order and theirs' new ids are
  appended in theirs' order; a row one side deleted and the other left
  unchanged stays deleted; an id both sides added with different rows is an
  id collision and a conflict;
* within a row, each field merges three-way against the base: the side that
  changed it wins; when both changed a list, the result is ours plus the
  elements theirs added (an element ours removed stays removed); when both
  changed anything else differently, that is a real conflict;
* proofs.json `events` arrays are generated (tools/ledger.py --write from
  proof-events.json), so ours is kept and the caller regenerates.

A real conflict leaves ours for that field, names every one on stderr
(`CONFLICT PRF-212 status: ours 'proved' theirs 'open'`), and exits 1, so git
marks the file conflicted.  The file stays valid JSON either way.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys

GENERATED_FIELDS = {"planning/proofs.json": {"events"}}
MISSING = object()


def rows_key(document: object) -> str | None:
    """The top-level key holding the id-keyed rows."""
    if not isinstance(document, dict):
        return None
    for key, value in document.items():
        if isinstance(value, list) and value and all(
                isinstance(row, dict) and "id" in row for row in value):
            return key
    return None


def merge_list(base: list, ours: list, theirs: list) -> list:
    """Ours, plus what theirs added since base; what ours removed stays out."""
    out = list(ours)
    for element in theirs:
        if element not in out and element not in base:
            out.append(element)
    return out


def merge_value(base, ours, theirs, where: str, conflicts: list[str]):
    if ours == theirs:
        return ours
    if theirs == base:
        return ours
    if ours == base:
        return theirs
    if isinstance(ours, list) and isinstance(theirs, list):
        return merge_list(base if isinstance(base, list) else [], ours, theirs)
    if isinstance(ours, dict) and isinstance(theirs, dict):
        return merge_mapping(base if isinstance(base, dict) else {}, ours, theirs,
                             where, conflicts)
    conflicts.append(f"CONFLICT {where}: ours {short(ours)} theirs {short(theirs)}"
                     f" base {short(base)}")
    return ours


def merge_mapping(base: dict, ours: dict, theirs: dict, where: str,
                  conflicts: list[str], skip: set[str] = frozenset()) -> dict:
    out: dict = {}
    for key in list(ours) + [key for key in theirs if key not in ours]:
        if key in skip:
            if key in ours:
                out[key] = ours[key]
            continue
        value = merge_value(base.get(key, MISSING), ours.get(key, MISSING),
                            theirs.get(key, MISSING), f"{where} {key}", conflicts)
        if value is not MISSING:
            out[key] = value
    return out


def short(value) -> str:
    if value is MISSING:
        return "(absent)"
    text = json.dumps(value, ensure_ascii=False)
    return text if len(text) <= 80 else text[:77] + "..."


def merge_rows(base: list, ours: list, theirs: list, skip: set[str],
               conflicts: list[str]) -> list:
    base_by = {row["id"]: row for row in base}
    ours_by = {row["id"]: row for row in ours}
    theirs_by = {row["id"]: row for row in theirs}
    out = []
    for row in ours:
        ident = row["id"]
        if ident not in theirs_by:
            if ident in base_by and base_by[ident] == row:
                continue  # theirs deleted it and ours did not touch it
            out.append(row)
            continue
        if ident not in base_by and row != theirs_by[ident]:
            # Both sides took this id for different rows: an id collision,
            # not an edit.  One of them must be renumbered.
            conflicts.append(f"CONFLICT {ident}: both sides added this id with "
                             "different rows (an id collision: renumber one; "
                             "ours kept)")
            out.append(row)
            continue
        out.append(merge_mapping(base_by.get(ident, {}), row, theirs_by[ident],
                                 ident, conflicts, skip))
    for row in theirs:
        ident = row["id"]
        if ident in ours_by:
            continue
        if ident in base_by:
            if base_by[ident] != row:
                conflicts.append(f"CONFLICT {ident}: ours deleted the row, theirs "
                                 "changed it (kept deleted)")
            continue
        out.append(row)
    seen: set = set()
    for row in out:
        if row["id"] in seen:
            conflicts.append(f"CONFLICT {row['id']}: duplicate id after merge")
        seen.add(row["id"])
    return out


def merge_documents(base, ours, theirs, path: str) -> tuple[object, list[str]]:
    conflicts: list[str] = []
    key = rows_key(ours) or rows_key(theirs) or rows_key(base)
    if key is None:
        raise ValueError(f"{path}: no id-keyed list of rows")
    skip = GENERATED_FIELDS.get(path, set())
    base = base if isinstance(base, dict) else {}
    merged = merge_mapping(base, ours, theirs, "(top level)", conflicts,
                           skip={key})
    merged[key] = merge_rows(base.get(key, []), ours.get(key, []),
                             theirs.get(key, []), skip, conflicts)
    return merged, conflicts


def read(path: str):
    text = Path(path).read_text(encoding="utf-8")
    return json.loads(text) if text.strip() else {}


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print("usage: merge_registry.py BASE OURS THEIRS PATH  (git's %O %A %B %P)",
              file=sys.stderr)
        return 2
    base_file, ours_file, theirs_file, path = argv
    try:
        base, ours, theirs = read(base_file), read(ours_file), read(theirs_file)
        merged, conflicts = merge_documents(base, ours, theirs, path)
    except (OSError, ValueError) as error:
        # Leave git's own conflict handling to the caller: ours is untouched.
        print(f"merge_registry: {path}: cannot merge: {error}", file=sys.stderr)
        return 1
    Path(ours_file).write_text(json.dumps(merged, indent=2, ensure_ascii=False) + "\n",
                               encoding="utf-8")
    for line in conflicts:
        print(f"merge_registry: {path}: {line}", file=sys.stderr)
    rows = merged[rows_key(merged)] if rows_key(merged) else []
    print(f"merge_registry: {path}: {len(rows)} rows, "
          f"{len(conflicts)} conflict(s)", file=sys.stderr)
    return 1 if conflicts else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
