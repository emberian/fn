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
  id collision and a conflict, and BOTH rows stay (ours first) so resolving
  it by `git add` cannot lose either side's row;
* within a row, each field merges three-way against the base: the side that
  changed it wins; when both changed a list, the result is ours plus the
  elements theirs added (an element ours removed stays removed); when both
  changed anything else differently, that is a real conflict;
* proofs.json `events` arrays are generated (tools/ledger.py --write from
  proof-events.json), so ours is kept and the caller regenerates.

The claims ledger (tools/next_id.py, build/coordinator/id-claims.jsonl) is
read after the merge: a row the merge adds whose id nobody claimed is named
UNCLAIMED, and an id collision names the lane that claimed the number.
Neither changes the merge or its exit code.

A real conflict leaves ours for that field, names every one on stderr
(`CONFLICT PRF-212 status: ours 'proved' theirs 'open'`), and exits 1, so git
marks the file conflicted.  That non-zero exit IS the intended behaviour: git
then refuses to commit the merge until someone resolves the file.  The file
stays valid JSON either way -- which is the trap: `git add` of a JSON file
that parses "resolves" it with OURS for every conflicted field, and the
stderr lines scroll away (batch AY's obstruction report).  So every conflict
is also appended, one JSON object per line, to the CONFLICT RECORD

    build/merge-conflicts/registry.jsonl      (FN_REGISTRY_CONFLICTS moves it)

under the repository the merge runs in (git runs a driver at the work tree's
top level): {"path", "id", "field", "detail", "ours_kept": true, "time"}.
The batch runner reads it after every merge:

    python3 tools/merge_registry.py --pending   # print them; exit 1 if any
    python3 tools/merge_registry.py --clear     # after resolving them (moves
                                                # the record to *.resolved-<time>)

A merge whose record is non-empty is not finished, whatever `git status`
says.  The driver's own exit stays 1 on any conflict, so a scripted merge
(build/coordinator/merge_lane.sh) stops too.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))

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
    collided: set = set()
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
            # Both rows stay, ours first: keeping only ours lost the other
            # side's row whenever the conflict was resolved by `git add`
            # (compact-arena and log-2 lost dev's rows that way, 2026-09-27).
            conflicts.append(f"CONFLICT {ident}: both sides added this id with "
                             "different rows (an id collision: renumber one; "
                             "both rows kept, ours first)")
            out.append(row)
            out.append(theirs_by[ident])
            collided.add(ident)
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
        if row["id"] in seen and row["id"] not in collided:
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


def claim_notes(base, merged, ours, theirs, conflicts: list[str]) -> list[str]:
    """What the id-claims ledger says of the rows this merge adds.

    tools/next_id.py hands out ids from build/coordinator/id-claims.jsonl.
    A row the merge adds whose id nobody claimed is named (UNCLAIMED: the
    lane took a number by hand); a collision names who claimed the number,
    which is the side that keeps it.  Neither changes the merge: the ledger
    is evidence for the person resolving it, and a merge on a box with no
    ledger says so once.
    """
    try:
        import next_id  # noqa: PLC0415 (a sibling tool; the driver runs from tools/)
        next_id.ledger_path, next_id.claims_by_id  # noqa: B018 (an older next_id has neither)
    except (ImportError, AttributeError):
        return []
    path = next_id.ledger_path(Path.cwd())
    if path is None or not path.is_file():
        return ["NOTE no id-claims ledger here; claims not checked"]
    claims = next_id.claims_by_id(next_id.read_ledger(path))
    key = rows_key(merged)
    before = {row["id"] for row in (base.get(key, []) if isinstance(base, dict) else [])}
    notes: list[str] = []
    for row in merged.get(key, []):
        ident = row["id"]
        if ident in before or not next_id.parse_id(ident):
            continue
        claim = claims.get(ident)
        if claim is None:
            side = ("theirs" if ident not in {r["id"] for r in ours.get(key, [])}
                    else "ours")
            notes.append(f"UNCLAIMED {ident} ({side}): no row in {path.name}; "
                         "`next_id.py claim` takes a free id to renumber to")
    for line in conflicts:
        match = next_id.re.match(r"CONFLICT (\S+): both sides added", line)
        if match and match.group(1) in claims:
            claim = claims[match.group(1)]
            notes.append(f"CLAIMED {match.group(1)} by {claim.get('lane')} "
                         f"({claim.get('note')}): the other side renumbers")
    return notes


CONFLICT_RECORD = Path("build/merge-conflicts/registry.jsonl")
CONFLICT_LINE = re.compile(r"CONFLICT (.+?): (.*)\Z", re.S)


def record_path() -> Path:
    """The conflict record: FN_REGISTRY_CONFLICTS, else build/merge-conflicts/
    registry.jsonl under the current directory (git runs a merge driver at
    the work tree's top level)."""
    configured = os.environ.get("FN_REGISTRY_CONFLICTS", "")
    return Path(configured) if configured else Path.cwd() / CONFLICT_RECORD


def conflict_records(path: str, conflicts: list[str]) -> list[dict]:
    """Each CONFLICT line as {path, id, field, detail}: `CONFLICT PRF-212
    status: ...' is id PRF-212, field status; a row-level conflict (an id
    collision, a deleted-and-changed row) has field ""."""
    out = []
    stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    for line in conflicts:
        match = CONFLICT_LINE.match(line)
        where, detail = (match.group(1), match.group(2)) if match else ("?", line)
        if where.startswith("(top level)"):
            ident, field = "(top level)", where[len("(top level)"):].strip()
        else:
            ident, _, field = where.partition(" ")
        out.append({"path": path, "id": ident, "field": field.strip(), "detail": detail,
                    "ours_kept": True, "time": stamp})
    return out


def append_record(records: list[dict]) -> Path | None:
    """Append RECORDS to the conflict record; None when it cannot be written
    (then the driver says so, and its exit is still 1)."""
    target = record_path()
    try:
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("a", encoding="utf-8") as handle:
            for entry in records:
                handle.write(json.dumps(entry, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return None
    return target


def pending() -> list[dict]:
    target = record_path()
    if not target.is_file():
        return []
    entries = []
    for line in target.read_text(encoding="utf-8").splitlines():
        if line.strip():
            entries.append(json.loads(line))
    return entries


def pending_main(clear: bool) -> int:
    entries = pending()
    target = record_path()
    for entry in entries:
        field = f" {entry['field']}" if entry.get("field") else ""
        print(f"UNRESOLVED {entry['path']}: {entry['id']}{field}: {entry['detail']} "
              f"(ours kept, {entry['time']})")
    if clear:
        if entries:
            stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
            target.rename(target.with_name(target.name + ".resolved-" + stamp))
        print(f"merge_registry --clear: {len(entries)} conflict(s) marked resolved")
        return 0
    print(f"merge_registry --pending: {len(entries)} unresolved registry field "
          f"conflict(s) in {target}")
    return 1 if entries else 0


def read(path: str):
    text = Path(path).read_text(encoding="utf-8")
    return json.loads(text) if text.strip() else {}


def main(argv: list[str]) -> int:
    if argv in (["--pending"], ["--clear"]):
        return pending_main(argv == ["--clear"])
    if len(argv) != 4:
        print("usage: merge_registry.py BASE OURS THEIRS PATH  (git's %O %A %B %P)\n"
              "       merge_registry.py --pending | --clear",
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
    if conflicts:
        written = append_record(conflict_records(path, conflicts))
        print(f"merge_registry: {path}: {len(conflicts)} conflict(s) "
              + (f"recorded in {written}; `merge_registry.py --pending` lists them"
                 if written else "NOT recorded (the conflict record is not writable)"),
              file=sys.stderr)
    for line in claim_notes(base, merged, ours, theirs, conflicts):
        print(f"merge_registry: {path}: {line}", file=sys.stderr)
    rows = merged[rows_key(merged)] if rows_key(merged) else []
    print(f"merge_registry: {path}: {len(rows)} rows, "
          f"{len(conflicts)} conflict(s)", file=sys.stderr)
    return 1 if conflicts else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
