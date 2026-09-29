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
  proof-events.json), so they are never merged element-wise: the side that
  changed them wins (theirs when ours is the base's), and when BOTH sides
  changed them ours is kept and the driver prints a `REGENERATE` line naming
  the rows -- the file is then stale until `python3 tools/ledger.py --write`
  runs (a plain text merge, or the old keep-ours rule, left dev's newer
  events behind silently: assurance-hygiene-3, 2026-09-29);
* planning/reach-baseline.json is not id-keyed rows but one mapping
  (`accepted`: "PRF-n:event" -> reason); it merges key by key, three-way,
  with the same field rule (an entry one side removed and the other left
  alone stays removed).

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

RECIPROCITY is the one invariant that spans two of the four files: a proof's
`requirements` in planning/proofs.json and each requirement's
`proof_targets` in planning/requirements.json name the same links
(tools/check_scaffold.py refuses them otherwise).  Git hands a driver one file
at a time, so no per-file merge can keep it; and the recurring breaks were
not merge drops at all (PRF-374, 378, 379 and 383, 2026-09-28: each lane
registered its proof with `requirements` and never added the proof to the
requirement's `proof_targets`).  After a merge or a registration:

    python3 tools/merge_registry.py --reciprocate           # add missing sides
    python3 tools/merge_registry.py --reciprocate --check   # exit 1 if any

The repair is a union: a link either side names is written on both, so it
never drops a link; removing one means removing it from both files.  A link
to an id the other registry does not have is left for check_scaffold to name.

A clone where the driver is not registered merges these files as TEXT,
silently.  `--installed` exits 1 and says how to register it when the
current clone's git config lacks `merge.fn-registry.driver`; `--install`
registers it with a path relative to the work tree (git runs a driver at the
top level), so each clone runs its own tree's driver.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))

GENERATED_FIELDS = {"planning/proofs.json": {"events"}}
KEYED_DOCUMENTS = {"planning/reach-baseline.json": "accepted"}
REGENERATE = {"planning/proofs.json": "python3 tools/ledger.py --write"}
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
            value = generated_value(base.get(key, MISSING), ours.get(key, MISSING),
                                    theirs.get(key, MISSING))
            if value is not MISSING:
                out[key] = value
            continue
        value = merge_value(base.get(key, MISSING), ours.get(key, MISSING),
                            theirs.get(key, MISSING), f"{where} {key}", conflicts)
        if value is not MISSING:
            out[key] = value
    return out


def generated_value(base, ours, theirs):
    """A generated field: the side that changed it; ours when both did."""
    if ours == base and theirs is not MISSING:
        return theirs
    return ours


def stale_generated(base, ours, theirs, path: str) -> list[str]:
    """The ids whose generated fields both sides changed (ours kept: stale)."""
    fields = GENERATED_FIELDS.get(path, set())
    key = rows_key(ours) or rows_key(theirs)
    if not fields or key is None:
        return []
    by = lambda document: {row["id"]: row for row in (
        document.get(key, []) if isinstance(document, dict) else [])}
    base_by, theirs_by = by(base), by(theirs)
    stale = []
    for row in ours.get(key, []):
        other, old = theirs_by.get(row["id"]), base_by.get(row["id"], {})
        if other is None:
            continue
        for field in sorted(fields):
            mine, their = row.get(field, MISSING), other.get(field, MISSING)
            if mine != their and mine != old.get(field, MISSING) \
                    and their != old.get(field, MISSING):
                stale.append(f"{row['id']} {field}")
    return stale


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


def merge_keyed(base: dict, ours: dict, theirs: dict, key: str,
                conflicts: list[str]) -> dict:
    """A document whose KEY maps entry names to values: entry by entry,
    three-way; a conflict names the entry (`CONFLICT PRF-1:ev value: ...`)."""
    merged = merge_mapping(base, ours, theirs, "(top level)", conflicts, skip={key})
    b, o, t = (d.get(key, {}) if isinstance(d.get(key), dict) else {}
               for d in (base, ours, theirs))
    entries: dict = {}
    for name in list(o) + [name for name in t if name not in o]:
        value = merge_value(b.get(name, MISSING), o.get(name, MISSING),
                            t.get(name, MISSING), f"{name} value", conflicts)
        if value is not MISSING:
            entries[name] = value
    merged[key] = entries
    return merged


def merge_documents(base, ours, theirs, path: str) -> tuple[object, list[str]]:
    conflicts: list[str] = []
    if path in KEYED_DOCUMENTS:
        return merge_keyed(base if isinstance(base, dict) else {}, ours, theirs,
                           KEYED_DOCUMENTS[path], conflicts), conflicts
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


REQUIREMENTS = Path("planning/requirements.json")
PROOFS = Path("planning/proofs.json")
DRIVER_KEY = "merge.fn-registry.driver"
DRIVER_COMMAND = "python3 tools/merge_registry.py %O %A %B %P"


def reciprocate(requirements: dict, proofs: dict) -> list[str]:
    """Make requirement `proof_targets` and proof `requirements` name the same
    links by adding each missing side in place; return what was added."""
    req_rows = {row["id"]: row for row in requirements.get("requirements", [])}
    proof_rows = {row["id"]: row for row in proofs.get("proofs", [])}
    added: list[str] = []
    for ident, proof in proof_rows.items():
        for target in proof.get("requirements", []):
            row = req_rows.get(target)
            if row is not None and ident not in row.get("proof_targets", []):
                row.setdefault("proof_targets", []).append(ident)
                added.append(f"{target} proof_targets += {ident}")
    for ident, row in req_rows.items():
        for target in row.get("proof_targets", []):
            proof = proof_rows.get(target)
            if proof is not None and ident not in proof.get("requirements", []):
                proof.setdefault("requirements", []).append(ident)
                added.append(f"{target} requirements += {ident}")
    return added


def reciprocate_main(root: Path, check: bool) -> int:
    paths = (root / REQUIREMENTS, root / PROOFS)
    requirements, proofs = (json.loads(path.read_text(encoding="utf-8")) for path in paths)
    added = reciprocate(requirements, proofs)
    for line in added:
        print(("MISSING " if check else "ADDED ") + line)
    if check:
        print(f"merge_registry --reciprocate --check: {len(added)} one-way link(s)"
              + ("; `merge_registry.py --reciprocate` adds the missing sides" if added else ""))
        return 1 if added else 0
    if added:
        for path, document in zip(paths, (requirements, proofs)):
            path.write_text(json.dumps(document, indent=2, ensure_ascii=False) + "\n",
                            encoding="utf-8")
    print(f"merge_registry --reciprocate: {len(added)} link side(s) added")
    return 0


def git_config(root: Path, *words: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(root), "config", *words], check=False,
                          capture_output=True, text=True)


def installed_main(root: Path, install: bool) -> int:
    if install:
        git_config(root, "merge.fn-registry.name", "fn registry rows, id-keyed three-way")
        git_config(root, DRIVER_KEY, DRIVER_COMMAND)
    driver = git_config(root, "--get", DRIVER_KEY).stdout.strip()
    if not driver or "merge_registry.py" not in driver:
        print(f"merge_registry: NOT REGISTERED in this clone: git merges the registries "
              f"as text (a one-sided link or a lost row is silent). Register it: "
              f"python3 tools/merge_registry.py --install")
        return 1
    print(f"merge_registry: registered: {DRIVER_KEY} = {driver}")
    return 0


def read(path: str):
    text = Path(path).read_text(encoding="utf-8")
    return json.loads(text) if text.strip() else {}


def main(argv: list[str]) -> int:
    if argv in (["--pending"], ["--clear"]):
        return pending_main(argv == ["--clear"])
    if argv in (["--reciprocate"], ["--reciprocate", "--check"]):
        return reciprocate_main(Path.cwd(), "--check" in argv)
    if argv in (["--installed"], ["--install"]):
        return installed_main(Path.cwd(), argv == ["--install"])
    if len(argv) != 4:
        print("usage: merge_registry.py BASE OURS THEIRS PATH  (git's %O %A %B %P)\n"
              "       merge_registry.py --pending | --clear\n"
              "       merge_registry.py --reciprocate [--check]\n"
              "       merge_registry.py --installed | --install",
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
    stale = stale_generated(base, ours, theirs, path)
    if stale:
        print(f"merge_registry: {path}: REGENERATE: both sides changed the generated "
              f"field of {len(stale)} row(s) ({', '.join(stale[:5])}"
              f"{', ...' if len(stale) > 5 else ''}); ours kept, so the file is stale "
              f"until `{REGENERATE.get(path, 'its generator')}` runs", file=sys.stderr)
    for line in claim_notes(base, merged, ours, theirs, conflicts):
        print(f"merge_registry: {path}: {line}", file=sys.stderr)
    rows = merged[rows_key(merged)] if rows_key(merged) else []
    print(f"merge_registry: {path}: {len(rows)} rows, "
          f"{len(conflicts)} conflict(s)", file=sys.stderr)
    return 1 if conflicts else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
