#!/usr/bin/env python3
"""Ruling 22: critical keystones gate their use.

A registry keystone is CRITICAL when tools/keystone_critical_map.json maps it
to one of seven classes (durability, authorization, identity-binding,
ownership-reclamation, resource-reservation, parser-boundary, extraction) by
its BOOK and the definterface entry that cites it.  The class is computed from
the tree and the map, never typed per keystone; tools/keystone_emit.py records
it in planning/teeth-obligations.json (`critical`, `statement_digest`) and its
--check applies the gate below.  Single source of truth: the map plus the tree.

THE EVIDENCE PACKAGE (deputy P's five parts), per critical keystone:

  premises        a positive defteeth witness asserting the whole antecedent:
                  generated teeth, witness `executable` or `instance`, the
                  owner book certified at its digest
  wrong_answer    a hypothesis-removal witness (a reachable removal) or an
                  edit mutation, from the same defteeth
  host_test       DECLARED in planning/critical-evidence.json: the entry's
                  :subject is reached by a host line (reach_check) and a named
                  test (`tests/...::marker`) exists and mentions the subject
  trace_witness   DECLARED there: a test that produces the state by running
                  the host or its ACL2 step from init and asserts the claim;
                  the tree has no machine record of this yet, so the gate
                  checks only that the named test exists and says so (owed)
  mutation        DECLARED there: an implementation mutation caught by the
                  host test or the theorem; same existence check

A NEW or CHANGED critical keystone (absent from the protected base, or its
statement/claim digest differs from the base entry's digest) without the whole
package is a HARD FAIL: no ceiling, no ACKS escape.  An EXISTING one without it
must be listed in planning/critical-owed.json with a claimed item id; the list
shrinks only (a name that gained the package, is no longer critical or is not
in the base is a finding).  Redundant hypotheses are not detected here
(tools/premise_audit.py finds unestablished premises, not redundant ones): owed.

    python3 tools/keystone_critical.py --report        # classes, examples, package status
    python3 tools/keystone_critical.py --claim-owed    # claim items for unlisted existing criticals
"""
from __future__ import annotations

import argparse
import fnmatch
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT = Path(__file__).resolve().parents[1]
MAP = ROOT / "tools/keystone_critical_map.json"
EVIDENCE = ROOT / "planning/critical-evidence.json"
OWED = ROOT / "planning/critical-owed.json"
INTERFACES = ROOT / "planning/interfaces.json"
PARTS = ("premises", "wrong_answer", "host_test", "trace_witness", "mutation")
DECLARED = ("host_test", "trace_witness", "mutation")
ROW_KEYS = {"class", "book", "theorem", "interface_class", "subsystem", "extraction", "why"}


def load_map(path: Path = MAP) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    classes = set(data["classes"])
    for index, row in enumerate(data["rows"]):
        unknown = set(row) - ROW_KEYS
        if unknown or row.get("class") not in classes or not row.get("why"):
            raise ValueError(f"{path}: row {index} is malformed ({sorted(unknown)}, "
                             f"class {row.get('class')!r}, why required)")
    return data


def interface_index(path: Path = INTERFACES) -> dict[str, list[dict]]:
    """Each keystone theorem to the interface entries citing it."""
    index: dict[str, list[dict]] = {}
    for entry in json.loads(path.read_text(encoding="utf-8"))["entries"]:
        for keystone in entry.get("keystones", []):
            index.setdefault(keystone["theorem"], []).append(entry)
    return index


def _globs(patterns, value: str) -> bool:
    return any(fnmatch.fnmatchcase(value, pattern) for pattern in patterns)


def row_matches(row: dict, name: str, book: str, interfaces: list[dict]) -> bool:
    if "book" in row and not _globs(row["book"], book):
        return False
    if "theorem" in row and not _globs(row["theorem"], name):
        return False
    wants = {key: row[key] for key in ("interface_class", "subsystem") if key in row}
    if "extraction" in row:
        wants["extraction"] = row["extraction"]
    if not wants:
        return True
    for entry in interfaces:
        if all((bool(entry.get("extraction")) == wants["extraction"]) if key == "extraction"
               else entry.get(key.replace("interface_class", "class")) == value
               for key, value in wants.items()):
            return True
    return False


def classify(name: str, book: str | None, interfaces: list[dict], rows: list[dict]) -> str | None:
    """The first matching row's class; None is noncritical (also for a keystone
    whose book is unknown: it cannot be mapped)."""
    if book is None:
        return None
    for row in rows:
        if row_matches(row, name, book, interfaces):
            return row["class"]
    return None


def classify_all(names_books: dict[str, str | None], interfaces: dict[str, list[dict]],
                 mapping: dict) -> dict[str, str]:
    out = {}
    for name, book in names_books.items():
        cls = classify(name, book, interfaces.get(name, []), mapping["rows"])
        if cls:
            out[name] = cls
    return out


# --------------------------------------------------------------------------
# the package
# --------------------------------------------------------------------------


def _load(path: Path, key: str) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8")).get(key, {})
    except (OSError, ValueError):
        return {}


def _ref_problem(ref, subject: str | None, root: Path) -> str | None:
    """A declared test ref `tests/...::marker` must name a file under tests/
    that contains the marker (and, for a host test, the subject)."""
    if not isinstance(ref, str) or "::" not in ref:
        return "not a `tests/PATH::MARKER` reference"
    path, marker = ref.split("::", 1)
    if not path.startswith("tests/") or ".." in path or not marker:
        return "not under tests/"
    try:
        text = (root / path).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return f"{path} does not exist"
    if marker not in text:
        return f"{marker!r} does not occur in {path}"
    if subject and subject not in text:
        return f"{path} never mentions the subject {subject}"
    return None


def package(entry: dict, declared: dict | None, reachable, root: Path = ROOT) -> dict[str, str | None]:
    """Each part to None (met) or why it is not."""
    out: dict[str, str | None] = {}
    if entry.get("class") != "generated":
        out["premises"] = out["wrong_answer"] = "no defteeth/defkeystone teeth"
    else:
        out["premises"] = (None if entry.get("witness") in ("executable", "instance")
                           and entry.get("certified")
                           else "no certified executable/instance positive witness")
        removals = entry.get("removals", {})
        out["wrong_answer"] = (None if removals.get("reachable") or
                               str(entry.get("mutations", "")).startswith("edits:")
                               else "no reachable removal or edit mutation")
    declared = declared or {}
    subject = declared.get("subject") or entry.get("subject")
    for part in DECLARED:
        ref = declared.get(part)
        if ref is None:
            out[part] = "not declared in planning/critical-evidence.json"
        else:
            out[part] = _ref_problem(ref, subject if part == "host_test" else None, root)
    if out["host_test"] is None:
        if not subject:
            out["host_test"] = "no :subject declared"
        elif not reachable(subject):
            out["host_test"] = f"{subject} is reached by no host line (reach_check)"
    return out


def missing(pkg: dict) -> list[str]:
    return [f"{part} ({why})" for part, why in pkg.items() if why]


# --------------------------------------------------------------------------
# the gate
# --------------------------------------------------------------------------

ITEM = re.compile(r"^PRF-\d{3,}$")


def findings(current: dict[str, dict], base: dict | None, declared: dict, owed: dict,
             reachable, root: Path = ROOT) -> tuple[list[str], dict]:
    """(findings, summary).  CURRENT entries carry `critical` (and
    `statement_digest`); a base entry may carry them too."""
    problems: list[str] = []
    base_entries = {e["name"]: e for e in (base or {}).get("entries", [])}
    critical = {n: e for n, e in current.items() if e.get("critical")}
    summary = {"critical": len(critical), "complete": 0, "new_or_changed": 0,
               "owed": 0, "by_class": {}}
    for name, entry in sorted(critical.items()):
        summary["by_class"][entry["critical"]] = summary["by_class"].get(entry["critical"], 0) + 1
        pkg = package(entry, declared.get(name), reachable, root)
        lacking = missing(pkg)
        old = base_entries.get(name)
        if base is None:
            kind = "new"
        elif old is None:
            kind = "new"
        else:
            was = old.get("statement_digest")
            now = entry.get("statement_digest")
            claim_changed = (old.get("claim_digest") and entry.get("claim_digest")
                             and old["claim_digest"] != entry["claim_digest"])
            kind = "changed" if (was and now and was != now) or claim_changed else "existing"
        if not lacking:
            summary["complete"] += 1
            if name in owed:
                problems.append(f"critical gate: {name} now has the whole package: remove it "
                                f"from planning/critical-owed.json in this commit")
            continue
        if kind in ("new", "changed"):
            summary["new_or_changed"] += 1
            problems.append(f"critical gate: {kind} {entry['critical']} keystone {name} lacks "
                            f"the evidence package (HARD FAIL, no ceiling): " + "; ".join(lacking))
        else:
            row = owed.get(name)
            if not row or not ITEM.match(str(row.get("item", ""))):
                problems.append(f"critical gate: existing {entry['critical']} keystone {name} "
                                f"lacks the evidence package and has no owed item in "
                                f"planning/critical-owed.json (tools/keystone_critical.py "
                                f"--claim-owed)")
            else:
                summary["owed"] += 1
    for name in sorted(set(owed) - set(critical)):
        problems.append(f"critical gate: {name} is in planning/critical-owed.json and is no "
                        f"longer a critical registry keystone: remove it")
    if base is not None:
        for name in sorted(set(owed) & set(critical)):
            if name not in base_entries:
                problems.append(f"critical gate: {name} is new and cannot be owed: a new "
                                f"critical keystone ships with its package")
    for name in sorted(set(declared) - set(critical)):
        problems.append(f"critical gate: planning/critical-evidence.json declares {name}, which "
                        f"is not a critical registry keystone")
    return problems, summary


def load_declared() -> dict:
    return _load(EVIDENCE, "entries")


def load_owed() -> dict:
    return _load(OWED, "items")


def lazy_reachable():
    graph = []

    def reachable(subject: str) -> bool:
        if not graph:
            import reach_check
            graph.append(reach_check.Graph())
        return subject in graph[0].reachable
    return reachable


# --------------------------------------------------------------------------
# reporting and owed items
# --------------------------------------------------------------------------


def _current():
    import keystone_emit as ke
    import ledger
    tree = ledger.load_tree(lazy=True)
    return ke, ke.obligations(tree, {})


def report(examples: int = 5) -> None:
    ke, current = _current()
    critical = {n: e for n, e in current.items() if e.get("critical")}
    counts: dict[str, list[str]] = {}
    for name, entry in sorted(critical.items()):
        counts.setdefault(entry["critical"], []).append(name)
    registry = [e for e in current.values() if e["registry"]]
    print(f"{len(critical)} critical of {len(registry)} registry keystones")
    for cls in load_map()["classes"]:
        names = counts.get(cls, [])
        print(f"{cls}: {len(names)}")
        for name in names[:examples]:
            print(f"    {name}  ({current[name].get('book')})")


def claim_owed(lane: str, write: bool) -> int:
    """One claimed PRF item per class for the existing criticals that lack the
    package and have no owed row; planning/critical-owed.json maps each
    keystone to its class's item (and records its book)."""
    import subprocess
    ke, current = _current()
    base, why = ke.base_manifest()
    base_names = {e["name"] for e in (base or {}).get("entries", [])}
    declared, owed, reach = load_declared(), load_owed(), lazy_reachable()
    groups: dict[tuple[str, str], list[str]] = {}
    for name, entry in sorted(current.items()):
        if not entry.get("critical") or name in owed:
            continue
        if base is not None and name not in base_names:
            continue  # new since the base: ships with its package, cannot be owed
        if not missing(package(entry, declared.get(name), reach)):
            continue
        groups.setdefault(entry["critical"], []).append(name)
    print(f"{sum(map(len, groups.values()))} unowned existing criticals in {len(groups)} class items")
    if not write:
        for cls, names in sorted(groups.items()):
            print(f"  {cls}: {len(names)}")
        return 0
    registry = json.loads(ke.PROOFS.read_text(encoding="utf-8"))
    for cls, names in sorted(groups.items()):
        done = subprocess.run(
            [sys.executable, str(ROOT / "tools/next_id.py"), "claim", "PRF", "--lane", lane,
             "--note", f"critical evidence package ({cls}) for {len(names)} existing keystone(s)"],
            capture_output=True, text=True, check=True)
        item = re.search(r"PRF-\d{3,}", done.stdout).group(0)
        registry["proofs"].append({
            "id": item,
            "title": f"Critical evidence package for the existing {cls} keystones",
            "statement": (f"Ruling 22: the {len(names)} existing {cls} keystones listed under "
                          f"this item in planning/critical-owed.json gain the "
                          f"evidence package (tools/keystone_critical.py): positive witness, "
                          f"wrong-answer witness, host-path test, trace-derived witness, "
                          f"implementation mutation."),
            "milestone": "M4", "requirements": [], "depends_on": [], "assumptions": [],
            "status": "planned", "evidence": ["planning/critical-owed.json"]})
        for name in names:
            owed[name] = {"class": cls, "item": item, "book": current[name].get("book")}
    ke.PROOFS.write_text(json.dumps(registry, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    OWED.write_text(json.dumps({
        "about": "Existing critical keystones that lack the evidence package, each owned by a "
                 "claimed item (tools/keystone_critical.py --claim-owed). Shrink-only: delete a "
                 "name when it gains the package; a new or changed critical keystone cannot be "
                 "listed here.", "items": dict(sorted(owed.items()))}, indent=1) + "\n",
        encoding="utf-8")
    print(f"wrote {OWED.relative_to(ROOT)} ({len(owed)} keystones)")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", action="store_true")
    parser.add_argument("--claim-owed", action="store_true")
    parser.add_argument("--write", action="store_true", help="with --claim-owed: claim and write")
    parser.add_argument("--lane", default=Path.cwd().name)
    args = parser.parse_args(argv)
    if args.claim_owed:
        return claim_owed(args.lane, args.write)
    report()
    return 0


if __name__ == "__main__":
    sys.exit(main())
