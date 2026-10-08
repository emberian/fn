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
                  generated teeth, witness `executable`, `instance`, or a world-checked ground `lemma`, the
                  owner book certified at its digest
  wrong_answer    a hypothesis-removal witness (a reachable removal) or an
                  edit mutation, from the same defteeth
  host_test       DECLARED in planning/critical-evidence.json: the entry's
                  :subject is reached by a host line, or a campaign-tied log
                  program whose host sequence and cuts pass their checker; campaign-tied
                  subjects additionally require a native cut-driving test, never only a
                  static verifier. A named
                  test (`tests/...::marker`) exists and mentions the subject
  trace_witness   DECLARED there: a test that produces the state by running
                  the host or its ACL2 step from init and asserts the claim;
                  the tree has no machine record of this yet, so the gate
                  checks only that the named test exists and says so (owed)
  mutation        DECLARED there: an implementation mutation caught by the
                  host test or the theorem; same existence check

A NEW or CHANGED critical keystone (absent from planning/critical-base.json, the gate's own
cutover, or its statement digest differs from the one recorded there) without the whole
package is a HARD FAIL: no ceiling, no ACKS escape.  An EXISTING one without it
must be listed in planning/critical-owed.json with a claimed item id; the list
shrinks only (a name that gained the package, is no longer critical or is new or
changed since the critical base is a finding).  Redundant hypotheses are not detected here
(tools/premise_audit.py finds unestablished premises, not redundant ones): owed.

    python3 tools/keystone_critical.py --report        # classes, examples, package status
    python3 tools/keystone_critical.py --write-critical-base   # the cutover, once
    python3 tools/keystone_critical.py --lower-stale           # shrink the owed and base rows
    python3 tools/keystone_critical.py --lower-complete        # remove fully evidenced owed rows
    python3 tools/keystone_critical.py --claim-owed    # claim items for unlisted existing criticals
"""
from __future__ import annotations

import argparse
import ast
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
CBASE = ROOT / "planning/critical-base.json"
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


def _native_campaign_problem(ref: str, root: Path) -> str | None:
    """Source check for a native cut driver, not a runtime test verdict.

    Follow calls within the named Python module from the declared function.
    A static cut-map verifier alone cannot reach a native process launch.
    """
    path, marker = ref.split("::", 1)
    if not re.fullmatch(r"tests/(?:campaign/native_|test_native_)[\w]+\.py", path):
        return "campaign-tied subject requires a native campaign host_test"
    try:
        tree = ast.parse((root / path).read_text(encoding="utf-8"))
    except (OSError, SyntaxError) as error:
        return f"cannot inspect native campaign: {error}"
    functions: dict[str, list] = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions.setdefault(node.name, []).append(node)
    if marker not in functions:
        return "native host_test marker must name the cut-driving function"
    pending, seen, launches, selects = [marker], set(), False, False
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        for function in functions.get(name, []):
            nodes = list(function.body)
            while nodes:
                node = nodes.pop()
                # A docstring or an uncalled nested definition is not execution.
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    continue
                if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant):
                    continue
                nodes.extend(ast.iter_child_nodes(node))
                if isinstance(node, ast.Call):
                    callee = node.func
                    called = callee.id if isinstance(callee, ast.Name) else getattr(callee, "attr", None)
                    if called in functions:
                        pending.append(called)
                    if (isinstance(callee, ast.Attribute) and isinstance(callee.value, ast.Name)
                            and callee.value.id == "subprocess" and callee.attr in ("run", "Popen")):
                        launches = True
                    if any(k.arg == "fault" for k in node.keywords):
                        selects = True
                if (isinstance(node, ast.Constant) and isinstance(node.value, str)
                        and "FN_NATIVE_" in node.value and "FAULT" in node.value):
                    selects = True
    if not launches or not selects:
        return "native host_test does not drive fault cuts through a native process"
    return None


def package(entry: dict, declared: dict | None, reachable, root: Path = ROOT) -> dict[str, str | None]:
    """Each part to None (met) or why it is not."""
    out: dict[str, str | None] = {}
    if entry.get("class") != "generated":
        out["premises"] = out["wrong_answer"] = "no defteeth/defkeystone teeth"
    else:
        # defteeth accepts a ground lemma only when its world formula equals
        # the CLOSED full premise-and-conclusion conjunction. It establishes
        # satisfiability even for non-executable crash-image predicates.
        # Reachability still needs the separate trace_witness declaration.
        if entry.get("witness") not in ("executable", "instance", "lemma"):
            out["premises"] = "no executable/instance/ground-lemma positive witness"
        elif not entry.get("certified"):
            out["premises"] = "positive witness book is not certified at its current closure key"
        else:
            out["premises"] = None
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
            out["host_test"] = f"{subject} is reached by no host line or checked log campaign (reach_check)"
        elif getattr(reachable, "campaign_tied", lambda s: False)(subject):
            out["host_test"] = _native_campaign_problem(declared["host_test"], root)
    return out


def missing(pkg: dict) -> list[str]:
    return [f"{part} ({why})" for part, why in pkg.items() if why]


# --------------------------------------------------------------------------
# the gate
# --------------------------------------------------------------------------

ITEM = re.compile(r"^PRF-\d{3,}$")


def findings(current: dict[str, dict], cbase: dict | None, declared: dict, owed: dict,
             reachable, root: Path = ROOT) -> tuple[list[str], dict]:
    """(findings, summary).  CBASE is planning/critical-base.json's `entries`
    (name -> class, statement_digest): the gate's own cutover.  NEW is absent
    from it, CHANGED has a different statement digest; both need the whole
    package.  Everything else in it is existing debt, owed with an item."""
    problems: list[str] = []
    if cbase is None:
        return ["critical gate: planning/critical-base.json is missing; "
                "python3 tools/keystone_critical.py --write-critical-base (once)"], \
            {"critical": 0, "complete": 0, "new_or_changed": 0, "owed": 0, "by_class": {}}
    critical = {n: e for n, e in current.items() if e.get("critical")}
    summary = {"critical": len(critical), "complete": 0, "new_or_changed": 0,
               "owed": 0, "by_class": {}}
    for name, entry in sorted(critical.items()):
        summary["by_class"][entry["critical"]] = summary["by_class"].get(entry["critical"], 0) + 1
        pkg = package(entry, declared.get(name), reachable, root)
        lacking = missing(pkg)
        old = cbase.get(name)
        if old is None:
            kind = "new"
        elif old.get("statement_digest") != entry.get("statement_digest"):
            kind = "changed"
        else:
            kind = "existing"
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
    for name in sorted(set(owed) & set(critical)):
        if name not in cbase or cbase[name].get("statement_digest") != critical[name].get("statement_digest"):
            problems.append(f"critical gate: {name} is new or changed since the critical base and "
                            f"cannot be owed: it ships with its package")
    for name in sorted(set(declared) - set(critical)):
        problems.append(f"critical gate: planning/critical-evidence.json declares {name}, which "
                        f"is not a critical registry keystone")
    return problems, summary


def load_critical_base() -> dict | None:
    try:
        return json.loads(CBASE.read_text(encoding="utf-8"))["entries"]
    except (OSError, ValueError, KeyError):
        return None


def write_critical_base(current: dict[str, dict]) -> int:
    """The cutover, written ONCE: the critical set now, with statement digests.
    Never rewritten (a second run refuses); names leave it by hand-free
    shrinkage only when a keystone stops being critical."""
    if CBASE.exists():
        print(f"{CBASE.name} exists: the critical base is written once")
        return 1
    entries = {n: {"class": e["critical"], "statement_digest": e["statement_digest"]}
               for n, e in sorted(current.items()) if e.get("critical")}
    CBASE.write_text(json.dumps({
        "about": "The critical gate's cutover (Ruling 22): the critical keystones that existed "
                 "when the gate landed, with statement digests. A critical keystone absent from "
                 "this file, or with a different digest, is new or changed and needs the whole "
                 "evidence package; the rest are existing debt owed in planning/critical-owed.json. "
                 "Generated once by tools/keystone_critical.py --write-critical-base.",
        "entries": entries}, indent=1) + "\n", encoding="utf-8")
    print(f"wrote {CBASE.name} ({len(entries)} critical keystones)")
    return 0


def lower_stale(current: dict[str, dict], cbase: dict, owed: dict) -> tuple[dict, dict, dict[str, list[str]]]:
    """Shrink-only: (cbase, owed, dropped-by-class) without the rows whose
    keystone is gone from the registry or no longer critical.  Never adds or
    edits a row; a result that held a row the inputs lacked is refused."""
    live = {n for n, e in current.items() if e.get("critical")}
    dropped: dict[str, list[str]] = {}
    new_base = {n: r for n, r in cbase.items() if n in live}
    new_owed = {n: r for n, r in owed.items() if n in live}
    for table, kept, rows in (("base", new_base, cbase), ("owed", new_owed, owed)):
        for n in rows:
            if n not in kept:
                dropped.setdefault(f"{table}:{rows[n].get('class', '?')}", []).append(n)
    if not (set(new_base) <= set(cbase) and set(new_owed) <= set(owed)):
        raise ValueError("lower-stale would add a row")
    return new_base, new_owed, dropped


def lower_stale_main(write: bool = True) -> int:
    _, current = _current()
    cbase, owed = load_critical_base(), load_owed()
    if cbase is None:
        print("planning/critical-base.json is missing")
        return 1
    new_base, new_owed, dropped = lower_stale(current, cbase, owed)
    for key, names in sorted(dropped.items()):
        print(f"dropped {len(names)} {key}")
    if not dropped:
        print("nothing stale")
        return 0
    if write:
        base_doc = json.loads(CBASE.read_text(encoding="utf-8"))
        base_doc["entries"] = new_base
        CBASE.write_text(json.dumps(base_doc, indent=1) + "\n", encoding="utf-8")
        owed_doc = json.loads(OWED.read_text(encoding="utf-8"))
        owed_doc["items"] = new_owed
        OWED.write_text(json.dumps(owed_doc, indent=1) + "\n", encoding="utf-8")
        print(f"wrote {CBASE.name} ({len(new_base)}) and {OWED.name} ({len(new_owed)})")
    return 0


def lower_complete(current, owed, declared, reachable, root=ROOT):
    """Drop only fully evidenced rows; preserve every retained row verbatim."""
    complete = {n for n in owed if n in current and current[n].get("critical")
                and not missing(package(current[n], declared.get(n), reachable, root))}
    return {n: row for n, row in owed.items() if n not in complete}, sorted(complete)


def retire_line(name: str, entry: dict, declared: dict) -> str:
    """The witness files a retired owed row stands on (coordinator, 2026-10-08:
    a row leaves critical-owed only when the tool finds its package, naming
    them)."""
    parts = [f"premises/wrong_answer {entry.get('owner_book') or '?'}"]
    for key in ("host_test", "trace_witness", "mutation"):
        parts.append(f"{key} {declared.get(key) or '?'}")
    return f"completed {name}: " + "; ".join(parts)


def lower_complete_main() -> int:
    ke, current = _current()
    owed = load_owed()
    books = sorted({current[n]["owner_book"] for n in owed if n in current
                    and current[n].get("owner_book")})
    certified = ke.certified_books(books)
    for entry in current.values():
        entry["certified"] = certified.get(entry.get("owner_book"), False)
    declared = load_declared()
    kept, dropped = lower_complete(current, owed, declared, lazy_reachable())
    for name in dropped:
        print(retire_line(name, current[name], declared.get(name) or {}))
    if dropped:
        doc = json.loads(OWED.read_text(encoding="utf-8"))
        doc["items"] = kept
        doc["about"] = ("Existing critical keystones that lack the evidence package, each owned by a claimed item "
                        "(tools/keystone_critical.py --claim-owed). Shrink-only: --lower-stale removes obsolete rows; "
                        "--lower-complete removes only rows whose full package passes with current-closure certification. "
                        "New or changed critical keystones cannot be owed.")
        OWED.write_text(json.dumps(doc, indent=1) + "\n", encoding="utf-8")
    print(f"lower-complete: {len(dropped)} removed, {len(kept)} retained")
    return 0


def load_declared() -> dict:
    return _load(EVIDENCE, "entries")


def load_owed() -> dict:
    return _load(OWED, "items")


def lazy_reachable():
    graph = []
    checked_programs: dict[str, bool] = {}

    def reachable(subject: str) -> bool:
        if not graph:
            import reach_check
            graph.append(reach_check.Graph())
        if subject in graph[0].reachable:
            return True
        # The host implements these model programs as I/O, rather than
        # calling their Lisp list constructors. Require both reach_check's
        # campaign tie and the existing source-to-model sequence/cut check.
        if subject not in graph[0].tied:
            return False
        from tests.campaign import native_cuts
        if subject not in native_cuts.LOG_PROGRAM_HOSTS and subject != "fn-lg-open-program":
            return False
        if subject not in checked_programs:
            try:
                if subject == "fn-lg-open-program":
                    native_cuts.verify_recovery_order()
                    valid = not native_cuts.verify_log_route_arms()
                else:
                    native_cuts.verify_log_cut_map()
                    valid = True
            except (AssertionError, OSError, ValueError):
                valid = False
            checked_programs[subject] = valid
        return checked_programs[subject]
    def campaign_tied(subject: str) -> bool:
        reachable(subject)  # initialize the same graph and correspondence checks
        return subject not in graph[0].reachable and subject in graph[0].tied

    reachable.campaign_tied = campaign_tied
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
    cbase = load_critical_base() or {}
    declared, owed, reach = load_declared(), load_owed(), lazy_reachable()
    groups: dict[tuple[str, str], list[str]] = {}
    for name, entry in sorted(current.items()):
        if not entry.get("critical") or name in owed:
            continue
        if cbase.get(name, {}).get("statement_digest") != entry.get("statement_digest"):
            continue  # new or changed since the critical base: ships with its package
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
    parser.add_argument("--lower-stale", action="store_true",
                        help="drop owed and critical-base rows whose keystone is gone or no "
                             "longer critical (shrink-only; never adds a row)")
    parser.add_argument("--lower-complete", action="store_true",
                        help="drop only owed rows whose full package currently passes")
    parser.add_argument("--write-critical-base", action="store_true",
                        help="write planning/critical-base.json once (the gate's cutover)")
    parser.add_argument("--lane", default=Path.cwd().name)
    args = parser.parse_args(argv)
    if args.lower_complete:
        return lower_complete_main()
    if args.lower_stale:
        return lower_stale_main()
    if args.write_critical_base:
        return write_critical_base(_current()[1])
    if args.claim_owed:
        return claim_owed(args.lane, args.write)
    report()
    return 0


if __name__ == "__main__":
    sys.exit(main())
