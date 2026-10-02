#!/usr/bin/env python3
"""The registry half of `defkeystone`: rows and subjects from the forms.

`(defkeystone NAME TERM :subject FN [:id "PRF-NNN"] [:restates K] ...)`
(books/defkeystone.lisp) admits a keystone with its teeth.  This reads every
such form in books/ and tests/acl2/ with the ledger's non-evaluating reader
(nothing is interned, evaluated or macro-expanded) and keeps the registry in
step with it:

* the REGISTRY KEYSTONE is K when the form restates a source theorem
  (the form checks, in ACL2, that the two formulas are equal), else NAME;
* the row named by :id must exist in planning/proofs.json, and the curated
  map planning/proof-events.json must cite the registry keystone for it
  (`--write` adds the citation; tools/ledger.py --write then regenerates
  the row's `events`);
* the row's `keystone_subjects` maps each defkeystone's registry keystone to
  its :subject.  It is GENERATED here: `--write` writes it, `--check` fails
  when it differs, and nothing else edits it;
* the subject must be one of the functions the keystone's conclusion calls
  as tools/reach_check.py reads it (`Subject`), and a host line must reach
  it (`Graph.reachable`).  The first host file that calls it directly is
  printed with the line, found by tools/current_view.py's `host_call`; a
  subject reached only through book functions says so;
* `:id :test` marks a test of the macro itself, which is skipped;
* TEETH COVERAGE (the ratchet).  Every registry event (planning/proofs.json
  `events`) either has GENERATED teeth -- a `(table fn-teeth 'NAME ...)` row
  the ledger read from a `defkeystone` or `defteeth` form -- or HAND teeth,
  the comment-convention sections tools/teeth_check.py counts as a floor.
  tools/teeth_baseline.json holds the hand count and ONLY SHRINKS: `--check`
  fails when more registry keystones have hand teeth than the baseline says
  (a new keystone declares its teeth), `--write-baseline` lowers it and
  refuses to raise it.  A `(table fn-teeth-owed 'NAME ...)` row (a
  generator's debt) with no fn-teeth row anywhere fails `--check` outright;
* a form with no :id is a NEW keystone: `--write --claim --milestone M4
  --title "..."` claims a PRF id through tools/next_id.py, adds a planned
  row and prints the `:id` to add to the form (the Lisp source is never
  rewritten by a tool).

    python3 tools/keystone_emit.py            # report every form
    python3 tools/keystone_emit.py --check    # exit 1 on any finding (make check)
    python3 tools/keystone_emit.py --write    # proof-events citations, keystone_subjects
    python3 tools/keystone_emit.py --write --claim --milestone M4 --title T --lane L

Counts stay generated elsewhere (tools/ledger.py, tools/current_view.py);
this writes no count.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger  # noqa: E402
from ledger import Sym, head  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "planning/proofs.json"
PROOF_EVENTS = ROOT / "planning/proof-events.json"
TEETH_BASELINE = ROOT / "tools/teeth_baseline.json"
CONTAINERS = {"local", "progn", "encapsulate", "with-output", "defsection"}


def render(form: object) -> str:
    if isinstance(form, Sym):
        return str(form)
    if isinstance(form, str):
        return '"' + form.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(form, list):
        if head(form) == "quote" and len(form) == 2:
            return "'" + render(form[1])
        return "(" + " ".join(render(item) for item in form) + ")"
    return str(form)


def forms_in(root: Path = ROOT) -> list[tuple[str, int, list]]:
    """(book, line, form) for every defkeystone in books/ and tests/acl2/."""
    found: list[tuple[str, int, list]] = []

    def walk(book: str, form: object, line: int) -> None:
        name = head(form)
        if name == "defkeystone":
            found.append((book, line, form))
        elif name in CONTAINERS:
            for item in form[1:]:
                walk(book, item, line)

    for directory in ("books", "tests/acl2"):
        for path in sorted((root / directory).glob("*.lisp")):
            text = path.read_text(encoding="utf-8", errors="replace")
            if "defkeystone" not in text:
                continue
            try:
                forms = ledger.Reader(text).top_level()
            except ledger.ReadError:
                continue
            book = path.relative_to(root).as_posix()
            for form, line in forms:
                walk(book, form, line)
    return found


class Keystone:
    def __init__(self, book: str, line: int, form: list) -> None:
        self.book, self.line, self.form = book, line, form
        self.parts = ledger.defkeystone_parts(form)
        self.name = str(form[1]) if len(form) > 1 else "?"

    @property
    def where(self) -> str:
        return f"{self.book}:{self.line}"

    @property
    def registry_name(self) -> str:
        restates = self.parts["restates"] if self.parts else None
        return str(restates) if restates is not None else self.name

    @property
    def ident(self) -> str | None:
        ident = self.parts["id"] if self.parts else None
        return str(ident) if isinstance(ident, str) and not isinstance(ident, Sym) else None

    @property
    def subject(self) -> str:
        return str(self.parts["subject"]) if self.parts else "?"


def host_line(subject: str, root: Path = ROOT) -> str | None:
    """`file:line` of the first host file that calls SUBJECT directly."""
    import current_view
    for path in sorted((root / "host").rglob("*.lisp")):
        relative = path.relative_to(root).as_posix()
        try:
            return f"{relative}:{current_view.host_call(root, subject, relative)}"
        except current_view.ViewError:
            continue
    return None


def subject_findings(keystones: list[Keystone]) -> tuple[list[str], dict[str, str]]:
    """Findings on subjects, and each registry keystone's host line (or how
    it is reached)."""
    import reach_check
    graph = reach_check.Graph()
    theorems = reach_check.theorem_forms(graph.books)
    problems: list[str] = []
    reached: dict[str, str] = {}
    for keystone in keystones:
        name = keystone.registry_name
        entry = theorems.get(name.lower())
        text = entry[1] if entry else render([Sym("defthm"), Sym(name),
                                              keystone.parts["term"]])
        subject = reach_check.Subject(graph, name.lower(), text)
        if keystone.subject not in subject.functions:
            problems.append(
                f"{keystone.where}: {keystone.name}: :subject {keystone.subject} is not "
                f"a function {name}'s conclusion calls (reach_check reads "
                f"{', '.join(sorted(subject.functions)) or 'nothing'})")
            continue
        if keystone.subject not in graph.reachable:
            problems.append(
                f"{keystone.where}: {keystone.name}: :subject {keystone.subject} is "
                f"reached by no host line (reach_check)")
            continue
        line = host_line(keystone.subject)
        reached[name] = line or "reached through book functions only"
    return problems, reached


def registry_findings(keystones: list[Keystone], write: bool) -> list[str]:
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    curated = json.loads(PROOF_EVENTS.read_text(encoding="utf-8"))
    rows = {row["id"]: row for row in registry["proofs"]}
    targets = {target["id"]: target for target in curated["targets"]}
    wanted: dict[str, dict[str, str]] = {}
    problems: list[str] = []
    for keystone in keystones:
        ident = keystone.ident
        if ident is None:
            problems.append(f"{keystone.where}: {keystone.name}: no :id; a new "
                            f"keystone claims one with --write --claim")
            continue
        if ident not in rows:
            problems.append(f"{keystone.where}: {keystone.name}: :id {ident} is not "
                            f"a row of planning/proofs.json")
            continue
        wanted.setdefault(ident, {})[keystone.registry_name] = keystone.subject
        target = targets.get(ident)
        cited = {event.get("name") for event in (target or {}).get("events", [])}
        if keystone.registry_name not in cited:
            if write:
                if target is None:
                    target = {"id": ident, "events": []}
                    curated["targets"].append(target)
                    targets[ident] = target
                target["events"].append({"kind": "theorem",
                                         "name": keystone.registry_name})
            else:
                problems.append(f"{keystone.where}: {ident} does not cite "
                                f"{keystone.registry_name} in planning/proof-events.json")
    for ident, row in rows.items():
        current = row.get("keystone_subjects")
        target = wanted.get(ident)
        if current == target or (current is None and target is None):
            continue
        if write:
            if target is None:
                row.pop("keystone_subjects", None)
            else:
                row["keystone_subjects"] = dict(sorted(target.items()))
        else:
            problems.append(f"{ident}: keystone_subjects is {current!r}, the "
                            f"defkeystone forms say {target!r}; run --write")
    if write:
        PROOFS.write_text(json.dumps(registry, indent=2, ensure_ascii=False) + "\n",
                          encoding="utf-8")
        PROOF_EVENTS.write_text(json.dumps(curated, indent=2, ensure_ascii=False) + "\n",
                                encoding="utf-8")
    return problems


def teeth_coverage() -> dict:
    """Registry keystones by how their teeth are written, and the generators'
    unmet debts: {"generated": [...], "hand": [...], "unmet": [(name, book)]}."""
    tree = ledger.load_tree(lazy=True)
    events = {event["name"] for target in json.loads(
        PROOFS.read_text(encoding="utf-8"))["proofs"] for event in target.get("events", [])}
    declared: set[str] = set()
    owed: dict[str, str] = {}
    for book in tree.books.values():
        declared |= book.teeth_declared
        for name in book.teeth_owed:
            owed.setdefault(name, book.path)
    return {"generated": sorted(events & declared),
            "hand": sorted(events - declared),
            "unmet": sorted((name, book) for name, book in owed.items()
                            if name not in declared)}


def teeth_findings(write_baseline: bool) -> list[str]:
    coverage = teeth_coverage()
    problems = [f"{book}: {name} owes its teeth (table fn-teeth-owed) and no "
                f"defteeth/defkeystone declares them" for name, book in coverage["unmet"]]
    hand = len(coverage["hand"])
    baseline = (json.loads(TEETH_BASELINE.read_text(encoding="utf-8"))["hand_toothed"]
                if TEETH_BASELINE.exists() else None)
    if write_baseline:
        if baseline is not None and hand > baseline:
            problems.append(f"teeth baseline: {hand} registry keystones have hand teeth, "
                            f"the baseline is {baseline}; it only shrinks")
        else:
            TEETH_BASELINE.write_text(json.dumps({
                "about": "Registry keystones (planning/proofs.json events) whose teeth "
                         "are hand-written, not a defkeystone/defteeth row; tools/"
                         "keystone_emit.py --check refuses a rise, --write-baseline "
                         "lowers it.",
                "hand_toothed": hand}, indent=1) + "\n", encoding="utf-8")
    elif baseline is None:
        problems.append("tools/teeth_baseline.json is missing; run --write-baseline")
    elif hand > baseline:
        problems.append(f"{hand} registry keystones have hand teeth, the baseline is "
                        f"{baseline}: a new keystone declares its teeth (defteeth NAME "
                        f"...) in its test book, or lower the count on purpose")
    print(f"keystone_emit: teeth coverage: {len(coverage['generated'])} registry "
          f"keystones with generated teeth, {hand} with hand teeth (baseline "
          f"{baseline}), {len(coverage['unmet'])} unmet debt(s)")
    return problems


def claim(keystone: Keystone, lane: str, milestone: str, title: str) -> str:
    """Claim a PRF id for a new keystone and add its planned row."""
    answer = subprocess.run(
        [sys.executable, str(ROOT / "tools/next_id.py"), "claim", "PRF", "--lane", lane,
         "--note", f"defkeystone {keystone.name} ({keystone.book})"],
        capture_output=True, text=True, check=True)
    match = re.search(r"PRF-\d{3,}", answer.stdout)
    if not match:
        raise SystemExit(f"keystone_emit: next_id.py claim printed no id: {answer.stdout}")
    ident = match.group(0)
    registry = json.loads(PROOFS.read_text(encoding="utf-8"))
    registry["proofs"].append({
        "id": ident, "title": title,
        "statement": (f"{keystone.registry_name} (defkeystone {keystone.name}, "
                      f"{keystone.book}); subject {keystone.subject}."),
        "milestone": milestone, "requirements": [], "depends_on": [],
        "assumptions": [], "status": "planned", "evidence": [keystone.book]})
    PROOFS.write_text(json.dumps(registry, indent=2, ensure_ascii=False) + "\n",
                      encoding="utf-8")
    return ident


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--claim", action="store_true",
                        help="with --write: claim an id for each form with none")
    parser.add_argument("--milestone")
    parser.add_argument("--title")
    parser.add_argument("--lane", default=Path.cwd().name)
    parser.add_argument("--write-baseline", action="store_true",
                        help="lower tools/teeth_baseline.json to the hand-toothed count")
    arguments = parser.parse_args(argv)

    keystones = [Keystone(book, line, form) for book, line, form in forms_in()]
    # `:id :test` marks a test of the macro itself (tests/acl2/defkeystone-
    # tests.lisp), not a registry keystone.
    keystones = [k for k in keystones
                 if not (k.parts and isinstance(k.parts["id"], Sym)
                         and str(k.parts["id"]) == ":test")]
    refused = [k for k in keystones if k.parts is None]
    wellformed = [k for k in keystones if k.parts is not None]
    problems = [f"{k.where}: {k.name}: the form is one books/defkeystone.lisp "
                f"refuses (certification names the reason)" for k in refused]
    if arguments.write and arguments.claim:
        for keystone in wellformed:
            if keystone.ident is None:
                if not (arguments.milestone and arguments.title):
                    raise SystemExit("keystone_emit: --claim needs --milestone and --title")
                ident = claim(keystone, arguments.lane, arguments.milestone,
                              arguments.title)
                print(f"{keystone.where}: claimed {ident}; add  :id \"{ident}\"  to "
                      f"(defkeystone {keystone.name} ...)")
    subject_problems, reached = subject_findings(wellformed)
    problems += subject_problems
    problems += registry_findings(wellformed, arguments.write)
    problems += teeth_findings(arguments.write_baseline)

    if not (arguments.check and not problems):
        for keystone in wellformed:
            names = ledger.defkeystone_names(keystone.parts)
            print(f"{keystone.where}: {keystone.name} -> {keystone.ident or '(no id)'} "
                  f"{keystone.registry_name}; subject {keystone.subject} "
                  f"({reached.get(keystone.registry_name, 'unresolved')}); "
                  f"{len(names['without'])} removal, {len(names['mutant'])} mutant")
    for problem in problems:
        print(f"keystone_emit: {problem}")
    print(f"keystone_emit: {len(keystones)} defkeystone form(s) in "
          f"{len({k.book for k in keystones})} book(s), {len(problems)} finding(s)")
    return 1 if (arguments.check and problems) else 0


if __name__ == "__main__":
    sys.exit(main())
