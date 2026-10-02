#!/usr/bin/env python3
"""The registry half of `defkeystone`, and the TEETH GATE (contract v1).

`(defkeystone NAME TERM :subject FN [:id "PRF-NNN"] [:restates K] ...)` and
`(defteeth NAME :claim ... :subject FN ...)` (books/defkeystone.lisp) declare
a keystone's teeth.  This reads every such form in books/ and tests/acl2/
with the ledger's non-evaluating reader (nothing is interned, evaluated or
macro-expanded) and keeps the registry and the OBLIGATION MANIFEST in step
with it:

* the REGISTRY KEYSTONE of a defkeystone is K when the form restates a
  source theorem (the form checks, in ACL2, that the two formulas are
  equal), else NAME; the row named by :id must exist in planning/proofs.json
  and the curated map planning/proof-events.json must cite the registry
  keystone for it (`--write` adds the citation; tools/ledger.py --write then
  regenerates the row's `events`); the row's `keystone_subjects` is
  GENERATED here; the subject must be a function the keystone's conclusion
  calls as tools/reach_check.py reads it, reached from a host line;
  `:id :test` marks a test of the macro itself, which is skipped;

* THE GATE.  planning/teeth-obligations.json holds one entry per registry
  event (planning/proofs.json `events`, deduplicated by name) and per
  `(table fn-teeth-owed 'NAME ...)` row a generator emitted: its class
  (`generated`: a defteeth/defkeystone form declares its teeth, read from
  the form, never from a bare table; `hand`: none does), the owner book and
  that book's digest, the claim's digest, the subject, the witness mode, the
  removal kinds (reachable / logical / lemma), the mutation class (edits,
  not-applicable, deferred), each bound (attained, derived), whether an owed
  row is met (claim, subject and bounds EQUAL), whether the owner book is
  CERTIFIED at its digest (green_check's verdict from an archived manifest:
  a form earns credit only there), and `complete`.  The manifest is
  regenerated from the tree and compared with the committed one and with
  the PROTECTED BASE: planning/teeth-base.json names an externally selected
  immutable revision whose manifest `git show` yields; a missing base or
  revision FAILS CLOSED (no HEAD fallback).  Findings: a base `generated`
  entry no longer generated (a downgrade); a name absent from the base that
  is not generated (a new keystone declares its teeth); a new `deferred`
  exemption (rejected by default; a base deferred is grandfathered); an
  owed row not met; a stale committed manifest.  Counts are printed from
  the sets: coverage counts only certified generated entries whose
  removals are all reachable, whose mutations are edits and whose bounds
  are derived; everything else is counted debt by class.

* `--write` (the registry: citations and `keystone_subjects`) and
  `--write-manifest` (the gate's manifest) each VALIDATE FULLY FIRST and
  write nothing while their own gate has a finding other than the staleness
  they repair; a finding of the other gate is reported and exits nonzero but
  does not hold the write hostage (the registry's subject debt is older
  than the manifest).  Neither writes planning/teeth-base.json: the runner
  moves the base at integration.  `--write-manifest --bootstrap` writes the
  FIRST manifest when neither a base nor a manifest exists, never again.

    python3 tools/keystone_emit.py            # report; exit 1 on a finding
    python3 tools/keystone_emit.py --check    # the same (make check)
    python3 tools/keystone_emit.py --write    # citations, keystone_subjects
    python3 tools/keystone_emit.py --write-manifest   # the gate's manifest
    python3 tools/keystone_emit.py --write --claim --milestone M4 --title T --lane L

Counts stay generated elsewhere (tools/ledger.py, tools/current_view.py);
this writes no count.
"""
from __future__ import annotations

import argparse
import hashlib
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
MANIFEST = ROOT / "planning/teeth-obligations.json"
BASE = ROOT / "planning/teeth-base.json"
CONTAINERS = {"local", "progn", "encapsulate", "with-output", "defsection"}


def render(form: object) -> str:
    if isinstance(form, Sym):
        return str(form)
    if isinstance(form, str):
        return '"' + form.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(form, list):
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
    """The citation and keystone_subjects findings; with WRITE, the writes
    (the caller validates everything before passing write=True)."""
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


# --------------------------------------------------------------------------
# the obligation manifest
# --------------------------------------------------------------------------


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _owed_met(parts: dict, row: list) -> bool:
    """The declared PARTS state what the owed ROW asks: the same claim and
    subject, every owed bound with the same terms and :rests-on."""
    owed = ledger.keyword_plist(row)
    if owed.get(":claim") != parts["claim"]:
        return False
    if ":subject" in owed and owed[":subject"] != parts["subject"]:
        return False
    for kind in (":visits", ":allocation"):
        for entry in ledger._dk_nil(owed.get(kind, [])) or []:
            if not isinstance(entry, list) or len(entry) < 2:
                return False
            rests = set(map(str, ledger._dk_nil(ledger.keyword_plist(entry[2:]).get(
                ":rests-on", [])) or []))
            stated = any(e[1] == entry[0] and e[2] == entry[1]
                         and set(map(str, ledger._dk_nil(ledger.keyword_plist(e[3:]).get(
                             ":rests-on", [])) or [])) == rests
                         for e in parts[kind[1:]])
            if not stated:
                return False
    return True


def obligations(tree: ledger.Tree, certified: dict[str, bool] | None = None) -> dict[str, dict]:
    """The manifest's entries by name (see the module docstring)."""
    events: set[str] = set()
    for target in json.loads(PROOFS.read_text(encoding="utf-8"))["proofs"]:
        events |= set(target.get("events", []))
    declared: dict[str, tuple[str, dict]] = {}
    owed: dict[str, tuple[str, list]] = {}
    for path, book in sorted(tree.books.items()):
        for name, parts in book.teeth_declared.items():
            declared.setdefault(name, (path, parts))
        for name, row in book.teeth_owed.items():
            owed.setdefault(name, (path, row))
    entries: dict[str, dict] = {}
    for name in sorted(events | set(declared) | set(owed)):
        entry: dict = {"name": name, "registry": name in events,
                       "class": "generated" if name in declared else "hand"}
        if name in owed:
            entry["owed_by"] = str(ledger.keyword_plist(owed[name][1]).get(":by", "?"))
            entry["owed_in"] = owed[name][0]
        if name in declared:
            book, parts = declared[name]
            entry["owner_book"] = book
            entry["book_digest"] = _digest((ROOT / book).read_text(encoding="utf-8"))
            entry["claim_digest"] = _digest(ledger.source_text(parts["claim"]))
            entry["subject"] = str(parts["subject"]) if parts["subject"] is not None else None
            entry["witness"] = "lemma" if ":witness-lemma" in parts["options"] else "executable"
            kinds = [str(ledger._dk_witness_kind(ledger.keyword_plist(
                parts["breaks"][str(label)][2:]))).lstrip(":") for label in parts["labels"]]
            entry["removals"] = {kind: kinds.count(kind)
                                 for kind in ("reachable", "logical", "lemma")}
            entry["mutations"] = (parts["exemption"].lstrip(":") if parts["exemption"]
                                  else f"edits:{len(parts['mutations'])}")
            entry["bounds"] = [{"label": str(e[0]), "kind": kind.lstrip(":"),
                                "attained": ":attains" in ledger.keyword_plist(e[3:]),
                                "derived": ":derived-by" in ledger.keyword_plist(e[3:])}
                               for kind in (":visits", ":allocation") for e in parts[kind[1:]]]
            entry["owed_met"] = _owed_met(parts, owed[name][1]) if name in owed else None
            entry["certified"] = (certified or {}).get(book)
            entry["complete"] = bool(
                entry["certified"]
                and entry["removals"]["logical"] == 0 and entry["removals"]["lemma"] == 0
                and entry["witness"] == "executable"
                and entry["mutations"].startswith("edits:")
                and all(b["derived"] for b in entry["bounds"])
                and entry["owed_met"] is not False)
        else:
            entry["complete"] = False
        entries[name] = entry
    return entries


def certified_books(books: list[str]) -> dict[str, bool]:
    """Whether each BOOK is green at its current digest and closure from an
    archived manifest (green_check.green_at_these_bytes, the one meaning of
    certified)."""
    if not books:
        return {}
    import green_check
    roots = [book[:-5] if book.endswith(".lisp") else book for book in books]
    report = green_check.audit(ROOT, roots=roots)
    records = report.get("books_by_verdict", {})
    return {book: green_check.green_at_these_bytes(records.get(root))
            for book, root in zip(books, roots)}


def base_manifest() -> tuple[dict | None, str]:
    """The protected base's manifest and the revision it names, or (None,
    why): a missing base file or revision fails closed."""
    if not BASE.exists():
        return None, "planning/teeth-base.json is missing (the base is an externally " \
                     "selected immutable revision; fail closed)"
    try:
        revision = str(json.loads(BASE.read_text(encoding="utf-8"))["revision"])
    except (ValueError, KeyError, TypeError) as error:
        return None, f"planning/teeth-base.json is unreadable: {error}"
    done = subprocess.run(["git", "-C", str(ROOT), "show",
                           f"{revision}:planning/teeth-obligations.json"],
                          capture_output=True, text=True, check=False)
    if done.returncode != 0:
        return None, f"the base revision {revision[:12]} has no planning/teeth-obligations.json" \
                     f" ({done.stderr.strip()[:80]})"
    try:
        return json.loads(done.stdout), revision
    except ValueError as error:
        return None, f"the base manifest at {revision[:12]} is unreadable: {error}"


def manifest_findings(current: dict[str, dict], base: dict | None, why: str,
                      committed: dict | None) -> list[str]:
    problems: list[str] = []
    if base is None:
        return [f"teeth gate: {why}"]
    base_entries = {entry["name"]: entry for entry in base.get("entries", [])}
    for name, entry in sorted(current.items()):
        old = base_entries.get(name)
        if old is None:
            if entry["class"] != "generated":
                problems.append(f"teeth gate: {name} is new (not in the base {base.get('revision', '?')[:12]}) "
                                f"and has no generated teeth: declare them (defteeth {name} ...)")
            elif entry.get("mutations") == "deferred":
                problems.append(f"teeth gate: {name} is new and defers its mutation: a new "
                                f":deferred exemption is rejected (give a checked edit, or "
                                f":not-applicable with its reason)")
            continue
        if old["class"] == "generated" and entry["class"] != "generated":
            problems.append(f"teeth gate: {name} had generated teeth in the base and has none "
                            f"now (a downgrade)")
        if (old.get("mutations", "").startswith("edits:") and entry.get("mutations") == "deferred"):
            problems.append(f"teeth gate: {name} had edit mutations in the base and defers "
                            f"them now (a downgrade)")
        if entry["class"] == "generated" and entry.get("owed_met") is False:
            problems.append(f"teeth gate: {name}'s teeth do not state what {entry.get('owed_by')} "
                            f"owes (claim, subject or a bound differs)")
    for name, entry in sorted(current.items()):
        if entry["class"] == "generated" and entry.get("owed_met") is False \
                and name not in base_entries:
            problems.append(f"teeth gate: {name}'s teeth do not state what {entry.get('owed_by')} "
                            f"owes (claim, subject or a bound differs)")
    if committed is None:
        problems.append("teeth gate: planning/teeth-obligations.json is missing; run --write")
    elif committed.get("entries") != sorted(current.values(), key=lambda e: e["name"]):
        problems.append("teeth gate: planning/teeth-obligations.json is stale; run --write")
    return problems


def manifest_counts(current: dict[str, dict]) -> str:
    registry = [e for e in current.values() if e["registry"]]
    generated = [e for e in registry if e["class"] == "generated"]
    certified = [e for e in generated if e.get("certified")]
    complete = [e for e in registry if e["complete"]]
    return (f"keystone_emit: teeth gate: {len(registry)} registry keystones: "
            f"{len(generated)} with generated teeth ({len(certified)} certified at their "
            f"digest, {len(complete)} complete), {len(registry) - len(generated)} hand; "
            f"debt: {sum(1 for e in generated if e.get('mutations') == 'deferred')} deferred, "
            f"{sum(1 for e in generated if e.get('mutations') == 'not-applicable')} not-applicable, "
            f"{sum(1 for e in generated if e.get('removals', {}).get('logical'))} with logical "
            f"removals, {sum(1 for e in generated if e.get('witness') == 'lemma')} lemma witnesses, "
            f"{sum(1 for e in generated for b in e.get('bounds', []) if not b['derived'])} underived "
            f"bounds, {sum(1 for e in generated for b in e.get('bounds', []) if not b['attained'])} "
            f"unattained bounds, {sum(1 for e in current.values() if e.get('owed_by'))} owed "
            f"({sum(1 for e in current.values() if e.get('owed_met') is False)} unmet)")


def gate(write: bool, bootstrap: bool = False) -> list[str]:
    """The teeth gate's findings; with WRITE and no finding but staleness,
    the manifest is written.  BOOTSTRAP (the first manifest ever, before a
    base exists) writes it when the base is the only finding and says so
    loudly: the base file is then committed by hand, naming the revision
    that holds this manifest."""
    tree = ledger.load_tree(lazy=True)
    books = sorted({book.path for book in tree.books.values() if book.teeth_declared})
    current = obligations(tree, certified_books(books))
    base, why = base_manifest()
    committed = None
    if MANIFEST.exists():
        try:
            committed = json.loads(MANIFEST.read_text(encoding="utf-8"))
        except ValueError:
            committed = None
    problems = manifest_findings(current, base, why, committed)
    stale = [p for p in problems if "stale" in p or "is missing; run --write" in p]
    if bootstrap and base is None and committed is None:
        print(f"keystone_emit: BOOTSTRAP: no base and no manifest; writing the first "
              f"manifest ({why}); commit it, then planning/teeth-base.json naming that "
              f"revision")
        stale = problems
    print(manifest_counts(current))
    if write and problems == stale:
        MANIFEST.write_text(json.dumps({
            "about": "The teeth obligation manifest (TEETH CONTRACT v1): one entry per "
                     "registry keystone and per owed row; generated by tools/keystone_emit.py "
                     "--write, compared with planning/teeth-base.json's revision by --check.",
            "base_revision": base.get("revision") if base else None,
            "entries": sorted(current.values(), key=lambda e: e["name"]),
        }, indent=1, sort_keys=True) + "\n", encoding="utf-8")
        return []
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
    parser.add_argument("--check", action="store_true",
                        help="the report; findings exit 1 with or without it")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--claim", action="store_true",
                        help="with --write: claim an id for each form with none")
    parser.add_argument("--milestone")
    parser.add_argument("--title")
    parser.add_argument("--lane", default=Path.cwd().name)
    parser.add_argument("--write-manifest", action="store_true",
                        help="write planning/teeth-obligations.json when the gate's only "
                             "finding is its staleness")
    parser.add_argument("--bootstrap", action="store_true",
                        help="with --write-manifest: write the FIRST manifest when no base "
                             "and no manifest exist (never again)")
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
    # Validate fully first, each gate on its own: the registry findings
    # without writing, then the manifest gate.
    registry_problems = registry_findings(wellformed, False)
    registry_writable = {p for p in registry_problems
                         if "does not cite" in p or "run --write" in p}
    gate_problems = gate(False, arguments.bootstrap)
    gate_writable = {p for p in gate_problems if "stale" in p or "is missing; run --write" in p}
    if arguments.bootstrap and not MANIFEST.exists() and not BASE.exists():
        gate_writable |= {p for p in gate_problems if p.startswith("teeth gate: planning/teeth-base")}
    registry_blocking = [p for p in registry_problems if p not in registry_writable]
    gate_blocking = [p for p in gate_problems if p not in gate_writable]
    problems += registry_blocking + gate_blocking
    if arguments.write:
        if problems and (registry_blocking or subject_problems or refused):
            print(f"keystone_emit: --write refused: {len(registry_blocking) + len(subject_problems) + len(refused)} "
                  f"registry finding(s) to fix first; nothing written")
        else:
            registry_findings(wellformed, True)
            print("keystone_emit: wrote the citations and keystone_subjects")
    else:
        problems += sorted(registry_writable)
    if arguments.write_manifest:
        if gate_blocking:
            print(f"keystone_emit: --write-manifest refused: {len(gate_blocking)} gate "
                  f"finding(s) to fix first; nothing written")
        else:
            gate(True, arguments.bootstrap)
            print("keystone_emit: wrote planning/teeth-obligations.json")
    else:
        problems += sorted(gate_writable)

    if not (arguments.check and not problems):
        for keystone in wellformed:
            names = ledger.defkeystone_names(keystone.parts)
            print(f"{keystone.where}: {keystone.name} -> {keystone.ident or '(no id)'} "
                  f"{keystone.registry_name}; subject {keystone.subject} "
                  f"({reached.get(keystone.registry_name, 'unresolved')}); "
                  f"{len(keystone.parts['labels'])} removal, "
                  f"{len(keystone.parts['mutations'])} mutant, "
                  f"{len(names['bounds'])} bound")
    for problem in problems:
        print(f"keystone_emit: {problem}")
    print(f"keystone_emit: {len(keystones)} defkeystone form(s) in "
          f"{len({k.book for k in keystones})} book(s), {len(problems)} finding(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
