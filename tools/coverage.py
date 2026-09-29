#!/usr/bin/env python3
"""What the certified world says about each host-called entry, precisely.

Replaces the name-match heuristic that planning/interfaces-gaps.md used to
carry (a `:keystones` declaration, or a theorem whose name carried the
entry).  The subject of a claim is the function the host calls (AGENTS.md,
"What makes a claim"); this tool reads what the CERTIFIED WORLD says about
that function, from a dump tools/coverage_dump.lisp writes inside an ACL2
session over books/image-world (its certificates) and the host :program
files -- never from source text:

    python3 tools/proof_repl.py --host BOX start cov books/image-world --lane LANE
    python3 tools/proof_repl.py --host BOX send cov '(ld "../tools/coverage_dump.lisp")'
    python3 tools/proof_repl.py --host BOX send cov '(cov-dump "/abs/world.json" state)'
    python3 tools/coverage.py build --world build/coverage/world.json --write

`build --write` writes planning/coverage.json (one row per declared entry,
planning/interfaces.json's rows) and planning/interfaces-gaps.md from it;
both carry the coordinate of the world they were computed from (the source
revision, the box, the dump's digest).  The world changes with every book,
so a row is a statement about that coordinate: regenerate at convergence,
not per commit.

WHAT A THEOREM SAYS ABOUT AN ENTRY E, from its translated formula (the
`theorem` property), split on `implies` and on conjunctions:

  direct      E is a function symbol of a CONCLUSION.  The theorem is about E.
  hyps-only   E appears only in a hypothesis.  The theorem assumes something
              about E and concludes nothing about it.
  via-caller  the conclusion names a function F whose definitional closure
              (callees of `unnormalized-body', both sides of every mbe, and
              defattach attachments) reaches E, and E itself is unmentioned.
              The path F -> ... -> E is shown; the row says whether E is
              named in that proof's :hints (`opened`: expand/enable/use named
              it) or not (`by name only`: nothing in the world says E's
              definition took part in the proof).
  callee-only the conclusion names a function E calls.  AGENTS.md counts a
              theorem about a callee only with a named equating theorem; the
              `:via` keystones in host/interfaces.lisp are of this kind.
  nothing     no theorem of the tree's books mentions E, its callers or its
              callees.

Every theorem is also read against planning/proofs.json (a cited theorem is
an `events` entry of a proof; the proof's requirements file it under the
property families of planning/families.json), so a query can ask "which
entries has no storage-consistency theorem mentioned in a conclusion":

    python3 tools/coverage.py query --family storage-consistency --unmentioned
    python3 tools/coverage.py query --entry fn-lgc-append
    python3 tools/coverage.py query --subsystem store --unmentioned --md
    python3 tools/coverage.py query --family durability --level any --json

`--unmentioned` means no DIRECT theorem cited under a proof of that family;
`--level hyps|caller|any` widens what counts as mentioned.

A DECISION ENTRY (the rule, from the world, not from names of the entry):
an entry whose private closure -- E's body and the bodies reached from it
through callees that are not themselves declared entries and are defined in
the tree (a callee that is an entry is its own subject; a ground-zero or
community function is a leaf) -- both

  (a) BRANCHES: some body in the closure applies `if` (every `cond', `case',
      `and', `or' translates to it; a straight-line accessor, constructor or
      field projection does not), and
  (b) CONSTRUCTS OR CLASSIFIES AN OUTCOME: some function in the closure
      carries a word of DECISION_VOCABULARY in its name (a refusal, reply,
      answer, verdict, outcome class, decision, admission, acceptance,
      grant, authorization, reason, charge, credit, reservation,
      allocation, budget, capacity or fence).  Each word must name at least
      one function of the world, or the rule is stale and `--check` says so.

A DECLARED DELEGATION (`:delegates CALLEE` in host/interfaces.lisp, where
definterface refuses it unless the entry's body is exactly CALLEE applied to
the entry's formals): the entry is plumbing whose decision is CALLEE's, and
CALLEE's direct theorems are the entry's by definition -- provided the world
agrees (the entry calls exactly CALLEE) and CALLEE has a direct theorem;
`--check` refuses a declared delegation the world does not bear out, so a
delegation never hides a decision nobody proved anything about.

Everything else is PLUMBING, filed by what the world shows: `straight-line`
(no branch anywhere in the private closure), `codec` (branches only over
encode/decode/render/parse helpers), `delegates` (its decision is another
entry's: a callee that is a decision entry, named), `branches` (branches,
names no outcome; a scan, a fold, a projection with a case split).  An
entry the dumped world lacks is `absent` (declared after the dump, or
defined in a host file the session did not load) and decides nothing here.

`--check` (make check) refuses: a families file that leaves a requirement
unfiled or names an unknown id; a vocabulary word no function of the world
carries; a DECISION ENTRY WITH NO DIRECT THEOREM that
planning/coverage-baseline.json does not list (the baseline shrinks and
cannot grow silently: `--baseline` rewrites it, and a review reads the
diff); a gaps file that is not what planning/coverage.json renders.  It
prints, without failing, how far the declarations have moved since the
dump (entries declared and not in the coverage), since only a session can
close that gap.
"""
from __future__ import annotations

import argparse
import collections
import datetime as _dt
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

INTERFACES = ROOT / "planning" / "interfaces.json"
PROOFS = ROOT / "planning" / "proofs.json"
REQUIREMENTS = ROOT / "planning" / "requirements.json"
FAMILIES = ROOT / "planning" / "families.json"
COVERAGE = ROOT / "planning" / "coverage.json"
BASELINE = ROOT / "planning" / "coverage-baseline.json"
GAPS = ROOT / "planning" / "interfaces-gaps.md"
DEFAULT_WORLD = ROOT / "build" / "coverage" / "world.json"

SUBSYSTEMS = ("store", "owner", "nntp/served", "peer/feed", "bp", "web",
              "admin/operator", "control")

# A word of a function's name that says the function constructs or
# classifies an outcome (rule (b) above), with what it constructs.
DECISION_VOCABULARY = {
    "refus": "a refusal", "reject": "a rejection", "reply": "a reply",
    "answer": "an answer", "verdict": "a verdict", "outcome": "an outcome class",
    "decid": "a decision", "admit": "an admission", "admission": "an admission",
    "accept": "an acceptance", "grant": "a grant", "authoriz": "an authorization",
    "reason": "a refusal reason", "charge": "a charge",
    "credit": "a credit", "reserv": "a reservation", "alloc": "an allocation",
    "budget": "a budget", "capacity": "a capacity figure", "fence": "a fence",
}
CODEC_VOCABULARY = ("encode", "decode", "codec", "cbor", "render", "parse")
LEVELS = ("direct", "hyps", "caller", "any")
EXAMPLES = 5   # via-caller and callee-only rows keep this many examples


def sym(text: str) -> str:
    """`PKG::NAME` as the tree writes it: lowercase, no prefix for ACL2's own."""
    package, sep, name = text.partition("::")
    if not sep:
        return text.lower()
    return name.lower() if package in ("ACL2", "COMMON-LISP", "KEYWORD") else text.lower()


def book_of(raw) -> str:
    """A book as the tree names it (`books/x.lisp`), or where else the event was."""
    if raw is None:
        return "top-level"
    if raw.startswith(":"):
        return raw[1:]           # ground-zero, system/std/...
    head, sep, tail = raw.rpartition("/books/")
    return "books/" + tail if sep else raw


def ours(book: str) -> bool:
    return book.startswith("books/")


class World:
    """The dump, indexed: functions, theorems, the call graph and its reverse."""

    def __init__(self, doc: dict) -> None:
        self.cbd = doc.get("cbd", "")
        self.functions: dict[str, dict] = {}
        self.theorems: dict[str, dict] = {}
        # The dump is in world order: a null book before the first book is
        # ground zero (ACL2's primitives); after it, a file loaded at the top
        # level (the host :program files).
        seen_book = False
        for record in doc["functions"]:
            name = sym(record["name"])
            if name in self.functions:
                continue
            if record["book"] is not None:
                seen_book = True
            elif not seen_book:
                record = {**record, "book": ":ground-zero"}
            callees = sorted({sym(c) for c in record["callees"]})
            attachment = sym(record["attachment"]) if record.get("attachment") else None
            self.functions[name] = {
                "book": book_of(record["book"]),
                "class": sym(record["class"]),
                "callees": callees,
                "attachment": attachment,
                "constrained": bool(record.get("constrained")),
                "body": bool(record.get("body")),
            }
        for record in doc["theorems"]:
            name = sym(record["name"])
            book = book_of(record["book"])
            if name in self.theorems or not ours(book):
                continue
            self.theorems[name] = {
                "book": book,
                "hyps": sorted({sym(c) for c in record["hyps"]}),
                "concl": sorted({sym(c) for c in record["concl"]}),
                "classes": [sym(c) for c in record["classes"]],
                "hinted": sorted({sym(c) for c in record["hinted"]}),
            }
        self.graph: dict[str, list[str]] = {}
        self.reverse: dict[str, set[str]] = collections.defaultdict(set)
        for name, record in self.functions.items():
            edges = list(record["callees"])
            if record["attachment"]:
                edges.append(record["attachment"])
            self.graph[name] = edges
            for callee in edges:
                self.reverse[callee].add(name)
        self.concl_index: dict[str, set[str]] = collections.defaultdict(set)
        self.hyps_index: dict[str, set[str]] = collections.defaultdict(set)
        for name, record in self.theorems.items():
            for fn in record["concl"]:
                self.concl_index[fn].add(name)
            for fn in record["hyps"]:
                self.hyps_index[fn].add(name)

    def in_tree(self, name: str) -> bool:
        """Defined by the tree: a book, or a host file loaded at the top level."""
        record = self.functions.get(name)
        return bool(record) and (ours(record["book"]) or record["book"] == "top-level")

    def descendants(self, start: str, stop: frozenset = frozenset(),
                    tree_only: bool = False) -> set[str]:
        """Functions reached from START's callees; STOP names are leaves."""
        seen: set[str] = set()
        work = list(self.graph.get(start, ()))
        while work:
            name = work.pop()
            if name in seen or name == start:
                continue
            seen.add(name)
            if name in stop or (tree_only and not self.in_tree(name)):
                continue
            work.extend(self.graph.get(name, ()))
        return seen

    def ancestors(self, start: str) -> dict[str, str]:
        """Every caller reaching START, mapped to its callee toward START."""
        toward: dict[str, str] = {}
        queue = collections.deque([start])
        while queue:
            name = queue.popleft()
            for caller in self.reverse.get(name, ()):
                if caller in toward or caller == start:
                    continue
                toward[caller] = name
                queue.append(caller)
        return toward

    def path(self, toward: dict[str, str], top: str, start: str) -> list[str]:
        out = [top]
        while out[-1] != start:
            out.append(toward[out[-1]])
        return out


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


class Registry:
    """proofs.json, requirements.json and families.json, inverted."""

    def __init__(self, root: Path = ROOT) -> None:
        proofs = load_json(root / "planning" / "proofs.json")["proofs"]
        requirements = load_json(root / "planning" / "requirements.json")["requirements"]
        families = load_json(root / "planning" / "families.json")["families"]
        self.requirement_ids = {r["id"] for r in requirements}
        self.families = families
        self.family_of_requirement: dict[str, set[str]] = collections.defaultdict(set)
        for family, record in families.items():
            for rid in record["requirements"]:
                self.family_of_requirement[rid].add(family)
        self.proofs_of_event: dict[str, list[str]] = collections.defaultdict(list)
        self.requirements_of_proof: dict[str, list[str]] = {}
        for proof in proofs:
            self.requirements_of_proof[proof["id"]] = list(proof.get("requirements", []))
            for event in proof.get("events", []):
                self.proofs_of_event[event.lower()].append(proof["id"])

    def families_of_theorem(self, theorem: str) -> tuple[list[str], list[str]]:
        proofs = self.proofs_of_event.get(theorem, [])
        families: set[str] = set()
        for pid in proofs:
            for rid in self.requirements_of_proof.get(pid, ()):
                families |= self.family_of_requirement.get(rid, set())
        return proofs, sorted(families)

    def problems(self) -> list[str]:
        out = []
        filed: set[str] = set()
        for family, record in self.families.items():
            for rid in record["requirements"]:
                filed.add(rid)
                if rid not in self.requirement_ids:
                    out.append("planning/families.json: {} names {}, not a requirement".format(family, rid))
        for rid in sorted(self.requirement_ids - filed):
            out.append("planning/families.json: {} is filed under no family".format(rid))
        return out


# ---------------------------------------------------------------------------
# The coverage of one entry.

def theorem_row(world: World, registry: Registry, name: str) -> dict:
    proofs, families = registry.families_of_theorem(name)
    return {"theorem": name, "book": world.theorems[name]["book"],
            "proofs": proofs, "families": families}


def classify(world: World, entry: str, entries: frozenset) -> dict:
    """Decision or plumbing, by the rule in the module docstring."""
    record = world.functions[entry]
    closure = {entry} | world.descendants(entry, stop=entries, tree_only=True)
    closure = {name for name in closure if name == entry or name not in entries}
    branches = any("if" in world.graph.get(name, ()) for name in closure)
    vocabulary = {}
    for word, meaning in DECISION_VOCABULARY.items():
        hits = sorted(name for name in closure if word in name)
        if hits:
            vocabulary[word] = hits
    callee_entries = sorted(callee for callee in world.graph.get(entry, ())
                            if callee in entries and callee != entry)
    codec = sorted(name for name in closure
                   if any(word in name for word in CODEC_VOCABULARY))
    if branches and vocabulary:
        kind, why = "decision", "branches; constructs " + ", ".join(
            "{} ({})".format(DECISION_VOCABULARY[w], hits[0]) for w, hits in vocabulary.items())
    elif not branches:
        kind, why = "straight-line", "no branch in its private closure"
    elif codec and not vocabulary:
        kind, why = "codec", "branches only over " + ", ".join(codec[:3])
    else:
        kind, why = "branches", "branches, names no outcome"
    return {"kind": kind, "why": why, "closure": len(closure), "callee_entries": callee_entries,
            "vocabulary": vocabulary, "mode": record["class"], "book": record["book"]}


def delegate(rows: list[dict]) -> None:
    """A `branches` entry whose callee entries include a decision entry DELEGATES
    to it: its decision is that entry's (a second pass, once every entry is classified)."""
    decisions = {r["name"] for r in rows if r.get("kind") == "decision"}
    for row in rows:
        if row.get("kind") != "branches":
            continue
        delegates = sorted(c for c in row.get("callee_entries", ()) if c in decisions)
        if delegates:
            row["kind"] = "delegates"
            row["why"] = "its decision is another entry's: " + ", ".join(delegates)


def delegation(world: World, row: dict, callee: str) -> None:
    """A declared `:delegates CALLEE`: file the entry as plumbing whose decision
    is CALLEE's when the world bears it out (the entry's callees are exactly
    CALLEE, which has a direct theorem); else keep the entry's kind and carry
    the problem, which `check` refuses."""
    name = row["name"]
    if name not in world.functions:
        return
    edges = sorted(set(world.graph.get(name, ())))
    direct = sorted(world.concl_index.get(callee, set()))
    if edges != [callee]:
        row["delegates_problem"] = "{} is declared to delegate to {} but calls {}".format(
            name, callee, ", ".join(edges) or "nothing")
    elif not direct:
        row["delegates_problem"] = "{} delegates to {}, which no theorem's conclusion names".format(
            name, callee)
    else:
        row["kind"] = "delegates"
        row["why"] = ("its decision is {0}'s: the entry is exactly a call of it (declared "
                      ":delegates); {0}'s direct theorems: {1}".format(callee, ", ".join(direct[:3])))
        row["delegated_direct"] = direct


def cover(world: World, registry: Registry, entry: str, entries: frozenset) -> dict:
    if entry not in world.functions:
        return {"status": "absent", "kind": "absent",
                "why": "not in the dumped world (declared after it, or a host file it did not load)",
                "direct": [], "hyps_only": [], "via_caller": {"count": 0, "opened": 0, "examples": []},
                "callee_only": {"count": 0, "examples": []}}
    shape = classify(world, entry, entries)
    direct = sorted(world.concl_index.get(entry, set()))
    hyps_only = sorted(world.hyps_index.get(entry, set()) - set(direct))
    mentioned = set(direct) | set(hyps_only)
    toward = world.ancestors(entry)
    via: dict[str, tuple[str, list[str]]] = {}
    for caller in toward:
        for theorem in world.concl_index.get(caller, ()):
            if theorem in mentioned:
                continue
            path = world.path(toward, caller, entry)
            if theorem not in via or len(path) < len(via[theorem][1]):
                via[theorem] = (caller, path)
    opened = sorted(t for t in via if entry in world.theorems[t]["hinted"])
    via_rows = []
    for theorem in sorted(via, key=lambda t: (t not in opened, len(via[t][1]), t)):
        row = theorem_row(world, registry, theorem)
        row.update({"path": via[theorem][1], "opened": theorem in opened})
        via_rows.append(row)
    # About a callee: a theorem whose conclusion names a function of E's
    # PRIVATE closure (its own helpers: callees that are not entries, defined
    # in the tree).  The whole closure reaches the world's basic recognizers
    # and their thousands of lemmas, which say nothing about E.
    depth: dict[str, int] = {}
    queue = collections.deque((c, 1) for c in world.graph.get(entry, ()))
    while queue:
        callee, d = queue.popleft()
        if callee in depth or callee == entry:
            continue
        depth[callee] = d
        if callee in entries or not world.in_tree(callee):
            continue
        queue.extend((c, d + 1) for c in world.graph.get(callee, ()))
    nearest: dict[str, tuple[int, str]] = {}
    for callee, d in depth.items():
        if callee in entries or not world.in_tree(callee):
            continue
        for theorem in world.concl_index.get(callee, ()):
            if theorem not in nearest or d < nearest[theorem][0]:
                nearest[theorem] = (d, callee)
    callee_only = set(nearest) - mentioned - set(via)
    callee_rows = []
    for theorem in sorted(callee_only, key=lambda t: (
            nearest[t][0], not registry.proofs_of_event.get(t), t)):
        row = theorem_row(world, registry, theorem)
        row.update({"about": nearest[theorem][1], "depth": nearest[theorem][0]})
        callee_rows.append(row)
    if direct:
        status = "direct"
    elif hyps_only:
        status = "hyps-only"
    elif via:
        status = "via-caller"
    elif callee_only:
        status = "callee-only"
    else:
        status = "nothing"
    return {
        "status": status, **shape,
        "direct": [theorem_row(world, registry, t) for t in direct],
        "hyps_only": [theorem_row(world, registry, t) for t in hyps_only],
        "via_caller": {"count": len(via), "opened": len(opened), "examples": via_rows[:EXAMPLES]},
        "callee_only": {"count": len(callee_only), "examples": callee_rows[:EXAMPLES]},
    }


def coordinate(world_path: Path, box: str | None) -> dict:
    try:
        revision = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        revision = None
    return {"source_revision": revision, "box": box,
            "dump_sha256": hashlib.sha256(world_path.read_bytes()).hexdigest(),
            "date": _dt.date.today().isoformat()}


def build(world_path: Path, box: str | None = None, root: Path = ROOT) -> dict:
    world = World(load_json(world_path))
    registry = Registry(root)
    declared = load_json(root / "planning" / "interfaces.json")["entries"]
    entries = frozenset(d["name"] for d in declared)
    rows = []
    for d in declared:
        row = {"name": d["name"], "subsystem": d["subsystem"], "declared_class": d["class"],
               "keystones": d["keystones"], "dispatched_from": d["dispatched_from"],
               "delegates": d.get("delegates")}
        row.update(cover(world, registry, d["name"], entries))
        if d.get("delegates"):
            delegation(world, row, d["delegates"])
        rows.append(row)
    delegate(rows)
    stale = sorted(word for word in DECISION_VOCABULARY
                   if not any(word in name for name in world.functions if world.in_tree(name)))
    return {
        "schema_version": 1,
        "description": ("GENERATED by tools/coverage.py build from a dump of the certified world "
                        "(tools/coverage_dump.lisp) and planning/interfaces.json, proofs.json, "
                        "requirements.json and families.json.  Do not edit; regenerate at "
                        "convergence."),
        "coordinate": {**coordinate(world_path, box), "world_cbd": world.cbd,
                       "theorems": len(world.theorems),
                       "functions": sum(1 for n in world.functions if world.in_tree(n))},
        "rule": {"decision": "branches (if in its private closure) and constructs an outcome "
                             "(DECISION_VOCABULARY word in a closure function's name)",
                 "vocabulary": DECISION_VOCABULARY, "vocabulary_unmatched": stale},
        "entries": rows,
    }


# ---------------------------------------------------------------------------
# Reading the coverage: summaries, queries, the gaps file, the baseline.

def load_coverage(path: Path = COVERAGE) -> dict:
    if not path.is_file():
        raise SystemExit("coverage: {} is missing; run `coverage.py build --write` "
                         "from a world dump".format(path.relative_to(ROOT)))
    return load_json(path)


def summary(rows: list[dict]) -> dict:
    keys = ("declared", "decision", "decision_direct", "decision_uncovered", "plumbing",
            "direct", "hyps-only", "via-caller", "callee-only", "nothing", "absent",
            "program", "via_opened")
    out = {sub: dict.fromkeys(keys, 0) for sub in (*SUBSYSTEMS, "all")}
    for row in rows:
        for sub in (row["subsystem"], "all"):
            c = out[sub]
            c["declared"] += 1
            c[row["status"]] += 1
            if row["kind"] == "decision":
                c["decision"] += 1
                c["decision_direct" if row["direct"] else "decision_uncovered"] += 1
            elif row["kind"] != "absent":
                c["plumbing"] += 1
            if row.get("mode") == "program":
                c["program"] += 1
            if row["status"] == "via-caller" and row["via_caller"]["opened"]:
                c["via_opened"] += 1
    return out


def mentioned_under(row: dict, family: str | None, level: str) -> bool:
    """Does a theorem at LEVEL mention the entry under FAMILY (any family if None)?"""
    def hit(theorems):
        return any(family is None or family in t["families"] for t in theorems)
    if hit(row["direct"]):
        return True
    if level in ("hyps", "any") and hit(row["hyps_only"]):
        return True
    if level in ("caller", "any") and hit(row["via_caller"]["examples"]):
        return True
    return False


def query(cov: dict, family: str | None, subsystem: str | None, entry: str | None,
          unmentioned: bool, level: str) -> list[dict]:
    rows = cov["entries"]
    if entry:
        rows = [r for r in rows if r["name"] == entry]
    if subsystem:
        rows = [r for r in rows if r["subsystem"] == subsystem]
    if unmentioned:
        rows = [r for r in rows if not mentioned_under(r, family, level)]
    elif family:
        rows = [r for r in rows if mentioned_under(r, family, level)]
    return rows


def theorem_cell(theorems: list[dict], limit: int = 3) -> str:
    names = ["`{}`".format(t["theorem"]) for t in theorems[:limit]]
    more = len(theorems) - limit
    return ", ".join(names) + (" (+{})".format(more) if more > 0 else "")


def render_table(rows: list[dict]) -> str:
    lines = ["| entry | subsystem | kind | mode | status | direct | via caller (opened) | why |",
             "|---|---|---|---|---|---|---|---|"]
    for r in rows:
        lines.append("| `{}` | {} | {} | {} | {} | {} | {} ({}) | {} |".format(
            r["name"], r["subsystem"], r["kind"], r.get("mode", ""), r["status"],
            theorem_cell(r["direct"]), r["via_caller"]["count"], r["via_caller"]["opened"],
            r["why"].replace("|", "/")))
    return "\n".join(lines)


def render_entry(row: dict) -> str:
    lines = ["# `{}` ({}, {}, {})".format(row["name"], row["subsystem"], row["kind"], row.get("mode")),
             "", row["why"], "", "status: {}".format(row["status"]), ""]
    for label, key in (("Direct (conclusion names it)", "direct"),
                       ("Hypothesis only", "hyps_only")):
        lines.append("## {}: {}".format(label, len(row[key])))
        for t in row[key]:
            lines.append("- `{}` ({}) {} {}".format(t["theorem"], t["book"],
                                                    ",".join(t["proofs"]) or "uncited",
                                                    ",".join(t["families"])))
    via = row["via_caller"]
    lines.append("## Via a caller: {} ({} opened; {} shown)".format(
        via["count"], via["opened"], len(via["examples"])))
    for t in via["examples"]:
        lines.append("- `{}` path {} {}".format(
            t["theorem"], " -> ".join(t["path"]), "opened" if t["opened"] else "by name only"))
    callee = row["callee_only"]
    lines.append("## About a callee only: {} ({} shown)".format(callee["count"], len(callee["examples"])))
    for t in callee["examples"]:
        lines.append("- `{}` about `{}` at depth {} ({}) {}".format(
            t["theorem"], t.get("about"), t.get("depth"), t["book"],
            ",".join(t["proofs"]) or "uncited"))
    return "\n".join(lines)


def render_gaps(cov: dict) -> str:
    rows = cov["entries"]
    counts = summary(rows)
    c = cov["coordinate"]
    lines = [
        "# Host-called entries: the gaps",
        "",
        "GENERATED by tools/coverage.py from planning/coverage.json: what the",
        "certified world (a dump tools/coverage_dump.lisp wrote in an ACL2 session",
        "over books/image-world) says about each declared entry of",
        "planning/interfaces.json.  Do not edit; regenerate at convergence.",
        "",
        "Coordinate: source revision {}, box {}, {}; {} theorems of the tree's books,".format(
            c.get("source_revision"), c.get("box"), c.get("date"), c.get("theorems")),
        "{} functions.  The rule for a decision entry and each level are in".format(c.get("functions")),
        "tools/coverage.py's docstring: `direct` is a theorem whose conclusion names",
        "the entry; `via-caller` a theorem about a function whose definition reaches",
        "it (opened = the proof's hints name it; otherwise by name only);",
        "`callee-only` a theorem about something it calls, which AGENTS.md counts",
        "only with an equating theorem; `program` entries cannot appear in any",
        "theorem.  `decision uncovered` is the shrink-only figure",
        "(planning/coverage-baseline.json).",
        "",
        "| subsystem | declared | decision | decision direct | decision uncovered | plumbing | direct | hyps-only | via-caller (opened) | callee-only | nothing | absent | :program |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for sub in (*SUBSYSTEMS, "all"):
        k = counts[sub]
        lines.append("| {} | {} | {} | {} | {} | {} | {} | {} | {} ({}) | {} | {} | {} | {} |".format(
            sub, k["declared"], k["decision"], k["decision_direct"], k["decision_uncovered"],
            k["plumbing"], k["direct"], k["hyps-only"], k["via-caller"], k["via_opened"],
            k["callee-only"], k["nothing"], k["absent"], k["program"]))
    for sub in SUBSYSTEMS:
        mine = [r for r in rows if r["subsystem"] == sub]
        uncovered = [r for r in mine if r["kind"] == "decision" and not r["direct"]]
        lines += ["", "## {}: {} decision entries with no direct theorem, of {} decision entries".format(
            sub, len(uncovered), sum(1 for r in mine if r["kind"] == "decision")), ""]
        if uncovered:
            lines.append(render_table(sorted(uncovered, key=lambda r: r["name"])))
        else:
            lines.append("none")
        plumbing = [r for r in mine if r["kind"] not in ("decision", "absent")]
        lines += ["", "### {}: plumbing ({}), by kind".format(sub, len(plumbing)), "",
                  "| entry | kind | mode | status | why |", "|---|---|---|---|---|"]
        for r in sorted(plumbing, key=lambda r: (r["kind"], r["name"])):
            lines.append("| `{}` | {} | {} | {} | {} |".format(
                r["name"], r["kind"], r.get("mode", ""), r["status"], r["why"].replace("|", "/")))
        absent = [r for r in mine if r["kind"] == "absent"]
        if absent:
            lines += ["", "### {}: absent from the dumped world ({}): {}".format(
                sub, len(absent), ", ".join("`{}`".format(r["name"]) for r in sorted(
                    absent, key=lambda r: r["name"])))]
    return "\n".join(lines) + "\n"


def uncovered_decisions(cov: dict) -> list[str]:
    return sorted(r["name"] for r in cov["entries"] if r["kind"] == "decision" and not r["direct"])


def load_baseline(path: Path = BASELINE) -> dict:
    return load_json(path) if path.is_file() else {"uncovered": []}


def write_baseline(cov: dict, path: Path = BASELINE) -> None:
    path.write_text(json.dumps({
        "note": ("Decision entries (tools/coverage.py's rule) with no theorem whose conclusion "
                 "names them, at planning/coverage.json's coordinate.  coverage.py --check "
                 "fails on one NOT listed here, so the number can shrink and cannot grow "
                 "silently.  Remove an entry by proving a keystone about it, not by editing "
                 "this file."),
        "coordinate": cov["coordinate"].get("source_revision"),
        "uncovered": uncovered_decisions(cov)}, indent=2) + "\n")


def check(cov: dict | None, root: Path = ROOT) -> tuple[list[str], list[str]]:
    """(problems, notes): problems fail make check, notes only print."""
    problems = Registry(root).problems()
    notes: list[str] = []
    if cov is None:
        notes.append("planning/coverage.json is missing: no world dump has been built yet")
        return problems, notes
    for word in cov["rule"].get("vocabulary_unmatched", []):
        problems.append("DECISION_VOCABULARY word {!r} names no function of the world".format(word))
    baseline = set(load_baseline(root / "planning" / "coverage-baseline.json")["uncovered"])
    grown = sorted(set(uncovered_decisions(cov)) - baseline)
    for name in grown:
        problems.append("decision entry {} has no direct theorem and planning/coverage-baseline.json "
                        "does not list it".format(name))
    for row in cov["entries"]:
        if row.get("delegates_problem"):
            problems.append("declared :delegates the world does not bear out: " + row["delegates_problem"])
    gaps = root / "planning" / "interfaces-gaps.md"
    if not gaps.is_file() or gaps.read_text(encoding="utf-8") != render_gaps(cov):
        problems.append("planning/interfaces-gaps.md is not what planning/coverage.json renders; "
                        "run tools/coverage.py build --write (or render --write)")
    declared = {d["name"] for d in load_json(root / "planning" / "interfaces.json")["entries"]}
    covered = {r["name"] for r in cov["entries"]}
    if declared - covered:
        notes.append("{} declared entries are not in planning/coverage.json (declared since its "
                     "coordinate {}): {}".format(len(declared - covered), cov["coordinate"].get(
                         "source_revision"), ", ".join(sorted(declared - covered)[:8])))
    return problems, notes


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command")
    b = sub.add_parser("build", help="compute planning/coverage.json from a world dump")
    b.add_argument("--world", type=Path, default=DEFAULT_WORLD)
    b.add_argument("--box", default=None, help="where the session ran (the coordinate)")
    b.add_argument("--write", action="store_true", help="write coverage.json and the gaps file")
    b.add_argument("--baseline", action="store_true", help="also rewrite coverage-baseline.json")
    q = sub.add_parser("query", help="ask the coverage")
    q.add_argument("--family", default=None)
    q.add_argument("--subsystem", default=None, choices=SUBSYSTEMS)
    q.add_argument("--entry", default=None)
    q.add_argument("--unmentioned", action="store_true")
    q.add_argument("--level", default="direct", choices=LEVELS)
    q.add_argument("--json", action="store_true")
    q.add_argument("--md", action="store_true")
    s = sub.add_parser("summary", help="the per-subsystem and per-family numbers")
    s.add_argument("--json", action="store_true")
    r = sub.add_parser("render", help="rewrite the gaps file from coverage.json")
    r.add_argument("--write", action="store_true")
    c = sub.add_parser("check", help="the make-check step")
    parser.add_argument("--check", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--baseline", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args(argv)

    if args.command == "build":
        cov = build(args.world, args.box)
        if args.write:
            COVERAGE.write_text(json.dumps(cov, indent=1) + "\n")
            GAPS.write_text(render_gaps(cov))
        if args.baseline:
            write_baseline(cov)
        k = summary(cov["entries"])["all"]
        print("coverage: {} entries; {} decision ({} direct, {} uncovered); {} plumbing; "
              "{} direct / {} hyps-only / {} via-caller ({} opened) / {} callee-only / "
              "{} nothing / {} absent; {} :program".format(
                  k["declared"], k["decision"], k["decision_direct"], k["decision_uncovered"],
                  k["plumbing"], k["direct"], k["hyps-only"], k["via-caller"], k["via_opened"],
                  k["callee-only"], k["nothing"], k["absent"], k["program"]))
        return 0
    if args.command == "query":
        cov = load_coverage()
        if args.family and args.family not in cov and args.family not in Registry().families:
            raise SystemExit("coverage: unknown family {!r}; planning/families.json has: {}".format(
                args.family, ", ".join(Registry().families)))
        rows = query(cov, args.family, args.subsystem, args.entry, args.unmentioned, args.level)
        if args.json:
            print(json.dumps(rows, indent=1))
        elif args.entry and rows and not args.md:
            print(render_entry(rows[0]))
        else:
            print(render_table(rows))
            print("\n{} entries".format(len(rows)))
        return 0
    if args.command == "summary":
        cov = load_coverage()
        counts = summary(cov["entries"])
        families = family_summary(cov)
        if args.json:
            print(json.dumps({"subsystems": counts, "families": families}, indent=1))
        else:
            for sub, k in counts.items():
                print("{:15} {}".format(sub, " ".join("{}={}".format(a, b) for a, b in k.items())))
            for fam, k in families.items():
                print("{:28} {}".format(fam, " ".join("{}={}".format(a, b) for a, b in k.items())))
        return 0
    if args.command == "render":
        cov = load_coverage()
        text = render_gaps(cov)
        if args.write:
            GAPS.write_text(text)
        else:
            sys.stdout.write(text)
        return 0
    if args.command == "check" or args.check or args.baseline:
        cov = load_coverage() if COVERAGE.is_file() else None
        if args.baseline and cov:
            write_baseline(cov)
        problems, notes = check(cov)
        print("coverage: {} problem(s){}".format(
            len(problems), "; " + "; ".join(notes) if notes else ""))
        for problem in problems:
            print("  " + problem)
        return 1 if problems else 0
    parser.print_help()
    return 2


def family_summary(cov: dict) -> dict:
    """Per family: entries with a direct theorem cited under it, decision entries without."""
    families = list(Registry().families)
    out = {}
    for family in families:
        direct = [r for r in cov["entries"] if mentioned_under(r, family, "direct")]
        any_level = [r for r in cov["entries"] if mentioned_under(r, family, "any")]
        decisions = [r for r in cov["entries"] if r["kind"] == "decision"]
        out[family] = {"entries_direct": len(direct), "entries_any_level": len(any_level),
                       "decision_entries_unmentioned": sum(
                           1 for r in decisions if not mentioned_under(r, family, "direct"))}
    return out


if __name__ == "__main__":
    raise SystemExit(main())
