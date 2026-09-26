#!/usr/bin/env python3
"""Find the theorems whose subject no host line can reach.

AGENTS.md's first assurance rule says "The theorem subject is the function the
host calls", and "Say which host line calls the subject."  That rule has been
prose with nothing behind it, and the defect it names has been our most
expensive one.  Five instances surfaced on 2026-09-21 alone, every one found
by someone driving the wire and none by a check:

* K3's duplicate suppression (`fn-peer-history-is-have-at-offer`) was proved
  of `fn-peer-decide-offer`, which answered from the node pinned when the
  connection OPENED.  The certified refusal sat behind a branch the running
  server could not reach while the wire answered `335`, and a streaming peer
  paid for the whole article twice.
* `fn-peer-capability-lines` renders the transit capability list, has a
  block-text lemma and five assertions.  `fn-auth-step` answers `CAPABILITIES`
  itself before it ever delegates, so the arm never runs.
* `fn-own-feed-durable-records` existed with no caller, so the outbound queue
  lived in memory and an article accepted while a peer was down did not
  survive the process that accepted it.
* `fn-feed-lost` had no live caller: a socket that died left its entry `:sent`
  until a restart.
* `fn-cpc-validp` validates a checkpoint and no host line calls it.

Each was true, proved, certified, and irrelevant to the running server.

    python3 tools/reach_check.py              # findings
    python3 tools/reach_check.py --summary    # the line `make check` prints
    python3 tools/reach_check.py --strict     # non-zero on an UNBASELINED orphan
    python3 tools/reach_check.py --baseline   # rewrite the baseline (deliberate)

WHAT IT MEASURES.  The call graph over `books/*.lisp` and `host/*.lisp`,
seeded from every function `host/` defines, every book symbol a host file
names, and every book symbol a `tools/*.py` bridge names in a string --- the
bridges really do call ACL2 by building forms as text, so those are host
lines too.  A registry event is HOSTED when at least one function its theorem
mentions is in that reachable set.

WHAT IT CANNOT SEE, and why it is deliberately generous.  "The functions its
theorem mentions" over-approximates the subject: a hypothesis predicate
counts alongside the conclusion's real subject.  So an event can be called
hosted on the strength of a recognizer the host happens to reach.  That makes
the count a FLOOR --- every orphan it reports is real, and it misses some.
A gate that cries wolf gets switched off, and this one is meant to stay on.
It also cannot see a function reached only through a macro this reader does
not expand, or named in a Python string it does not recognize as a symbol.
The one macro it does expand is `fn-defrecord' (books/defrecord.lisp): its
generated recognizer is a definition here, whose body is the record's
`:fields' types, `:extra' conjuncts and `:recognizer-formals' (PKT-394: fn-node-statep's
field conjuncts call fn-statep and fn-node-articles-have-archive-bindingsp,
which fn-sco-finalize-from executes at every open, and without the expansion
three PRF-173 keystones read as orphans).

A flag is a question for a human, never a verdict.  Being unreachable is not
by itself a defect: a book can legitimately run ahead of its host.  What the
baseline does is stop the number growing silently.
"""
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASELINE = ROOT / "planning" / "reach-baseline.json"

DEFUN = re.compile(r"\((?:defun|defund|defun-nx|define|defmacro)\s+([a-zA-Z0-9<>=/*+-]+)")
DEFTHM = re.compile(r"\((?:defthm|defthmd)\s+([a-zA-Z0-9<>=/*+-]+)")
SYMBOL = re.compile(r"[a-zA-Z][a-zA-Z0-9<>=/*+-]*")
NAME = r"[a-zA-Z0-9<>=/*+-]+"
ATTACH_ONE = re.compile(rf"\(defattach\s+({NAME})\s+({NAME})")
ATTACH_PAIR = re.compile(rf"\(\s*({NAME})\s+({NAME})\s*\)")


def attachments(paths) -> dict[str, set[str]]:
    """constrained name -> the functions `defattach` binds it to.

    Calling a constrained function runs its attachment, so a host line that
    reaches `fn-bs-txn-name` reaches `fn-bs-txn-name-impl`.  Both forms are
    read: `(defattach f g)` and `(defattach (f g) (f2 g2) ...)`.  Pairs
    inside `:hints` are not attachments; the scan stops at the first keyword.
    """
    found: dict[str, set[str]] = collections.defaultdict(set)
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for form in forms(text):
            if not form.startswith("(defattach"):
                continue
            one = ATTACH_ONE.match(form)
            if one:
                found[one.group(1).lower()].add(one.group(2).lower())
                continue
            head = form.split(":", 1)[0]
            for left, right in ATTACH_PAIR.findall(head):
                found[left.lower()].add(right.lower())
    return found


def forms(text: str) -> list[str]:
    """Top-level forms, tracking parens outside strings and comments."""
    out: list[str] = []
    depth, start, i, n, in_string = 0, None, 0, len(text), False
    while i < n:
        char = text[i]
        if in_string:
            if char == "\\":
                i += 2
                continue
            if char == '"':
                in_string = False
            i += 1
            continue
        if char == ";":
            newline = text.find("\n", i)
            i = n if newline < 0 else newline + 1
            continue
        if char == '"':
            in_string = True
            i += 1
            continue
        if char == "(":
            if depth == 0:
                start = i
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0 and start is not None:
                out.append(text[start:i + 1])
                start = None
        i += 1
    return out


def definitions(paths, pattern=DEFUN):
    """name -> (file, whole form), for every definition the pattern opens."""
    found = {}
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for form in forms(text):
            match = pattern.match(form)
            if match:
                found[match.group(1).lower()] = (
                    str(path.relative_to(ROOT)), form)
    return found


SEXP_TOKEN = re.compile(r'\s+|;[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s()";]+')


def read_sexp(text: str):
    """The first s-expression of TEXT as nested lists of atom strings
    (strings and comments dropped): enough to read a macro's keywords."""
    stack: list[list] = [[]]
    for token in SEXP_TOKEN.findall(text):
        if not token.strip() or token.startswith((";", '"')):
            continue
        if token == "(":
            stack.append([])
        elif token == ")":
            done = stack.pop()
            stack[-1].append(done)
            if len(stack) == 1:
                return done
        else:
            stack[-1].append(token.lower())
    return stack[-1][0] if stack[-1] else None


def flatten(tree) -> str:
    if isinstance(tree, list):
        return "(" + " ".join(flatten(t) for t in tree) + ")"
    return str(tree)


def record_definitions(paths):
    """name -> (file, body) for the recognizer each `(fn-defrecord NAME ...)'
    generates (books/defrecord.lisp): `:recognizer', default NAMEp, none for
    `:recognizer nil'.  Its body is the record's field types (a unary
    predicate applied to the accessor, or a term), `:extra' and
    `:recognizer-formals'.  The shape predicate, constructor and accessors
    are not made definitions: they are the record's plumbing, and counting
    them would host every theorem that merely reads a field (PRF-088's
    fn-rcl-reclaim-keeps-the-numbering would be hosted by fn-state-groups)."""
    found = {}
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        rel = str(path.relative_to(ROOT))
        for form in forms(text):
            if not re.match(r"\(fn-defrecord\s", form, re.I):
                continue
            tree = read_sexp(form)
            if not tree or len(tree) < 2 or not isinstance(tree[1], str):
                continue
            name, rest = tree[1], tree[2:]
            keys = {rest[i]: rest[i + 1] for i in range(0, len(rest) - 1, 2)
                    if isinstance(rest[i], str) and rest[i].startswith(":")}
            recognizer = keys.get(":recognizer", ":default")
            if recognizer == "nil":
                continue
            recp = name + "p" if recognizer == ":default" else flatten(recognizer)
            conjuncts = []
            for field in keys.get(":fields") or []:
                if isinstance(field, list) and len(field) > 1 and field[1] != "t":
                    conjuncts.append(flatten(field[1]))
            conjuncts += [flatten(keys.get(":extra", [])),
                          flatten(keys.get(":recognizer-formals", []))]
            found[recp] = (rel, "(fn-defrecord-recognizer %s %s)" % (
                recp, " ".join(conjuncts)))
    return found


class Graph:
    """The call graph, and what a host line can reach through it."""

    def __init__(self) -> None:
        self.books = sorted(ROOT.glob("books/*.lisp"))
        self.hosts = (sorted(ROOT.glob("host/*.lisp"))
                      + sorted(ROOT.glob("host/native/*.lisp")))
        # Not this file: its prose names book functions as examples, and a
        # checker's own docstring is not a host line.
        self.bridges = [p for p in sorted(ROOT.glob("tools/*.py"))
                        if p.name != pathlib.Path(__file__).name]

        self.book_defs = {**record_definitions(self.books),
                          **definitions(self.books)}
        host_defs = definitions(self.hosts)
        attached = attachments(self.books)
        self.known = set(self.book_defs) | set(host_defs) | set(attached)

        bodies = {n: f for n, (_, f) in self.book_defs.items()}
        bodies.update({n: f for n, (_, f) in host_defs.items()})
        self.edges = {name: self.mentions(form, name)
                      for name, form in bodies.items()}
        for constrained, bound in attached.items():
            self.edges.setdefault(constrained, set()).update(bound)

        # Seeds: everything host/ defines, plus every book symbol a host file
        # or a Python bridge names.  A bridge naming `fn-own-read` in a form
        # it builds as text IS a host line; that is how the owner is driven.
        seen = set(host_defs)
        self.seeds = collections.Counter()
        for path in self.hosts + self.bridges:
            label = "host" if path.suffix == ".lisp" else "bridge"
            text = path.read_text(encoding="utf-8", errors="replace")
            for symbol in self.symbols(text) & set(self.book_defs):
                if symbol not in seen:
                    seen.add(symbol)
                    self.seeds[label] += 1
        work = list(seen)
        while work:
            for nxt in self.edges.get(work.pop(), ()):
                if nxt not in seen:
                    seen.add(nxt)
                    work.append(nxt)
        self.reachable = seen & set(self.book_defs)

    @staticmethod
    def symbols(text: str) -> set[str]:
        return {s.lower() for s in SYMBOL.findall(text)}

    def mentions(self, form: str, own: str) -> set[str]:
        return self.symbols(form) & self.known - {own}


class Finding:
    def __init__(self, proof_id, event, book, subjects):
        self.proof_id, self.event = proof_id, event
        self.book, self.subjects = book, subjects

    def key(self) -> str:
        return f"{self.proof_id}:{self.event}"

    def render(self) -> str:
        named = ", ".join(self.subjects[:4]) or "nothing this reader resolved"
        return (f"{self.book}: {self.event} ({self.proof_id}): no host line "
                f"reaches any function it is about ({named}), so the running "
                f"server does not exercise what this event claims")


def audit(graph: Graph):
    theorems = definitions(graph.books, DEFTHM)
    registry = json.loads((ROOT / "planning" / "proofs.json").read_text())
    rows = registry["proofs"] if isinstance(registry, dict) else registry

    findings, hosted, unresolved = [], 0, []
    for row in rows:
        for event in row.get("events", []):
            name = str(event).lower()
            entry = theorems.get(name)
            if not entry:
                unresolved.append((row["id"], name, "no such defthm here"))
                continue
            book, form = entry
            subjects = sorted(graph.mentions(form, name) & set(graph.book_defs))
            if not subjects:
                unresolved.append((row["id"], name, "no resolvable subject"))
                continue
            if set(subjects) & graph.reachable:
                hosted += 1
            else:
                findings.append(Finding(row["id"], name, book, subjects))
    return findings, hosted, unresolved


def load_baseline() -> dict:
    if not BASELINE.exists():
        return {"accepted": {}}
    return json.loads(BASELINE.read_text())


PLACEHOLDER = "no one has said why that is right"
DISPOSITIONS = ("SPEC", "HOST")


def unexplained(accepted: dict) -> list[str]:
    """Baselined orphans whose reason is not a disposition.

    Each entry says SPEC (a model or specification theorem kept, and why) or
    HOST (the packet that will host it); a bare acceptance is a flag nobody
    triaged (assurance-triage 2026-09-26 found 25 of 49 that way).
    """
    return sorted(key for key, reason in accepted.items()
                  if PLACEHOLDER in reason or not reason.startswith(DISPOSITIONS))


def write_baseline(findings) -> None:
    current = load_baseline()
    existing = current.get("accepted", {})
    accepted = {}
    for finding in sorted(findings, key=Finding.key):
        accepted[finding.key()] = existing.get(
            finding.key(),
            "no host line reaches this subject and " + PLACEHOLDER)
    BASELINE.write_text(json.dumps(
        {"note": current.get("note") or ("Registry events whose subject no host line reaches, that "
                  "the tree accepts for now.  tools/reach_check.py --strict "
                  "fails on any orphan NOT listed here, so the number can "
                  "shrink and cannot grow silently.  Remove an entry by "
                  "hosting the subject, not by editing this file."),
         "accepted": accepted}, indent=2, sort_keys=True) + "\n")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--summary", action="store_true",
                        help="one line, the shape `make check` prints")
    parser.add_argument("--strict", action="store_true",
                        help="exit non-zero on an orphan not in the baseline")
    parser.add_argument("--baseline", action="store_true",
                        help="rewrite planning/reach-baseline.json from this run")
    arguments = parser.parse_args(argv)

    graph = Graph()
    findings, hosted, unresolved = audit(graph)

    if arguments.baseline:
        write_baseline(findings)
        print(f"reach_check: baseline rewritten with {len(findings)} accepted "
              f"orphan(s) in {BASELINE.relative_to(ROOT)}")
        return 0

    accepted = load_baseline().get("accepted", {})
    fresh = [f for f in findings if f.key() not in accepted]
    stale = sorted(set(accepted) - {f.key() for f in findings})

    if arguments.summary:
        print(f"reach_check: {hosted + len(findings)} registry events over "
              f"{len(graph.book_defs)} book functions; {hosted} have a subject "
              f"a host line reaches, {len(findings)} do not "
              f"({len(fresh)} of them unbaselined), {len(unresolved)} "
              f"unresolvable here")
        by_proof = collections.Counter(f.proof_id for f in findings)
        if by_proof:
            worst = ", ".join(f"{p} {n}" for p, n in by_proof.most_common(5))
            print(f"reach_check: orphans concentrate in {worst}")
        for finding in fresh:
            print(f"reach_check: NEW unreachable subject -- {finding.render()}")
        if stale:
            print(f"reach_check: {len(stale)} baselined orphan(s) now hosted; "
                  f"drop them with --baseline: {', '.join(stale[:4])}")
    else:
        for finding in sorted(findings, key=Finding.key):
            mark = "NEW  " if finding.key() not in accepted else "     "
            print(mark + finding.render())
        print()
        print(f"{len(graph.book_defs)} book functions, "
              f"{len(graph.reachable)} reachable from a host line "
              f"({len(graph.reachable) / len(graph.book_defs):.0%}); seeds: "
              + ", ".join(f"{n} from {k}" for k, n in graph.seeds.items()))
        print(f"{hosted} registry events hosted, {len(findings)} orphaned, "
              f"{len(fresh)} of those unbaselined, {len(unresolved)} "
              f"unresolvable here")

    untriaged = unexplained({key: accepted[key] for key in accepted
                             if key not in stale})
    for key in untriaged:
        print(f"reach_check: baselined without a SPEC or HOST disposition: {key}")
    return 1 if (arguments.strict and (fresh or untriaged)) else 0


if __name__ == "__main__":
    sys.exit(main())
