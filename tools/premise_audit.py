#!/usr/bin/env python3
"""Premises assumed at a host entry that no host establishment proves.

B10 (operability review, 2026-09-29): a configuration record accepted on a
transaction-full store after an automatic checkpoint, then a clean stop,
left a store every open refused as checkpoint-damaged.  Refused POSTs on a
full budget consume transaction ids without records (fn-sn-refuse-reservation
advances the frontier); the open computed its frontier from the article
records alone; the replay's :frontier check then asked `every txid the node
reaches is below the frontier' -- a premise the writers never established.
No theorem said "a refused request has no effect on the state", and no
theorem said the open's premise is what a clean stop leaves.  Lane
owner-relation found the same shape by hand (PKT-888: fn-ocl-relation is
FALSE after fn-owner-open-peer, so every theorem assuming it at that entry is
vacuous on a real node), with a coverage table: host entry -> ACL2 function
-> the theorem that establishes or carries the relation.  This is that
table's method over the whole tree, generated:

  A PREMISE is a hypothesis conjunct `(R v ...)' of a defthm whose SUBJECT
  (what the conclusion calls: tools/reach_check.py's reader) a host line
  reaches, where R is a book-defined predicate and v a bare variable: the
  state R is assumed to hold of when the host enters.

  R is ESTABLISHED when some theorem concludes `(R (F ...))' (a conjunct of
  its conclusion, or `(equal (R ...) t)') without assuming R itself, and F,
  or a function inside R's argument, is host-reachable: the actual open,
  init or recovery makes R true.  R is ESTABLISHED OFF THE HOST PATH when
  every such theorem's F is unreachable (a model establishes it, nothing
  the host calls does).  R is PRESERVED ONLY when every theorem concluding
  R also assumes it (`(implies (R s) (R (step s)))' with no base case).
  R is NEVER CONCLUDED when no theorem concludes it at all.

  A FINDING is a premise whose R is never concluded, preserved only or
  established off the host path.  The premise's theorems are true; on the
  running node they say nothing until something the host calls makes R
  hold.  PKT-888's finding is the stronger one this reader cannot make (a
  hosted establishment exists for the open, but not for the peer open):
  the coverage table per entry is the lane's work; this is the list of
  where to start.

    python3 tools/premise_audit.py              # the findings, grouped by R
    python3 tools/premise_audit.py --summary    # the line `make check` prints
    python3 tools/premise_audit.py --strict     # non-zero on a finding NOT in
                                                # the baseline, or a baseline
                                                # entry that is no longer one
                                                # (shrink-only)
    python3 tools/premise_audit.py --baseline   # rewrite the baseline (deliberate)
    python3 tools/premise_audit.py --markdown   # the evidence record's table
    python3 tools/premise_audit.py --explain R  # every theorem assuming or
                                                # concluding R and why it counts

WHAT IS DELIBERATELY NOT COUNTED.  Recognizers a record macro generates
(reach_check.record_definitions: the shape of a tuple, established by its
constructor's theorem) and ACL2 primitives (natp, true-listp: not book
definitions).  A premise applied to a term (`(R (fn-sn-node s))') rather
than a variable is counted separately (`--all`), since the entry's state is
not what it is assumed of.  The baseline is per predicate: one hosted establishment clears every
theorem that assumes R.

GUARD-ESTABLISHED (PREMISE-CHECKER-GUARD-ESTABLISHED).  A premise (R v) of
theorem T is GUARD-ESTABLISHED when T's conclusion applies a subject S of T
to v at formal f, `(R f)' is a conjunct of S's declared `:guard', and every
way the native host reaches S is CHECKED.  The saved image runs with
guard-checking-on t (host/native/io.lisp faults otherwise), so fnn-call of a
:common-lisp-compliant entry through its executable counterpart checks the
entry's guard, and the entry's guard verification proves the guard of every
call its executed body makes, transitively (ec-call included; an mbe's
:logic is not executed).  So at every call of S that starts at a checked
entry, R holds of S's argument.  A native mention of a name is CHECKED only
when planning/interfaces.json declares it an entry of class
common-lisp-compliant that is neither `:raw-with' nor `:raw-guarded' (both
run the raw definition with the carried conjuncts held by preservation
theorems, not evaluated; host/native/io.lisp RAW DISPATCH) and is applied
directly nowhere.  Every other name the native code mentions -- a :program
or :ideal entry (a :program wrapper runs raw and establishes none of its
callees' guards), a raw-dispatched entry, a book function the native code
calls raw -- is UNCHECKED, and S is guard-established only when nothing
unchecked reaches it (the text call graph over-approximates the calls, so
an extra edge can only keep a premise a finding).  A subject declared
`:mode :program' or `:verify-guards nil', or defined in a book with a
`(program)' region, is never credited.  A guard-established theorem is
reported as its own class, never as a finding; R stays a finding while any
other hosted theorem assumes it without an establishment.

Repo-wide: run on a box (tools/remote_check.sh BOX --cmd '...'), never on
the laptop.
"""
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import reach_check  # noqa: E402

ROOT = reach_check.ROOT
BASELINE = ROOT / "planning" / "premise-baseline.json"

NEVER, PRESERVED, OFF_HOST, HOSTED = (
    "never concluded", "preserved only", "established off the host path",
    "established by a hosted entry")
FINDING_CLASSES = (NEVER, PRESERVED, OFF_HOST)
GUARD = "established by a checked guard"
INTERFACES = ROOT / "planning" / "interfaces.json"


def conjuncts(term) -> list:
    """The conjuncts of TERM: `(and a b)' unfolded, anything else itself."""
    out, work = [], [term]
    while work:
        t = work.pop()
        if isinstance(t, list) and t and t[0] == "and":
            work.extend(t[1:])
        else:
            out.append(t)
    return out


def predicate_application(term):
    """(R, argument) when TERM asserts a predicate of something: `(R a ...)',
    `(equal (R a ...) t)' or `(equal t (R a ...))'; else None."""
    if not isinstance(term, list) or not term or not isinstance(term[0], str):
        return None
    if term[0] == "equal" and len(term) == 3:
        for side, other in ((term[1], term[2]), (term[2], term[1])):
            if other == "t" and isinstance(side, list) and side and isinstance(side[0], str):
                return side[0], (side[1] if len(side) > 1 else None)
        return None
    if term[0] in ("not", "implies", "iff", "or", "if", "and"):
        return None
    return term[0], (term[1] if len(term) > 1 else None)


LOCAL_THEOREM = re.compile(r"\(local\s+\(defthmd?\s+([^\s()]+)", re.IGNORECASE)


def local_theorems(books) -> set[str]:
    """The theorems a book proves inside `(local ...)': a book-internal
    proof step whose hypotheses the book's own later events discharge.  It
    is never cited outside the book, so its hypotheses are no premise the
    host must establish; a non-local theorem that keeps the same hypothesis
    is audited in its own right."""
    out = set()
    for path in books:
        try:
            text = reach_check.file_text(path)
        except OSError:
            continue
        text = re.sub(r"(?m);.*$", "", text)   # a commented-out event is no event
        out.update(m.group(1).lower() for m in LOCAL_THEOREM.finditer(text))
    return out


def _substitute(term, env: dict):
    """TERM with each variable in ENV replaced by its bound term; a quoted
    constant is left alone."""
    if isinstance(term, str):
        return env.get(term, term)
    if isinstance(term, list):
        if term and term[0] == "quote":
            return term
        return [_substitute(t, env) for t in term]
    return term


def statement(form: str):
    """(hypotheses, conclusion) of a defthm FORM with the binders opened:
    a `let', `let*' or `mv-let' around the statement (or around the
    conclusion of an `implies') is substituted away, so `(let* ((o (open
    ...))) (implies (h o) (R o)))' concludes `(R (open ...))', as the
    theorem does.  reach_check.split_statement stops at the binder and
    would report no conclusion at all (fn-scj-invp-at-install, 2026-09-29)."""
    tree = reach_check.read_sexp(form)
    if not isinstance(tree, list) or len(tree) < 3:
        return [], None
    term, hyps, env = tree[2], [], {}
    while True:
        bound = reach_check._bindings(term)
        if bound is not None:
            pairs, body = bound
            for variables, value in pairs:
                value = _substitute(value, env)
                if len(variables) == 1:
                    env[variables[0]] = value
                else:
                    for i, v in enumerate(variables):
                        env[v] = ["mv-nth", str(i), value]
            term = body
            continue
        if isinstance(term, list) and len(term) == 3 and term[0] == "implies":
            hyps.append(_substitute(term[1], env))
            term = term[2]
            continue
        break
    return hyps, _substitute(term, env)



def _xargs(form) -> dict:
    """keyword -> [values] of every `(declare (xargs ...))' of a definition
    FORM (a callgraph form: Sym and str leaves, lists)."""
    out = collections.defaultdict(list)
    if not isinstance(form, list):
        return out
    for item in form[3:]:
        if not (isinstance(item, list) and item and item[0] == "declare"):
            continue
        for spec in item[1:]:
            if isinstance(spec, list) and spec and spec[0] == "xargs":
                for i in range(1, len(spec) - 1, 2):
                    if isinstance(spec[i], str):
                        out[spec[i].lower()].append(spec[i + 1])
    return out


def _plain(term):
    """A callgraph term as reach_check's reader writes one: lowercase symbol
    strings and lists."""
    if isinstance(term, list):
        return [_plain(t) for t in term]
    return term.lower() if isinstance(term, str) else term


class GuardModel:
    """Which book functions only CHECKED native entries reach (the
    GUARD-ESTABLISHED paragraph of the module docstring)."""

    def __init__(self, edges: dict, entries: dict, native_mentions: set,
                 definitions: dict, program_books: set) -> None:
        self.entries = entries
        self.definitions = definitions
        self.program_books = program_books
        self.checked_seeds = {n for n in native_mentions if self.checked_entry(n)}
        self.unchecked_seeds = set(native_mentions) - self.checked_seeds
        self.unchecked = self.closure(edges, self.unchecked_seeds)
        self.checked = self.closure(edges, self.checked_seeds)

    def checked_entry(self, name: str) -> bool:
        row = self.entries.get(name)
        return bool(row and row.get("class") == "common-lisp-compliant"
                    and not row.get("raw_with") and not row.get("raw_guarded")
                    and not row.get("applied_directly_in"))

    @staticmethod
    def closure(edges: dict, seeds) -> set:
        seen, work = set(seeds), list(seeds)
        while work:
            for nxt in edges.get(work.pop(), ()):
                if nxt not in seen:
                    seen.add(nxt)
                    work.append(nxt)
        return seen

    def only_checked(self, name: str) -> bool:
        return name in self.checked and name not in self.unchecked

    def guard_conjuncts(self, name: str):
        """(formals, [(R, formal)]) of NAME's declared guard, or None when it
        is not credited (no definition, :program, :verify-guards nil, a book
        with a (program) region)."""
        found = self.definitions.get(name)
        if not found:
            return None
        book, form = found
        if book in self.program_books or not isinstance(form, list) or len(form) < 4:
            return None
        if not (isinstance(form[0], str) and form[0].lower() in
                ("defun", "defund", "defun-inline", "defund-inline")):
            return None
        xargs = _xargs(form)
        if any(str(v).lower() == ":program" for v in xargs.get(":mode", ())):
            return None
        if any(str(v).lower() == "nil" for v in xargs.get(":verify-guards", ())):
            return None
        formals = [str(f).lower() for f in form[2]] if isinstance(form[2], list) else []
        apps = []
        for guard in xargs.get(":guard", ()):
            for conjunct in conjuncts(_plain(guard)):
                app = predicate_application(conjunct)
                if app and isinstance(app[1], str) and app[1] in formals:
                    apps.append(app)
        return formals, apps

    def establishes(self, r: str, var: str, conclusion, subjects) -> str | None:
        """The subject whose checked guard holds (R VAR) at T's conclusion,
        or None."""
        for s in subjects:
            if not self.only_checked(s):
                continue
            found = self.guard_conjuncts(s)
            if not found:
                continue
            formals, apps = found
            wanted = {f for rr, f in apps if rr == r}
            if not wanted:
                continue
            for call in _applications(conclusion, s):
                for i, arg in enumerate(call[1:]):
                    if arg == var and i < len(formals) and formals[i] in wanted:
                        return s
        return None


def _applications(term, name):
    """Every application `(NAME ...)' inside TERM."""
    out, work = [], [term]
    while work:
        t = work.pop()
        if isinstance(t, list) and t:
            if t[0] == "quote":
                continue
            if t[0] == name:
                out.append(t)
            work.extend(t)
    return out


def native_guard_model(graph) -> GuardModel:
    """The model over the tree: the native files the image loads, the
    declared entries, the host ACL2 files' definitions."""
    entries = {}
    if INTERFACES.exists():
        entries = {row["name"]: row for row in
                   json.loads(INTERFACES.read_text())["entries"]}
    acl2_hosts = [p for p in graph.hosts if "/native/" not in str(p)
                  and str(p.relative_to(ROOT)) in graph.loaded_hosts]
    host_defs = graph.read_definitions(acl2_hosts)
    known = set(graph.book_defs) | set(host_defs)
    mentions = set()
    for path in graph.hosts:
        rel = str(path.relative_to(ROOT))
        if "/native/" not in rel or rel not in graph.loaded_hosts:
            continue
        mentions |= graph.code_symbols(path.read_text(encoding="utf-8", errors="replace")) & known
    program_books = {str(p.relative_to(ROOT)) for p in graph.books
                     if any(line.strip() == "(program)" for line in
                            p.read_text(encoding="utf-8", errors="replace").splitlines())}
    definitions = {**graph.book_defs, **host_defs}
    return GuardModel(graph.edges, entries, mentions, definitions, program_books)


class Audit:
    def __init__(self, graph: reach_check.Graph, guard: "GuardModel | None" = None) -> None:
        self.graph = graph
        self.guard = guard
        self.book_defs = set(graph.book_defs)
        self.generated = set(reach_check.record_definitions(graph.books))
        self.theorems = reach_check.theorem_forms(graph.books)
        self.local = local_theorems(graph.books)
        # R -> [(theorem, book, argument-heads, hosted-establishment?)]
        self.concluded: dict[str, list] = collections.defaultdict(list)
        # R -> [theorem]: concluded under its own assumption (a preservation)
        self.preserving: dict[str, list] = collections.defaultdict(list)
        # R -> [(theorem, book, subject-hosted?, bare-variable?,
        #        the subject whose checked guard holds R there, or None)]
        self.assumed: dict[str, list] = collections.defaultdict(list)
        self.subjects: dict[str, reach_check.Subject] = {}
        self.scan()

    def predicate(self, name) -> bool:
        return (isinstance(name, str) and name in self.book_defs
                and name not in self.generated
                and name not in self.graph.stobj_names)

    def scan(self) -> None:
        reachable = self.graph.reachable
        for name, (book, form) in self.theorems.items():
            hyps, conclusion = statement(form)
            if conclusion is None:
                continue
            assumed_heads = set()
            for hyp in hyps:
                for conjunct in conjuncts(hyp):
                    app = predicate_application(conjunct)
                    if app is None or not self.predicate(app[0]):
                        continue
                    assumed_heads.add(app[0])
            for conjunct in conjuncts(conclusion):
                app = predicate_application(conjunct)
                if app is None or not self.predicate(app[0]):
                    continue
                r, arg = app
                if r in assumed_heads:
                    self.preserving[r].append(name)
                    continue  # a preservation, not an establishment
                heads = (reach_check.tree_symbols(arg) & self.book_defs) - self.graph.stobj_names
                hosted = bool(heads & reachable)
                self.concluded[r].append((name, book, sorted(heads), hosted))
            if not hyps or not assumed_heads or name in self.local:
                continue
            subject = reach_check.Subject(self.graph, name, form)
            self.subjects[name] = subject
            hosted_subject = subject.hosted(self.graph)
            for hyp in hyps:
                for conjunct in conjuncts(hyp):
                    app = predicate_application(conjunct)
                    if app is None or not self.predicate(app[0]):
                        continue
                    r, arg = app
                    bare = isinstance(arg, str) and arg not in self.book_defs
                    guarded = (self.guard.establishes(r, arg, conclusion, subject.functions)
                               if self.guard is not None and bare and hosted_subject
                               else None)
                    self.assumed[r].append((name, book, hosted_subject, bare, guarded))

    def classify(self, r: str) -> str:
        rows = self.concluded.get(r, [])
        if any(hosted for _, _, _, hosted in rows):
            return HOSTED
        if rows:
            return OFF_HOST
        return PRESERVED if self.preserving.get(r) else NEVER

    def premises(self, *, all_arguments: bool = False) -> dict[str, dict]:
        """R -> {class, theorems (hosted subject, bare variable), ...} for every
        R assumed at a hosted entry."""
        out = {}
        for r, rows in self.assumed.items():
            hosted_rows = [(t, b, guarded) for t, b, hosted, bare, guarded in rows
                           if hosted and (bare or all_arguments)]
            if not hosted_rows:
                continue
            entries = [(t, b) for t, b, guarded in hosted_rows if not guarded]
            by_guard = sorted({(t, guarded) for t, _, guarded in hosted_rows if guarded})
            cls = self.classify(r)
            if cls in FINDING_CLASSES and not entries:
                cls = GUARD
            out[r] = {"class": cls,
                      "theorems": sorted(set(entries)),
                      "guard_established": by_guard,
                      "establishments": sorted({t for t, _, _, h in self.concluded.get(r, []) if h}),
                      "unhosted_establishments": sorted(
                          {t for t, _, _, h in self.concluded.get(r, []) if not h}),
                      "preservations": sorted(set(self.preserving.get(r, [])))}
        return out

    def findings(self, *, all_arguments: bool = False) -> dict[str, dict]:
        return {r: row for r, row in self.premises(all_arguments=all_arguments).items()
                if row["class"] in FINDING_CLASSES}


def load_baseline() -> dict:
    if not BASELINE.exists():
        return {"accepted": {}}
    return json.loads(BASELINE.read_text())


def write_baseline(findings: dict) -> None:
    current = load_baseline()
    existing = current.get("accepted", {})
    accepted = {}
    for r in sorted(findings):
        accepted[r] = existing.get(r, findings[r]["class"] + "; no one has said which host entry establishes it")
    BASELINE.write_text(json.dumps(
        {"note": current.get("note") or (
            "Predicates assumed of a bare variable by a theorem whose subject a "
            "host line reaches, that no hosted theorem establishes (never "
            "concluded, preserved only, or established only by a model).  "
            "tools/premise_audit.py --strict fails on a premise NOT listed "
            "here and on a listed one that is no longer a finding, so the "
            "list can shrink and cannot grow silently.  Remove an entry by "
            "proving the establishment at the host entry (an open, an init, a "
            "recovery), never by editing this file."),
         "accepted": accepted}, indent=2, sort_keys=True) + "\n")


def summary_line(findings: dict, premises: dict, baseline: dict) -> str:
    counts = collections.Counter(row["class"] for row in findings.values())
    theorems = sum(len(row["theorems"]) for row in findings.values())
    return (f"premise_audit: {len(premises)} premises at hosted entries, "
            f"{len(findings)} unestablished ({theorems} theorems): "
            f"{counts[NEVER]} never concluded, {counts[PRESERVED]} preserved only, "
            f"{counts[OFF_HOST]} established off the host path; "
            f"{sum(1 for row in premises.values() if row['class'] == GUARD)} established "
            f"by a checked guard only; "
            f"baseline {len(baseline.get('accepted', {}))}")


def markdown(findings: dict, premises: dict) -> str:
    lines = ["| premise R | class | theorems assuming R at a hosted entry | establishments (unhosted) |",
             "| --- | --- | --- | --- |"]
    for r in sorted(findings, key=lambda k: (findings[k]["class"], k)):
        row = findings[r]
        names = ", ".join(f"`{t}`" for t, _ in row["theorems"][:6])
        if len(row["theorems"]) > 6:
            names += f" (+{len(row['theorems']) - 6})"
        est = ", ".join(f"`{t}`" for t in row["unhosted_establishments"][:3]) or "-"
        lines.append(f"| `{r}` | {row['class']} | {names} | {est} |")
    hosted = len(premises) - len(findings)
    lines.append("")
    lines.append(f"{len(premises)} premises assumed of a bare variable at a hosted entry; "
                 f"{hosted} established by a hosted entry; {len(findings)} findings.")
    return "\n".join(lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--summary", action="store_true", help="one line, the shape `make check` prints")
    parser.add_argument("--strict", action="store_true",
                        help="exit non-zero on a finding not in the baseline, or a baseline entry that is no longer one")
    parser.add_argument("--baseline", action="store_true",
                        help="rewrite planning/premise-baseline.json from this run")
    parser.add_argument("--markdown", action="store_true", help="the evidence record's table")
    parser.add_argument("--all", action="store_true",
                        help="count premises applied to a term as well as to a bare variable")
    parser.add_argument("--json", action="store_true", help="every premise, machine-readable")
    parser.add_argument("--explain", metavar="R", help="every theorem assuming or concluding R")
    parser.add_argument("--pattern", metavar="REGEX",
                        help="the listing, --markdown and --json: only premises whose name matches "
                             "(e.g. the relation-shaped ones: 'inv|relation|okp|statep|carried'); "
                             "never applied to --strict or --baseline")
    arguments = parser.parse_args(argv)

    graph = reach_check.Graph()
    audit = Audit(graph, native_guard_model(graph))

    if arguments.explain:
        r = arguments.explain.lower()
        print(f"{r}: {audit.classify(r) if r in audit.concluded else NEVER}")
        for t, b, heads, hosted in audit.concluded.get(r, []):
            print(f"  concluded by {t} ({b}) of {', '.join(heads) or 'a variable'}: "
                  f"{'HOSTED' if hosted else 'not hosted'}")
        for t, b, hosted, bare, guarded in audit.assumed.get(r, []):
            print(f"  assumed by {t} ({b}): subject {'hosted' if hosted else 'not hosted'}, "
                  f"of {'a bare variable' if bare else 'a term'}"
                  + (f", held by the checked guard of {guarded}" if guarded else ""))
        return 0

    premises = audit.premises(all_arguments=arguments.all)
    findings = audit.findings(all_arguments=arguments.all)
    baseline = load_baseline()

    if arguments.baseline:
        write_baseline(findings)
        print(f"premise_audit: baseline written, {len(findings)} entries")
        return 0
    if arguments.pattern and not arguments.strict:
        import re
        chosen = re.compile(arguments.pattern)
        premises = {r: row for r, row in premises.items() if chosen.search(r)}
        findings = {r: row for r, row in findings.items() if chosen.search(r)}
    if arguments.json:
        print(json.dumps(premises, indent=2, sort_keys=True))
        return 0
    if arguments.markdown:
        print(markdown(findings, premises))
        return 0

    line = summary_line(findings, premises, baseline)
    accepted = baseline.get("accepted", {})
    new = sorted(r for r in findings if r not in accepted)
    stale = sorted(r for r in accepted if r not in findings)
    if arguments.summary:
        print(line)
    else:
        for r in sorted(findings, key=lambda k: (findings[k]["class"], k)):
            row = findings[r]
            mark = "" if r in accepted else "  NEW"
            print(f"{r}: {row['class']}{mark}")
            for t, b in row["theorems"]:
                print(f"    {t} ({b})")
            for t, s in row["guard_established"]:
                print(f"    {t}: held by the checked guard of {s}")
            for t in row["unhosted_establishments"]:
                print(f"    established (unhosted) by {t}")
        print(line)
    if arguments.strict:
        for r in new:
            print(f"premise_audit: NEW unestablished premise {r} ({findings[r]['class']}): "
                  f"assumed by {', '.join(t for t, _ in findings[r]['theorems'][:3])}")
        for r in stale:
            print(f"premise_audit: baseline entry {r} is no longer a finding: remove it "
                  "(the baseline only shrinks)")
        return 1 if new or stale else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
