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
  or a function inside R's argument, is host-reachable.  A hypothesis call
  receives no automatic credit.  A checked row in
  planning/premise-establishments.json can explicitly credit `(R v)' via
  a reachable outermost hypothesis call taking v directly.  Rows are
  written only by --register-establishment / --unregister-establishment
  and rechecked on every audit; invalid rows count for nothing.
  A conclusion `(if OK X t)' is read as X under the extra hypothesis OK.
  R is ESTABLISHED OFF THE HOST PATH when
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
    python3 tools/premise_audit.py --baseline-terms  # the term-premise baseline,
                                                # through the same ratchet
    python3 tools/premise_audit.py --lower-stale  # drop only the entries that are
                                                # no longer findings (adds none)
    python3 tools/premise_audit.py --markdown   # the evidence record's table
    python3 tools/premise_audit.py --explain R  # every theorem assuming or
                                                # concluding R and why it counts

WHAT IS DELIBERATELY NOT COUNTED.  Recognizers a record macro generates
(reach_check.record_definitions: the shape of a tuple, established by its
constructor's theorem) and ACL2 primitives (natp, true-listp: not book
definitions).  A premise applied to a term (`(R (fn-sn-node s))') rather
than a variable is counted separately, since the entry's state is not what
it is assumed of: a predicate assumed ONLY of terms at hosted entries is a
term finding, held to its own shrink-only baseline
(planning/premise-term-baseline.json, written by --baseline-terms, lowered
by --lower-stale), so --strict refuses a new one as it refuses a bare one
(`--all' still lists both together).  A variable is a symbol in any of R's
arguments that is not a numeral, keyword, character, t, nil or defined name
(`(R 0 x)' is of x; `(R 0 (F s))' of a term).  The baseline is per predicate: one hosted establishment clears every
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

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from tools import ratchet  # noqa: E402

ROOT = reach_check.ROOT
BASELINE = ROOT / "planning" / "premise-baseline.json"
# Premises stated of a term (`(R (nthcdr k rows))'), not of a bare variable:
# their own shrink-only baseline, so --strict sees them too (coordinator,
# 10-11, rule 6.4: a check that skips them silently is vacuous).
TERM_BASELINE = ROOT / "planning" / "premise-term-baseline.json"
ESTABLISHMENTS = ROOT / "planning" / "premise-establishments.json"

NEVER, PRESERVED, OFF_HOST, HOSTED = (
    "never concluded", "preserved only", "established off the host path",
    "established by a hosted entry")
FINDING_CLASSES = (NEVER, PRESERVED, OFF_HOST)
GUARD = "established by a checked guard"


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
    """(R, ARGUMENTS) when TERM asserts a predicate of something: `(R a ...)',
    `(equal (R a ...) t)' or `(equal t (R a ...))'; else None."""
    if not isinstance(term, list) or not term or not isinstance(term[0], str):
        return None
    if term[0] == "equal" and len(term) == 3:
        for side, other in ((term[1], term[2]), (term[2], term[1])):
            if other == "t" and isinstance(side, list) and side and isinstance(side[0], str):
                return side[0], list(side[1:])
        return None
    if term[0] in ("not", "implies", "iff", "or", "if", "and"):
        return None
    return term[0], list(term[1:])


_CONSTANT_ATOM = re.compile(r"^(?:[-+]?(?:\d+(?:/\d+)?|\d*\.\d+)|#[xXbBoO][-+]?[0-9a-fA-F]+|#\\.*|:.*|t|nil)$")


def variable_argument(arguments, defined) -> str | None:
    """The first of R's ARGUMENTS that is a variable: a symbol that is not a
    numeral, a keyword, a character, t or nil, and not a name the books
    define (a nullary call written bare).  An index or a constant in front
    of the subject does not make the premise one of a constant (A17,
    lane/vertical-lease: `(fn-rtc-free-slot 0 (fn-rtc-slots s))' was read
    as a premise of the variable `0')."""
    for arg in arguments:
        if isinstance(arg, str) and not _CONSTANT_ATOM.match(arg) and arg not in defined:
            return arg
    return None


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


def conclusion_branches(hyps, conclusion) -> list:
    """Normalize `(if OK X t)' to X under OK, scoped to that branch.
    Leave an ordinary conclusion intact (including its subject grouping)."""
    def conditional(term):
        return (isinstance(term, list) and len(term) == 4
                and term[0] == "if" and term[3] == "t")

    if conditional(conclusion):
        return conclusion_branches(hyps + [conclusion[1]], conclusion[2])
    if isinstance(conclusion, list) and conclusion and conclusion[0] == "and":
        ordinary, branches = [], []
        for term in conjuncts(conclusion):
            if conditional(term):
                branches.extend(conclusion_branches(hyps, term))
            else:
                ordinary.append(term)
        if branches:
            if ordinary:
                branches.insert(0, (hyps, ["and", *ordinary]))
            return branches
    return [(hyps, conclusion)]


def load_establishments(path):
    """Rows and format refusals; a missing register is empty, never written."""
    if not path.exists():
        return [], []
    try:
        rows = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        return [], [f"premise_audit: refused establishment register {path}: {error}"]
    if not isinstance(rows, list):
        return [], [f"premise_audit: refused establishment register {path}: expected a row list"]
    valid, errors, seen = [], [], set()
    for i, row in enumerate(rows):
        if (not isinstance(row, dict) or set(row) != {"premise", "theorem", "call"}
                or not all(isinstance(value, str) and value for value in row.values())):
            errors.append(f"premise_audit: refused registered row #{i + 1}: expected premise/theorem/call symbols")
            continue
        key = row["premise"], row["theorem"]
        if key in seen:
            errors.append(f"premise_audit: refused registered row {key[0]} {key[1]} via {row['call']}: duplicate premise/theorem")
        seen.add(key)
        valid.append(row)
    # An ambiguous or malformed register grants no credit.
    return ([], errors) if errors else (valid, [])


def _write_establishments(path, rows):
    """The register writer, called only by the tool's register operations."""
    rows = sorted(rows, key=lambda row: (row["premise"], row["theorem"], row["call"]))
    path.write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n")


def initialize_establishments(path) -> int:
    """Bootstrap an empty register without changing any existing rows."""
    if path.exists():
        print(f"premise_audit: refused initialization of {path}: register already exists")
        return 1
    _write_establishments(path, [])
    print(f"premise_audit: initialized empty establishment register {path}")
    return 0



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
                if app:
                    var = variable_argument(app[1], ())
                    if var in formals:
                        apps.append((app[0], var))
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


def _outermost_hypothesis_calls(hyps, defined):
    """First book calls beneath primitive conjunct roots, never below a
    book call or inside quoted data."""
    out, work = [], []
    for hyp in hyps:
        for term in conjuncts(hyp):
            if (isinstance(term, list) and term and isinstance(term[0], str)
                    and term[0] not in defined):
                work.append(term)
    while work:
        term = work.pop()
        if not (isinstance(term, list) and term and isinstance(term[0], str)):
            continue
        if term[0] == "quote":
            continue
        if term[0] in defined:
            out.append(term)
        else:
            work.extend(term[1:])
    return out


def native_guard_model(graph) -> GuardModel:
    """The model over the tree: the native files the image loads, the
    declared entries, the host ACL2 files' definitions."""
    from tools import interface_emit
    entries = {row["name"]: row for row in
               interface_emit.registry(ROOT)["entries"]}
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
    def __init__(self, graph: reach_check.Graph, guard: "GuardModel | None" = None,
                 establishments_path=None) -> None:
        self.graph = graph
        self.guard = guard
        self.book_defs = set(graph.book_defs)
        self.generated = set(reach_check.record_definitions(graph.books))
        self.theorems = reach_check.theorem_forms(graph.books)
        self.local = local_theorems(graph.books)
        self.establishments_path = establishments_path or ESTABLISHMENTS
        rows, self.refused_establishments = load_establishments(self.establishments_path)
        self.registered: dict[tuple[str, str], str] = {}
        for row in rows:
            r, t, f = row["premise"], row["theorem"], row["call"]
            problem = self.establishment_problem(r, t, f)
            if problem:
                self.refused_establishments.append(self.row_refusal(r, t, f, problem))
            else:
                self.registered[r, t] = f
        # R -> [(theorem, book, establishment-heads, hosted-establishment?)]
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

    def assumed_heads(self, hyps) -> set:
        out = set()
        for hyp in hyps:
            for conjunct in conjuncts(hyp):
                app = predicate_application(conjunct)
                if app is not None and self.predicate(app[0]):
                    out.add(app[0])
        return out

    def registered_match(self, r, f, hyps, conjunct) -> bool:
        app = predicate_application(conjunct)
        if app is None or app[0] != r or len(app[1]) != 1:
            return False
        var = variable_argument(app[1], self.book_defs)
        return var is not None and any(call[0] == f and var in call[1:]
                                       for call in _outermost_hypothesis_calls(hyps, self.book_defs))

    def establishment_problem(self, r, t, f) -> str | None:
        if t not in self.theorems:
            return "theorem is missing from the tree"
        if t in self.local:
            return "theorem is local"
        if not self.predicate(r):
            return "premise is not an audited book predicate"
        if f not in self.book_defs:
            return "call is not a book function"
        if f in self.graph.stobj_names:
            return "call is a stobj name"
        if f == r:
            return "call is the concluded predicate R"
        if f not in self.graph.reachable:
            return "call is not host-reachable"
        hyps, conclusion = statement(self.theorems[t][1])
        bare, preserving, shared = False, False, False
        for branch_hyps, branch in conclusion_branches(hyps, conclusion):
            assumed = self.assumed_heads(branch_hyps)
            for conjunct in conjuncts(branch):
                app = predicate_application(conjunct)
                if app is None or app[0] != r or len(app[1]) != 1:
                    continue
                var = variable_argument(app[1], self.book_defs)
                if var is None:
                    continue
                bare = True
                if r in assumed:
                    preserving = True
                    continue
                if self.registered_match(r, f, branch_hyps, conjunct):
                    return None
                shared |= any(var in call[1:] for hyp in branch_hyps for call in _applications(hyp, f))
        if not bare:
            return "conclusion has no (R v) with a single bare variable"
        if preserving:
            return "concluded premise is also assumed (preservation, not establishment)"
        if shared:
            return "call is not outermost below a primitive conjunct root (book roots and nested book calls excluded)"
        return "hypothesis call has no matching direct bare variable argument"

    @staticmethod
    def row_refusal(r, t, f, problem) -> str:
        return f"premise_audit: refused registered row {r} {t} via {f}: {problem}"

    def register_establishment(self, r, t, f) -> int:
        r, t, f = r.lower(), t.lower(), f.lower()
        problem = self.establishment_problem(r, t, f)
        if problem:
            print(self.row_refusal(r, t, f, problem))
            return 1
        rows, errors = load_establishments(self.establishments_path)
        if errors:
            print("\n".join(errors))
            return 1
        if any(row["premise"] == r and row["theorem"] == t for row in rows):
            print(self.row_refusal(r, t, f, "premise/theorem is already registered; unregister it first"))
            return 1
        _write_establishments(self.establishments_path, rows + [{"premise": r, "theorem": t, "call": f}])
        print(f"premise_audit: registered establishment {r} {t} via {f}")
        return 0

    def unregister_establishment(self, r, t) -> int:
        r, t = r.lower(), t.lower()
        rows, errors = load_establishments(self.establishments_path)
        if errors:
            print("\n".join(errors))
            return 1
        kept = [row for row in rows if (row["premise"], row["theorem"]) != (r, t)]
        if len(kept) == len(rows):
            print(f"premise_audit: refused unregister {r} {t}: no such registered row")
            return 1
        _write_establishments(self.establishments_path, kept)
        print(f"premise_audit: unregistered establishment {r} {t}")
        return 0

    def scan(self) -> None:
        reachable = self.graph.reachable
        for name, (book, form) in self.theorems.items():
            original_hyps, original_conclusion = statement(form)
            for hyps, conclusion in conclusion_branches(original_hyps, original_conclusion):
                self.scan_branch(name, book, form, hyps, conclusion,
                                 hyps != original_hyps or conclusion != original_conclusion, reachable)

    def scan_branch(self, name, book, form, hyps, conclusion, normalized, reachable) -> None:
        if conclusion is None:
            return
        assumed_heads = self.assumed_heads(hyps)
        for conjunct in conjuncts(conclusion):
            app = predicate_application(conjunct)
            if app is None or not self.predicate(app[0]):
                continue
            r, args = app
            if r in assumed_heads:
                self.preserving[r].append(name)
                continue  # a preservation, not an establishment
            # Every argument: an index-first predicate (R 0 (F ...)) is
            # established by its F as (R (F ...)) is (A17).
            heads = (reach_check.tree_symbols(args) & self.book_defs) - self.graph.stobj_names
            registered = self.registered.get((r, name))
            if registered and self.registered_match(r, registered, hyps, conjunct):
                heads = {registered}
            hosted = bool(heads & reachable)
            self.concluded[r].append((name, book, sorted(heads), hosted))
        if not hyps or not assumed_heads or name in self.local:
            return
        if normalized:
            form = reach_check.flatten(["defthm", name, ["implies", ["and", *hyps], conclusion]])
        subject = reach_check.Subject(self.graph, name, form)
        self.subjects[name] = subject
        hosted_subject = subject.hosted(self.graph)
        for hyp in hyps:
            for conjunct in conjuncts(hyp):
                app = predicate_application(conjunct)
                if app is None or not self.predicate(app[0]):
                    continue
                r, args = app
                var = variable_argument(args, self.book_defs)
                bare = var is not None
                guarded = (self.guard.establishes(r, var, conclusion, subject.functions)
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

    def term_findings(self) -> dict[str, dict]:
        """The findings only a premise of a term makes: R unestablished and
        assumed at a hosted entry of no bare variable (the bare ones are the
        main baseline's)."""
        bare = self.findings()
        return {r: row for r, row in self.findings(all_arguments=True).items() if r not in bare}


def load_baseline(path=None) -> dict:
    path = path or BASELINE
    if not path.exists():
        return {"accepted": {}}
    return json.loads(path.read_text())


TERM_NOTE = ("Predicates assumed only of a term (`(R (nthcdr k rows))'), not of a bare "
             "variable, by a theorem whose subject a host line reaches, that no hosted "
             "theorem establishes.  tools/premise_audit.py --strict fails on one NOT listed "
             "here and on a listed one that is no longer a finding; the list only shrinks "
             "(--lower-stale).  Remove an entry by establishing R of what the host passes, "
             "never by editing this file.")


def write_term_baseline(terms: dict) -> int:
    """The term baseline through the same ratchet: the first capture is the
    one initial capture (no history), every later write only shrinks."""
    current = load_baseline(TERM_BASELINE)
    existing = current.get("accepted", {})
    old = ratchet.old_rows("premise_audit_terms", TERM_BASELINE, lambda: dict.fromkeys(existing, 1))
    if ratchet.report("premise_audit_terms",
                      ratchet.refused("premise_audit_terms", old, dict.fromkeys(terms, 1))):
        return 1
    accepted = {r: existing.get(r, terms[r]["class"] + "; assumed of a term; no one has said "
                                "which host entry establishes it") for r in sorted(terms)}
    TERM_BASELINE.write_text(json.dumps({"note": current.get("note") or TERM_NOTE,
                                         "accepted": accepted}, indent=2, sort_keys=True) + "\n")
    return 0


def write_baseline(findings: dict) -> int:
    """Rewrite the baseline; it only shrinks (tools/ratchet.py): a new row needs an ACKS.md line."""
    current = load_baseline()
    existing = current.get("accepted", {})
    old = ratchet.old_rows("premise_audit", BASELINE, lambda: dict.fromkeys(existing, 1))
    if ratchet.report("premise_audit", ratchet.refused("premise_audit", old, dict.fromkeys(findings, 1))):
        return 1
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
    return 0


def lower_stale(findings: dict, baseline: dict, path=None) -> list[str]:
    """Remove from the baseline every accepted entry that is no longer a
    finding, keep every other entry as it is, and add none: what --strict
    names as stale leaves through this tool while other rows are still NEW
    (--baseline refuses a new row without an ACKS.md line, so it cannot
    shrink the file while any finding is unaccepted).  Returns the removed
    names."""
    accepted = baseline.get("accepted", {})
    stale = sorted(r for r in accepted if r not in findings)
    if stale:
        kept = {r: v for r, v in accepted.items() if r in findings}
        (path or BASELINE).write_text(json.dumps(dict(baseline, accepted=kept), indent=2, sort_keys=True) + "\n")
    return stale


def strict_verdict(findings: dict, accepted: dict, terms: dict, term_accepted: dict,
                   refused_establishments=()):
    """(lines, rc) of --strict: a finding of a bare variable or of a term not
    in its baseline, or a baseline entry of either that is no longer one."""
    lines = list(refused_establishments)
    for r in sorted(r for r in findings if r not in accepted):
        lines.append(f"premise_audit: NEW unestablished premise {r} ({findings[r]['class']}): "
                     f"assumed by {', '.join(t for t, _ in findings[r]['theorems'][:3])}")
    for r in sorted(r for r in accepted if r not in findings):
        lines.append(f"premise_audit: baseline entry {r} is no longer a finding: remove it "
                     "(the baseline only shrinks)")
    for r in sorted(r for r in terms if r not in term_accepted):
        lines.append(f"premise_audit: NEW unestablished premise of a term {r} ({terms[r]['class']}): "
                     f"assumed by {', '.join(t for t, _ in terms[r]['theorems'][:3])}")
    for r in sorted(r for r in term_accepted if r not in terms):
        lines.append(f"premise_audit: term baseline entry {r} is no longer a finding: remove it "
                     "(--lower-stale; the baseline only shrinks)")
    return lines, (1 if lines else 0)


def summary_line(findings: dict, premises: dict, baseline: dict,
                 terms: dict | None = None, term_baseline: dict | None = None) -> str:
    counts = collections.Counter(row["class"] for row in findings.values())
    theorems = sum(len(row["theorems"]) for row in findings.values())
    return (f"premise_audit: {len(premises)} premises at hosted entries, "
            f"{len(findings)} unestablished ({theorems} theorems): "
            f"{counts[NEVER]} never concluded, {counts[PRESERVED]} preserved only, "
            f"{counts[OFF_HOST]} established off the host path; "
            f"{sum(1 for row in premises.values() if row['class'] == GUARD)} established "
            f"by a checked guard only; "
            f"baseline {len(baseline.get('accepted', {}))}"
            + ("" if terms is None else
               f"; {len(terms)} more assumed only of a term, term baseline "
               f"{len((term_baseline or {}).get('accepted', {}))}"))


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
    parser.add_argument("--baseline-terms", action="store_true",
                        help="write planning/premise-term-baseline.json (the term premises) through the ratchet")
    parser.add_argument("--lower-stale", action="store_true",
                        help="drop the baseline entries that are no longer findings; add none")
    parser.add_argument("--markdown", action="store_true", help="the evidence record's table")
    parser.add_argument("--all", action="store_true",
                        help="count premises applied to a term as well as to a bare variable")
    parser.add_argument("--json", action="store_true", help="every premise, machine-readable")
    parser.add_argument("--explain", metavar="R", help="every theorem assuming or concluding R")
    register = parser.add_mutually_exclusive_group()
    register.add_argument("--register-establishment", nargs=3, metavar=("R", "T", "F"),
                          help="register a checked establishment of R by theorem T via call F")
    register.add_argument("--unregister-establishment", nargs=2, metavar=("R", "T"),
                          help="remove a registered establishment; refuse an absent row")
    register.add_argument("--init-establishments", action="store_true",
                          help="create an empty register only if it does not exist")
    parser.add_argument("--pattern", metavar="REGEX",
                        help="the listing, --markdown and --json: only premises whose name matches "
                             "(e.g. the relation-shaped ones: 'inv|relation|okp|statep|carried'); "
                             "never applied to --strict or --baseline")
    arguments = parser.parse_args(argv)

    if arguments.strict and (arguments.init_establishments or arguments.register_establishment
                             or arguments.unregister_establishment):
        parser.error("run register operations separately from --strict audits")
    if arguments.init_establishments:
        return initialize_establishments(ESTABLISHMENTS)
    graph = reach_check.Graph()
    audit = Audit(graph, native_guard_model(graph))
    for line in audit.refused_establishments:
        print(line)
    refusal_status = int(bool(audit.refused_establishments))
    if arguments.register_establishment:
        return audit.register_establishment(*arguments.register_establishment)
    if arguments.unregister_establishment:
        return audit.unregister_establishment(*arguments.unregister_establishment)
    if refusal_status and (arguments.baseline or arguments.baseline_terms or arguments.lower_stale):
        return 1

    if arguments.explain:
        r = arguments.explain.lower()
        print(f"{r}: {audit.classify(r) if r in audit.concluded else NEVER}")
        for t, b, heads, hosted in audit.concluded.get(r, []):
            print(f"  concluded by {t} ({b}) of {', '.join(heads) or 'a variable'}: "
                  f"{'HOSTED' if hosted else 'not hosted'}")
        for (premise, t), f in sorted(audit.registered.items()):
            if premise == r:
                print(f"  established by registered row {t} via {f}")
        for t, b, hosted, bare, guarded in audit.assumed.get(r, []):
            print(f"  assumed by {t} ({b}): subject {'hosted' if hosted else 'not hosted'}, "
                  f"of {'a bare variable' if bare else 'a term'}"
                  + (f", held by the checked guard of {guarded}" if guarded else ""))
        return refusal_status

    premises = audit.premises(all_arguments=arguments.all)
    findings = audit.findings(all_arguments=arguments.all)
    baseline = load_baseline()
    terms = audit.term_findings()
    term_baseline = load_baseline(TERM_BASELINE)

    if arguments.baseline_terms:
        if write_term_baseline(terms):
            return 1
        print(f"premise_audit: term baseline written, {len(terms)} entries")
        return 0

    if arguments.lower_stale:
        removed = lower_stale(findings, baseline)
        for r in removed:
            print(f"premise_audit: removed stale baseline entry {r}")
        print(f"premise_audit: {len(removed)} stale entr{'y' if len(removed) == 1 else 'ies'} removed, "
              f"{len(baseline.get('accepted', {})) - len(removed)} kept")
        if TERM_BASELINE.exists():
            gone = lower_stale(terms, term_baseline, TERM_BASELINE)
            for r in gone:
                print(f"premise_audit: removed stale term baseline entry {r}")
            print(f"premise_audit: {len(gone)} stale term entr{'y' if len(gone) == 1 else 'ies'} removed, "
                  f"{len(term_baseline.get('accepted', {})) - len(gone)} kept")
        return 0
    if arguments.baseline:
        if write_baseline(findings):
            return 1
        print(f"premise_audit: baseline written, {len(findings)} entries")
        return 0
    if arguments.pattern and not arguments.strict:
        import re
        chosen = re.compile(arguments.pattern)
        premises = {r: row for r, row in premises.items() if chosen.search(r)}
        findings = {r: row for r, row in findings.items() if chosen.search(r)}
    if arguments.json:
        print(json.dumps(premises, indent=2, sort_keys=True))
        return refusal_status
    if arguments.markdown:
        print(markdown(findings, premises))
        return refusal_status

    line = summary_line(findings, premises, baseline,
                        None if arguments.all else terms, term_baseline)
    term_accepted = term_baseline.get("accepted", {})
    accepted = baseline.get("accepted", {})
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
        if not arguments.all:
            for r in sorted(terms, key=lambda k: (terms[k]["class"], k)):
                mark = "" if r in term_accepted else "  NEW"
                print(f"{r}: {terms[r]['class']}, assumed only of a term{mark}")
                for t, b in terms[r]["theorems"]:
                    print(f"    {t} ({b})")
        print(line)
    if arguments.strict:
        lines, rc = strict_verdict(findings, accepted, {} if arguments.all else terms,
                                   {} if arguments.all else term_accepted,
                                   audit.refused_establishments)
        for text in lines:
            if text not in audit.refused_establishments:
                print(text)
        return rc
    return refusal_status


if __name__ == "__main__":
    sys.exit(main())
