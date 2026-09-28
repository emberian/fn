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

WHAT IT MEASURES.  The call graph over `books/*.lisp' and `host/*.lisp',
seeded from every function `host/' defines, every book symbol a host file
names, and every book symbol a `tools/*.py' bridge names in a string --- the
bridges really do call ACL2 by building forms as text, so those are host
lines too.  A `defabsstobj' export is a function whose body is its :logic and
:exec functions, and `(attach-stobj GENERIC IMPL)' makes each GENERIC export
reach IMPL's export with the same :logic (the node's `fn-arena' runs
`fn-arena-paged''s pages); a live stobj's creator and recognizer run
whenever one of its exports does.

A registry event is HOSTED when its SUBJECT is (the keystone audit of
2026-09-27 found 16 events hosted by something else; AGENTS.md: "The subject
is the function the host calls"):
* the subject is the book functions its CONCLUSION calls (nested `implies'
  unfolded), less the stobj names (`fn-arena', `fn-cat', `state': a stobj is
  threaded, never the subject) and less the predicate each hypothesis
  conjunct applies (in `(implies (inv s) (inv (step s)))' the subject is
  `step').  Hints never count.  A conclusion that calls nothing takes its
  subject from the hypotheses;
* a hosted subject counts only where it is applied to arguments no MODEL
  computed: under `(let ((m (model-run evs))) (host-f (views m)))' host-f is
  applied to the model's state, and the event is about the model;
* a row's generated `keystone_subjects' map (tools/keystone_emit.py, lane
  defkeystone: {"<registry keystone>": "<subject function>"}) DECLARES the
  subject: the event is hosted exactly when a host line reaches that
  function, and the conclusion is not read;
* `NAME{correspondence}' and `NAME{preserved}' are about the export NAME;
* failing that, a NAMED equality in books/ ties an unhosted subject U to a
  hosted H: a conclusion `(equal (U ..) (H x ..))' whose H side applies H to
  variables and constants only (not a commutation, not an unfolding into a
  constructor), or a refinement square `(equal (H .. (A x) ..) (A (U x ..)))'
  (store-log-kernel-concrete's fn-lgc-*-refines).  `--explain' names it.

WHAT IT CANNOT SEE.  A function reached only through a macro this reader
does not expand, or named in a Python string it does not recognize as a
symbol, and reachability is transitive: a book function a hosted function
calls is executed, so a keystone over a component (fn-cat-complete inside
the host's fn-sca-finish) is hosted even when the host-level theorem is a
different event.  The one macro it does expand is `fn-defrecord'
(books/defrecord.lisp): its generated recognizer is a definition here, whose
body is the record's `:fields' types, `:extra' conjuncts and
`:recognizer-formals' (PKT-394).  `$' and braces are symbol constituents
(before 2026-09-27 `(defun fn-arena$lcorr ...)' read as a definition of
`fn-arena').

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

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import callgraph  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASELINE = ROOT / "planning" / "reach-baseline.json"

# `$' and braces are symbol constituents: `fn-arena$lcorr' is one symbol, not
# `fn-arena' followed by noise (before 2026-09-27 the DEFUN pattern stopped at
# the `$', so `(defun fn-arena$lcorr ...)' defined `fn-arena', and every
# theorem naming the stobj was hosted by it), and `fn-arena-paged-get{correspondence}'
# is one event name.
DEFUN = re.compile(r"\((?:defun|defund|defun-nx|define|defmacro)\s+([a-zA-Z0-9<>=/*+$-]+)")
DEFTHM = re.compile(r"\((?:defthm|defthmd)\s+([a-zA-Z0-9<>=/*+${}-]+)")
SYMBOL = re.compile(r"[a-zA-Z][a-zA-Z0-9<>=/*+${}-]*")
NAME = r"[a-zA-Z0-9<>=/*+$-]+"
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


def absstobjs(paths):
    """name -> {"exports": {export: (logic, exec)}, "file": rel} for every
    `defabsstobj' (and the plain stobj names of every `defstobj').

    An export is what a host line calls (`fn-arena-seal-list'); its :logic
    function is what theorems are stated over and its :exec function is what
    runs.  The recognizer and the creator are read as exports too.  A
    `defstobj' contributes only its name (to `stobj_names')."""
    found = {}
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        rel = str(path.relative_to(ROOT))
        for form in forms(text):
            head = re.match(r"\((defabsstobj|defstobj)\s", form, re.I)
            if not head:
                continue
            tree = read_sexp(form)
            if not tree or len(tree) < 2 or not isinstance(tree[1], str):
                continue
            entry = {"exports": {}, "file": rel}
            found[tree[1]] = entry
            if head.group(1).lower() == "defstobj":
                continue
            rest = tree[2:]
            keys = {rest[i]: rest[i + 1] for i in range(0, len(rest) - 1, 2)
                    if isinstance(rest[i], str) and rest[i].startswith(":")}
            specs = [keys.get(":recognizer"), keys.get(":creator")]
            specs += keys.get(":exports") or []
            for spec in specs:
                if not isinstance(spec, list) or not spec or not isinstance(spec[0], str):
                    continue
                opts = {spec[i]: spec[i + 1] for i in range(1, len(spec) - 1, 2)
                        if isinstance(spec[i], str)}
                logic, execf = opts.get(":logic"), opts.get(":exec")
                entry["exports"][spec[0]] = (
                    logic if isinstance(logic, str) else None,
                    execf if isinstance(execf, str) else None)
    return found


def stobj_attachments(paths) -> dict[str, set[str]]:
    """generic stobj -> the implementations `(attach-stobj GENERIC IMPL)'
    names.  At run time an export of GENERIC executes IMPL's export that
    shares its :logic function (books/payload-arena-attach.lisp)."""
    found: dict[str, set[str]] = collections.defaultdict(set)
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for form in forms(text):
            match = re.match(rf"\(attach-stobj\s+({NAME})\s+({NAME})\s*\)", form, re.I)
            if match:
                found[match.group(1).lower()].add(match.group(2).lower())
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

        # Definitions and their bodies come from tools/callgraph.py (the
        # ledger's reader: nested definitions and macro bodies included);
        # the generated record recognizers, stobj exports and attachments
        # are this checker's own additions.
        self.unreadable = {}
        self.book_defs = {**record_definitions(self.books),
                          **self.read_definitions(self.books)}
        host_defs = self.read_definitions(self.hosts)
        attached = attachments(self.books)
        # Abstract stobjs: each export is a callable book function whose body
        # is its :logic and :exec functions; an attached implementation's
        # export with the same :logic is what the generic's export runs.
        self.stobjs = absstobjs(self.books)
        self.stobj_names = set(self.stobjs) | {"state"}
        self.export_of = {}
        by_logic = collections.defaultdict(set)
        for sname, entry in self.stobjs.items():
            for export, (logic, execf) in entry["exports"].items():
                self.export_of[export] = sname
                if logic:
                    by_logic[(sname, logic)].add(export)
        stobj_attached = stobj_attachments(self.books)
        for sname, entry in self.stobjs.items():
            for export, (logic, execf) in entry["exports"].items():
                parts = [p for p in (logic, execf) if p]
                for impl in stobj_attached.get(sname, ()):
                    parts += sorted(by_logic.get((impl, logic), ()))
                self.book_defs.setdefault(export, (
                    entry["file"], "(defabsstobj-export %s %s)" % (export, " ".join(parts))))
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
        # name -> what reached it: the calling definition, or the host file
        # or bridge that names it (`--explain' prints the chain).
        self.via = {name: host_defs[name][0] for name in host_defs}
        self.seeds = collections.Counter()
        for path in self.hosts + self.bridges:
            label = "host" if path.suffix == ".lisp" else "bridge"
            text = path.read_text(encoding="utf-8", errors="replace")
            for symbol in self.symbols(text) & set(self.book_defs):
                if symbol not in seen:
                    seen.add(symbol)
                    self.via[symbol] = str(path.relative_to(ROOT))
                    self.seeds[label] += 1
        work = list(seen)
        while work:
            name = work.pop()
            for nxt in self.edges.get(name, ()):
                if nxt not in seen:
                    seen.add(nxt)
                    self.via[nxt] = name
                    work.append(nxt)
        # A live stobj is created and recognized by ACL2 itself, never by a
        # host line: its creator and recognizer run whenever an export does.
        for sname, entry in self.stobjs.items():
            exports = list(entry["exports"])
            if any(e in seen for e in exports):
                for e in exports[:2]:
                    if e not in seen:
                        seen.add(e)
                        self.via[e] = f"stobj {sname}"
                        work = [e]
                        while work:
                            name = work.pop()
                            for nxt in self.edges.get(name, ()):
                                if nxt not in seen:
                                    seen.add(nxt)
                                    self.via[nxt] = name
                                    work.append(nxt)
        self.reachable = seen & set(self.book_defs)

    def host_chain(self, name: str) -> list[str]:
        """How a host line reaches NAME: the host file (or bridge, or stobj)
        first, then each definition down to NAME.  Empty when unreached."""
        if name not in self.via:
            return []
        chain = [name]
        while chain[-1] in self.via and len(chain) < 200:
            parent = self.via[chain[-1]]
            chain.append(parent)
            if parent not in self.via or parent == chain[-2]:
                break
        return list(reversed(chain))

    def read_definitions(self, paths) -> dict:
        """name -> (file, form) for every definition callgraph reads in
        PATHS; a later file's definition of a name replaces an earlier's."""
        found = {}
        for path in paths:
            relative = str(path.relative_to(ROOT))
            definitions, error = callgraph.read_file(path, relative, records=False)
            if error is not None:
                self.unreadable[relative] = error
            for definition in definitions:
                found[definition.name] = (relative, definition.form)
        return found

    @staticmethod
    def symbols(text: str) -> set[str]:
        return {s.lower() for s in SYMBOL.findall(text)}

    def mentions(self, form, own: str) -> set[str]:
        """What a definition names: callgraph's edge for a read form, the
        symbols of the text this checker synthesises for the rest."""
        found = (self.symbols(form) if isinstance(form, str)
                 else callgraph.symbols(form[2:]))
        return found & self.known - {own}


class Finding:
    def __init__(self, proof_id, event, book, subjects, declared=False):
        self.proof_id, self.event = proof_id, event
        self.book, self.subjects = book, subjects
        self.declared = declared

    def key(self) -> str:
        return f"{self.proof_id}:{self.event}"

    def render(self) -> str:
        named = ", ".join(self.subjects[:4]) or "nothing this reader resolved"
        if self.declared:
            named = "its declared subject " + named
        return (f"{self.book}: {self.event} ({self.proof_id}): no host line "
                f"reaches any function it is about ({named}), so the running "
                f"server does not exercise what this event claims")


NESTED_DEFTHM = re.compile(r"\((?:defthm|defthmd)\s+([a-zA-Z0-9<>=/*+${}-]+)")


def theorem_forms(paths) -> dict:
    """name -> (file, form) for every `defthm'/`defthmd', including those
    inside an `encapsulate', `local', `defsection' or `progn' (a top-level
    only scan left such events unresolved, which passed them silently)."""
    found = {}
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        rel = str(path.relative_to(ROOT))
        for form in forms(text):
            for match in NESTED_DEFTHM.finditer(form):
                name = match.group(1).lower()
                if name in found:
                    continue
                inner = forms(form[match.start():])
                if inner:
                    found[name] = (rel, inner[0])
    return found


def split_statement(form: str):
    """(hypotheses, conclusion) of a defthm FORM as s-expression trees.
    Nested `implies' in the conclusion are unfolded; the hints, rule
    classes and every other keyword argument are dropped."""
    tree = read_sexp(form)
    if not isinstance(tree, list) or len(tree) < 3:
        return [], None
    term, hyps = tree[2], []
    while isinstance(term, list) and len(term) == 3 and term[0] == "implies":
        hyps.append(term[1])
        term = term[2]
    return hyps, term


def tree_symbols(tree) -> set[str]:
    if isinstance(tree, list):
        out: set[str] = set()
        for t in tree:
            out |= tree_symbols(t)
        return out
    return {tree} if isinstance(tree, str) else set()


def hypothesis_heads(hyps) -> set[str]:
    """The predicate each hypothesis conjunct applies: `(and (p x) (not (q
    y)))' gives {p, q}.  Only these are the recognizers a theorem assumes;
    a function called INSIDE a hypothesis (`(ok (parse x))') may well be the
    conclusion's subject too, and is not removed from it."""
    heads: set[str] = set()
    work = list(hyps)
    while work:
        term = work.pop()
        if not isinstance(term, list) or not term or not isinstance(term[0], str):
            continue
        if term[0] in ("and", "not"):
            work.extend(term[1:])
        else:
            heads.add(term[0])
    return heads


def equality_heads(tree):
    """The two call heads of an `(equal (F ...) (G ...))' conclusion."""
    if (isinstance(tree, list) and len(tree) == 3 and tree[0] == "equal"
            and isinstance(tree[1], list) and isinstance(tree[2], list)
            and tree[1] and tree[2]
            and isinstance(tree[1][0], str) and isinstance(tree[2][0], str)):
        return tree[1][0], tree[2][0]
    return None


def _bindings(term):
    """(pairs, body) of a let/let*/mv-let TERM, else None.  Each pair is
    (list of variables, bound term)."""
    if not isinstance(term, list) or not term or not isinstance(term[0], str):
        return None
    head = term[0]
    if head in ("let", "let*") and len(term) >= 3 and isinstance(term[1], list):
        pairs = [([b[0]], b[1] if len(b) > 1 else None)
                 for b in term[1] if isinstance(b, list) and b and isinstance(b[0], str)]
        return pairs, term[-1]
    if head == "mv-let" and len(term) >= 4 and isinstance(term[1], list):
        return [([v for v in term[1] if isinstance(v, str)], term[2])], term[-1]
    return None


def model_tainted(term, env, graph) -> bool:
    """Is TERM computed by a book function no host line reaches (a model),
    directly or through a variable bound to one?"""
    if isinstance(term, str):
        return env.get(term, False)
    if not isinstance(term, list) or not term:
        return False
    if term[0] == "quote":
        return False
    bound = _bindings(term)
    if bound:
        pairs, body = bound
        inner = dict(env)
        for names, value in pairs:
            tainted = model_state(value, inner, graph)
            for name in names:
                inner[name] = tainted
        return model_tainted(body, inner, graph)
    return any(model_tainted(arg, env, graph) for arg in term[1:])


def model_state(term, env, graph) -> bool:
    """Is a let-bound TERM a model's state: a call of an unreached book
    function (or built from a variable that is one)?  Only a BOUND state
    taints: `(host-f (spec-input x))' states the host function over a class
    of inputs and stays hosted; `(let ((m (model-run evs))) (host-f
    (model-views m)))' states it over the model's own state."""
    if isinstance(term, str):
        return env.get(term, False)
    if not isinstance(term, list) or not term or term[0] == "quote":
        return False
    head = term[0]
    if (isinstance(head, str) and head in graph.book_defs
            and head not in graph.reachable and head not in graph.stobj_names):
        return True
    return model_tainted(term, env, graph)


def hosted_call(term, env, graph, subjects) -> bool:
    """Does TERM apply a hosted subject to arguments no model computed?

    `(fn-ocv-reader-view (fn-ocvm-views m) w)' with m bound to the count
    machine's run is a statement about the model, though the host calls
    fn-ocv-reader-view: the reader-view models of PRF-288/296 passed the old
    check that way (keystone audit 2026-09-27, G1-1)."""
    if not isinstance(term, list) or not term or term[0] == "quote":
        return False
    bound = _bindings(term)
    if bound:
        pairs, body = bound
        inner = dict(env)
        for names, value in pairs:
            if hosted_call(value, inner, graph, subjects):
                return True
            tainted = model_state(value, inner, graph)
            for name in names:
                inner[name] = tainted
        return hosted_call(body, inner, graph, subjects)
    head = term[0]
    if (isinstance(head, str) and head in subjects and head in graph.reachable
            and not any(model_tainted(arg, env, graph) for arg in term[1:])):
        return True
    return any(hosted_call(arg, env, graph, subjects) for arg in term[1:])


class Subject:
    """What an event is about, as this reader decides it.

    The SUBJECT is the set of book functions its CONCLUSION calls, less the
    stobj names (`fn-arena', `fn-cat', `state': a stobj is threaded, not
    called) and less every function its hypotheses already name (a
    recognizer or invariant the step is assumed to start in -- in
    `(implies (inv s) (inv (step s)))' the subject is `step').  When that
    leaves nothing (the conclusion only restates a hypothesis predicate),
    the conclusion's own functions are the subject.  Hints never count: a
    hosted function named in a `:use' is not what the theorem claims.

    A `NAME{correspondence}' (or `{preserved}') event of a `defabsstobj' is
    about the export NAME: it is hosted when a host line calls that export
    (directly, or as the generic export an `attach-stobj' runs it for)."""

    def __init__(self, graph: "Graph", name: str, form: str | None) -> None:
        self.via = None
        brace = re.match(r"(.+)\{(correspondence|preserved)\}$", name)
        if brace and brace.group(1) in graph.export_of:
            self.functions = [brace.group(1)]
            self.via = "export"
            return
        hyps, conclusion = split_statement(form or "")
        functions = tree_symbols(conclusion) & set(graph.book_defs)
        functions -= graph.stobj_names
        assumed = hypothesis_heads(hyps) & set(graph.book_defs)
        narrowed = functions - assumed
        if not functions:
            # A conclusion that calls nothing (`(equal x :done)') states a
            # consequence of its hypotheses; what it is about is there.
            functions = (tree_symbols(hyps) & set(graph.book_defs)) - graph.stobj_names
            narrowed = functions
        self.functions = sorted(narrowed or functions)
        self.term = conclusion if tree_symbols(conclusion) & set(self.functions) else (
            ["and"] + list(hyps))

    def hosted(self, graph: "Graph") -> bool:
        if self.via == "export":
            return bool(set(self.functions) & graph.reachable)
        return hosted_call(self.term, {}, graph, set(self.functions))


def equality_bridges(graph: "Graph", theorems: dict) -> dict[str, list]:
    """function -> [(other, theorem)] for every `(equal (F ...) (G ...))'
    theorem conclusion in books/: a NAMED equality that ties an unhosted
    subject to a hosted function (AGENTS.md: "A theorem about another
    function counts only with a named theorem equating the two")."""
    bridges: dict[str, list] = collections.defaultdict(list)
    for tname, (_, form) in theorems.items():
        _, conclusion = split_statement(form)
        heads = equality_heads(conclusion)
        if not heads:
            continue
        # A refinement square `(equal (C .. (A x) ..) (A (L x ..)))': the
        # concrete C the host calls, over the abstraction A of a logical
        # state, is A of the logical step L (store-log-kernel-concrete's
        # fn-lgc-*-refines).  It ties L to C.
        for conc, absn in ((conclusion[1], conclusion[2]), (conclusion[2], conclusion[1])):
            if (len(absn) == 2 and isinstance(absn[1], list) and absn[1]
                    and isinstance(absn[1][0], str)
                    and any(isinstance(arg, list) and arg and arg[0] == absn[0]
                            for arg in conc[1:])
                    and conc[0] in graph.book_defs and absn[1][0] in graph.book_defs
                    and conc[0] != absn[1][0] and conc[0] != absn[0]):
                bridges[absn[1][0]].append((conc[0], tname))
        left, right = heads
        # A commutation `(equal (f (g x)) (g (f x)))' ties neither to the
        # other: each side must be free of the other side's head.
        if (tree_symbols(conclusion[1]) & {right}
                or tree_symbols(conclusion[2]) & {left}):
            continue
        # And an equality to a FUNCTION, not an unfolding: the side a
        # subject is tied TO applies its head to variables and constants
        # only.  `(equal (indexed g ns (build as)) (plain g ns as))' ties the
        # indexed scan to `plain'; `(equal (fence d bs) (fn-bs-make (files
        # bs) ..))' only says what the result is built from.
        def plain(side):
            return len(side) > 1 and not any(tree_symbols(arg) & set(graph.book_defs) for arg in side[1:])
        if left in graph.book_defs and right in graph.book_defs and left != right:
            if plain(conclusion[2]):
                bridges[left].append((right, tname))
            if plain(conclusion[1]):
                bridges[right].append((left, tname))
    return bridges


def load_rows() -> list:
    registry = json.loads((ROOT / "planning" / "proofs.json").read_text())
    return registry["proofs"] if isinstance(registry, dict) else registry


def audit(graph: Graph):
    theorems = theorem_forms(graph.books)
    bridges = equality_bridges(graph, theorems)
    rows = load_rows()

    findings, hosted, unresolved = [], 0, []
    graph.bridged = []
    graph.declared = []
    for row in rows:
        declared = {str(k).lower(): str(v).lower()
                    for k, v in (row.get("keystone_subjects") or {}).items()}
        for event in row.get("events", []):
            name = str(event).lower()
            entry = theorems.get(name)
            if name in declared:
                # A defkeystone names its subject (tools/keystone_emit.py's
                # generated `keystone_subjects'): that function's host
                # caller is checked, never a subject inferred from the
                # conclusion.
                function = declared[name]
                book = entry[0] if entry else "planning/proofs.json"
                if function not in graph.book_defs:
                    unresolved.append((row["id"], name,
                                       f"declared subject {function} is not a book definition"))
                elif function in graph.reachable:
                    hosted += 1
                    graph.declared.append((row["id"], name, function))
                else:
                    findings.append(Finding(row["id"], name, book, [function], declared=True))
                continue
            subject = Subject(graph, name, entry[1] if entry else None)
            if not entry and subject.via != "export":
                unresolved.append((row["id"], name, "no such defthm here"))
                continue
            book = entry[0] if entry else graph.stobjs[
                graph.export_of[subject.functions[0]]]["file"]
            subjects = subject.functions
            if not subjects:
                unresolved.append((row["id"], name, "no resolvable subject"))
                continue
            if subject.hosted(graph):
                hosted += 1
                continue
            tie = next(((s, other, t) for s in subjects
                        for other, t in bridges.get(s, ())
                        if other in graph.reachable), None)
            if tie:
                hosted += 1
                graph.bridged.append((row["id"], name) + tie)
                continue
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
    parser.add_argument("--explain", metavar="EVENT",
                        help="print what this reader takes EVENT's subject to be and why it is or is not hosted")
    arguments = parser.parse_args(argv)

    graph = Graph()
    for relative, error in sorted(graph.unreadable.items()):
        print(f"reach_check: {relative} unreadable, its definitions are missing: {error}")
    if arguments.explain:
        name = arguments.explain.lower()
        theorems = theorem_forms(graph.books)
        entry = theorems.get(name)
        for row in load_rows():
            declared = {str(k).lower(): str(v).lower()
                        for k, v in (row.get("keystone_subjects") or {}).items()}
            if name in declared:
                function = declared[name]
                print(f"{name}: declared subject {function} ({row['id']} keystone_subjects)")
                chain = graph.host_chain(function)
                if chain:
                    print("hosted: " + " -> ".join(chain))
                    return 0
                print("NOT hosted: no host line reaches the declared subject")
                return 0
        subject = Subject(graph, name, entry[1] if entry else None)
        print(f"{name}: {'defined in ' + entry[0] if entry else 'no defthm here'}")
        print("subject: " + (", ".join(
            f + (" (reached)" if f in graph.reachable else "") for f in subject.functions)
            or "nothing resolvable"))
        if subject.hosted(graph):
            print("hosted: a reached subject is applied to arguments no model computed")
            for f in subject.functions:
                if graph.host_chain(f):
                    print("  " + " -> ".join(graph.host_chain(f)))
            return 0
        bridges = equality_bridges(graph, theorems)
        for s in subject.functions:
            for other, tname in bridges.get(s, ()):
                if other in graph.reachable:
                    print(f"hosted through the named equality {tname}: {s} = {other} (reached)")
                    return 0
        if set(subject.functions) & graph.reachable:
            print("NOT hosted: its reached subject is applied only to a model's state "
                  "(a let-bound call of an unreached function), and no named equality ties "
                  "the model to a reached function")
        else:
            print("NOT hosted: no reached subject, and no named equality to a reached function")
        return 0
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
