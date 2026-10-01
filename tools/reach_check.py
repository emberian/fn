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
seeded from every function a LOADED host file defines (one the image
builds, host/native/build.lisp and build-dtn.lisp, or the extraction world
tools/extract/world-host.lisp `ld' or `load'; a host file no build loads
seeds nothing, PKT-412, and tools/host_loaded_check.py refuses it), every book
symbol a loaded host file names.  Python development and checking tools
seed nothing: their book-symbol mentions are not served host lines.
A `defabsstobj' export is a function whose body is its :logic and
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
  a correspondence also counts when a reached export of the SAME stobj has
  a correspondence theorem explicitly using it, with matching logic/exec
  conclusions, and its exec directly calls NAME's exec.  This is named
  proof-dependency attribution, not equality of the exports or their effects;
  both the listing and `--explain' name the linking correspondence;
* failing that, a NAMED equality in books/ ties an unhosted subject U to a
  hosted H: a conclusion `(equal (U ..) (H x ..))' whose H side applies H to
  variables and constants only (not a commutation, not an unfolding into a
  constructor), or a refinement square `(equal (H .. (A x) ..) (A (U x ..)))'
  (store-log-kernel-concrete's fn-lgc-*-refines), or the square read with
  the abstraction the other way, `(equal (A .. (C ..) ..) (L .. (A ..) ..))'
  (A of what the hosted C leaves is L of A of the state before; the page
  store's pgs-x-commit-refines-commit), or a structural output projection
  `(equal (A (C x ..)) (L x ..))' over identical plain inputs: A only selects
  and reconstructs fields of C's answer (PKT-413's receiver result).
  `--explain' names it.  This last bridge covers the projected result, not
  the rest of C's output or effects.

WHAT IT CANNOT SEE.  A function reached only through a macro this reader
does not expand, or named in a Python string it does not recognize as a
symbol, and reachability is transitive: a book function a hosted function
calls is executed, so a keystone over a component (fn-cat-complete inside
the host's fn-sca-finish) is hosted even when the host-level theorem is a
different event.  The one macro it does expand is `fn-defrecord'
(books/defrecord.lisp): its generated recognizer is a definition here, whose
body is the record's `:fields' types, `:extra' conjuncts and
`:recognizer-formals' (PKT-394).  It also sees through a proof-only
ABBREVIATION in a statement: an unreached, non-recursive, branch-free
definition (or backquote macro) is read as the composition it names, so an
event over `fn-osi-live-store' is about `fn-own-store' of the owner the host
runs (PKT-376); a let-bound abbreviation is a model state only when what it
abbreviates is.  `$' and braces are symbol constituents
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


# The builds whose loads are the running server's host lines, each with the
# directory ACL2 runs it from: the two images, and the extraction world the
# served product (the SBCL core) is extracted from, which adds the FN-XO
# ports (host/store-open-host.lisp, store-write-host.lisp,
# interfaces-extract.lisp).  A host file no build loads is not a host line
# and seeds nothing (PKT-412); tools/host_loaded_check.py refuses one (Q7k).
IMAGE_BUILDS = {"host/native/build.lisp": ".",
                "host/native/build-dtn.lisp": ".",
                "tools/extract/world-host.lisp": "tools/extract"}
# A test image's build: what it loads is loaded (host_loaded_check), but a
# test image is not the server, so it seeds nothing here.
TEST_IMAGE_BUILDS = {"host/native/build-store-test.lisp": "."}
RAW_LOAD = re.compile(r'\(load\s+"([^"]+\.lisp)"')
RAW_LOAD_BESIDE = re.compile(r'\(load\s+\(merge-pathnames\s+"([^"]+\.lisp)"')


def loaded_host_files(builds=IMAGE_BUILDS, root: pathlib.Path = ROOT) -> set[str]:
    """Every host file BUILDS (a sequence of root-run builds, or a mapping of
    build to the directory it runs from) load, root-relative: the build script,
    each `ld' host file (an ld inside one in place: host_check.ld_sequence)
    and each raw file it `load's, following a raw file's own loads (a
    root-relative string, or a `merge-pathnames' beside the loading file)."""
    import host_check
    found: set[str] = set()
    work: list[str] = []
    for build in builds:
        if not (root / build).is_file():
            continue
        work.append(build)
        cbd = builds.get(build, ".") if isinstance(builds, dict) else "."
        work += host_check.ld_sequence(build, root, cbd=cbd)
    while work:
        relative = work.pop()
        if relative in found or not (root / relative).is_file():
            continue
        found.add(relative)
        text = (root / relative).read_text(encoding="utf-8", errors="replace")
        text = re.sub(r";[^\n]*", "", text)
        work += RAW_LOAD.findall(text)
        beside = pathlib.PurePosixPath(relative).parent
        work += [str(beside / name) for name in RAW_LOAD_BESIDE.findall(text)]
    return found


# A proof-only ABBREVIATION: a non-recursive, branch-free definition that
# names a composition of other functions (books/owner-store-indexed.lisp
# `fn-osi-live-store' is `(fn-own-store (fn-ocfg-owner (fn-osi-live-owner
# ...)))').  A theorem stated over it is a theorem over what it abbreviates:
# before 2026-09-29 reach_check read such an event as about the unreached
# abbreviation and reported it orphaned (PKT-376).  A branch (if, cond, and,
# or, mbe ...) makes a definition a function in its own right, never an
# abbreviation; a macro counts when its body is one backquoted template over
# plain formals.
ABBREVIATION_HEADS = ("defun", "defund", "defun-nx", "defun-inline", "defmacro")
BRANCHING = frozenset({"if", "cond", "case", "case-match", "and", "or", "mbe",
                       "mbt", "b*", "if*", "unquote-splicing", "&optional",
                       "&key", "&rest", "&body", "&whole",
                       # A binder sequences work (a stobj cleared, then
                       # loaded: fn-sca-load-history): an operation, not a name.
                       "let", "let*", "mv-let", "er-let*", "prog2$", "progn$"})


def proof_only(tree) -> bool:
    """Is a definition TREE proof-only: a macro, a `defun-nx', or declared
    `:verify-guards nil' or `:non-executable t'?  An executable function
    the host could call but does not is a function, never an abbreviation."""
    if tree[0] in ("defmacro", "defun-nx"):
        return True
    for item in tree[3:-1]:
        if isinstance(item, list) and item and item[0] == "declare":
            for decl in item[1:]:
                if isinstance(decl, list) and decl and decl[0] == "xargs":
                    pairs = dict(zip(decl[1::2], decl[2::2]))
                    if pairs.get(":verify-guards") == "nil" or pairs.get(":non-executable") == "t":
                        return True
    return False


def _as_tree(form):
    """A callgraph form (ledger.Sym symbols, plain-str string literals) as
    this reader's lower-case atom tree; a string literal reads as None."""
    if isinstance(form, list):
        return [_as_tree(item) for item in form]
    if isinstance(form, str):
        return str(form).lower() if type(form) is not str else None
    return str(form)


class Graph:
    """The call graph, and what a host line can reach through it."""

    def __init__(self) -> None:
        self.books = sorted(ROOT.glob("books/*.lisp"))
        self.hosts = (sorted(ROOT.glob("host/*.lisp"))
                      + sorted(ROOT.glob("host/native/*.lisp")))
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
        # A plain `defstobj' has no exports to read, but its creator is a
        # function ACL2 defines and runs: it is what an abstract stobj's
        # :creator executes (`:exec create-fn-arena$p'), so the edge from that
        # export reaches it, and a theorem concluding of `(create-NAME)' is
        # concluded of a reached function -- the premise audit's
        # establishment by the creator (tools/premise_audit.py).
        for sname, entry in self.stobjs.items():
            if entry["exports"]:
                continue
            self.book_defs.setdefault("create-" + sname, (
                entry["file"], "(defstobj-creator create-%s)" % sname))
        self.known = set(self.book_defs) | set(host_defs) | set(attached)

        bodies = {n: f for n, (_, f) in self.book_defs.items()}
        bodies.update({n: f for n, (_, f) in host_defs.items()})
        self.edges = {name: self.mentions(form, name)
                      for name, form in bodies.items()}
        for constrained, bound in attached.items():
            self.edges.setdefault(constrained, set()).update(bound)

        # Seeds: everything a LOADED host file defines, plus every book
        # symbol a loaded host file names.  Python tools seed nothing.
        # A host file no image build loads is not a host line (PKT-412):
        # it is named in `unloaded_hosts'.
        self.loaded_hosts = loaded_host_files()
        self.unloaded_hosts = sorted(str(p.relative_to(ROOT)) for p in self.hosts
                                     if str(p.relative_to(ROOT)) not in self.loaded_hosts)
        host_defs = {n: d for n, d in host_defs.items() if d[0] in self.loaded_hosts}
        seen = set(host_defs)
        # name -> what reached it: the calling definition, or the host file
        # that names it (`--explain' prints the chain).
        self.via = {name: host_defs[name][0] for name in host_defs}
        self.seeds = collections.Counter()
        for path in self.hosts:
            if str(path.relative_to(ROOT)) not in self.loaded_hosts:
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for symbol in self.symbols(text) & set(self.book_defs):
                if symbol not in seen:
                    seen.add(symbol)
                    self.via[symbol] = str(path.relative_to(ROOT))
                    self.seeds["host"] += 1
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

    def abbreviation(self, name: str):
        """(formals, body, macro?) when NAME is an unreached proof-only
        abbreviation (ABBREVIATION_HEADS' comment), else None."""
        cache = self.__dict__.setdefault("_abbreviations", {})
        if name in cache:
            return cache[name]
        found = None
        entry = self.book_defs.get(name)
        if entry is not None and name not in self.reachable:
            form = entry[1]
            if isinstance(form, str):
                import ledger
                try:
                    form = next(iter(ledger.Reader(form).top_level()))[0]
                except Exception:  # an unreadable text is no abbreviation
                    form = None
            tree = _as_tree(form)
            if (isinstance(tree, list) and len(tree) >= 4 and tree[0] in ABBREVIATION_HEADS
                    and isinstance(tree[2], list)
                    and all(isinstance(f, str) for f in tree[2]) and proof_only(tree)):
                formals, body = tree[2], tree[-1]
                macro = tree[0] == "defmacro"
                if macro:
                    body = (body[1] if isinstance(body, list) and len(body) == 2
                            and body[0] == "quasiquote" else None)
                symbols = tree_symbols(body) if body is not None else set()
                if (body is not None and isinstance(body, list) and name not in symbols
                        and not (symbols & BRANCHING) and not set(formals) & BRANCHING):
                    found = (formals, body, macro)
        cache[name] = found
        return found

    def unfold(self, term):
        """TERM, a call of an abbreviation, with the abbreviation's body in
        its place (the formals bound to TERM's arguments), else None."""
        if not isinstance(term, list) or not term or not isinstance(term[0], str):
            return None
        found = self.abbreviation(term[0])
        if found is None:
            return None
        formals, body, macro = found
        env = dict(zip(formals, term[1:]))
        if macro:
            def fill(t):
                if isinstance(t, list):
                    if len(t) == 2 and t[0] == "unquote" and isinstance(t[1], str):
                        return env.get(t[1], t[1])
                    return [fill(x) for x in t]
                return t
            return fill(body)
        return _substitute(body, env)

    def host_chain(self, name: str) -> list[str]:
        """How a host line reaches NAME: the host file (or stobj)
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
        callgraph.prune_cache()
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


def _substitute(term, env: dict):
    """TERM with each variable in ENV replaced by its bound term; a quoted
    constant is left alone (tools/premise_audit.py's rule)."""
    if isinstance(term, str):
        return env.get(term, term)
    if isinstance(term, list):
        if term and term[0] == "quote":
            return term
        return [_substitute(t, env) for t in term]
    return term


def split_statement(form: str, keep_binders: bool = False):
    """(hypotheses, conclusion) of a defthm FORM as s-expression trees.

    Nested `implies' in the conclusion are unfolded; the hints, rule
    classes and every other keyword argument are dropped.  A `let',
    `let*' or `mv-let' around the statement (or around an `implies'
    conclusion) is opened: `(let* ((o (open ...))) (implies (h o) (R o)))'
    has the hypothesis `(h (open ...))' and concludes `(R (open ...))', as
    the theorem does.  Until 2026-09-29 the reader stopped at the binder,
    read the whole let* as the conclusion and took the hypothesis predicate
    `h' for a subject (tools/premise_audit.py had the same blind spot,
    fixed on lane/closure-theorems for fn-scj-invp-at-install).

    With KEEP_BINDERS each hypothesis and the conclusion stay wrapped in the
    binders in scope at them instead of substituted: `hosted_call' tells a
    bound model state from a direct argument, and substitution would erase
    that difference."""
    tree = read_sexp(form)
    if not isinstance(tree, list) or len(tree) < 3:
        return [], None
    term, hyps, env, scope = tree[2], [], {}, []

    def place(one):
        if not keep_binders:
            return _substitute(one, env)
        for head, bindings in reversed(scope):
            one = [head, bindings, one] if head != "mv-let" else [head, bindings[0],
                                                                  bindings[1], one]
        return one
    while True:
        bound = _bindings(term)
        if bound is not None:
            pairs, body = bound
            if term[0] == "mv-let":
                scope.append(("mv-let", (term[1], term[2])))
            else:
                scope.append((term[0], term[1]))
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
            hyps.append(place(term[1]))
            term = term[2]
            continue
        break
    return hyps, place(term)


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
    unfolded = graph.unfold(term) if hasattr(graph, "unfold") else None
    if unfolded is not None:
        return model_state(unfolded, env, graph)
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
    unfolded = (graph.unfold(term) if isinstance(head, str) and head in subjects
                and hasattr(graph, "unfold") else None)
    if unfolded is not None:
        # An abbreviation the event is about: what it abbreviates is.
        widened = subjects | ((tree_symbols(unfolded) & set(graph.book_defs))
                              - graph.stobj_names)
        return hosted_call(unfolded, env, graph, widened)
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
    (directly, or as the generic export an `attach-stobj' runs it for).
    The audit may separately attribute a correspondence through the named,
    executable component link checked by `correspondence_bridges'."""

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
        bound_hyps, bound_conclusion = split_statement(form or "", keep_binders=True)
        self.term = (bound_conclusion if tree_symbols(conclusion) & set(self.functions)
                     else ["and"] + list(bound_hyps))

    def hosted(self, graph: "Graph") -> bool:
        if self.via == "export":
            return bool(set(self.functions) & graph.reachable)
        return hosted_call(self.term, {}, graph, set(self.functions))


def structural_result_projection(graph: "Graph", name: str) -> bool:
    """Does unary NAME only select/reconstruct its answer's fields?

    A one-sided abstraction needs this check: `(equal (constant (C x))
    (L x))' does not connect L to C's result.  This deliberately small
    grammar admits car/cdr selectors, nil fallbacks guarded by shape tests,
    list/cons reconstruction and local bindings.  It rejects payload
    transformations, arbitrary calls, constant-only results and macros.
    It recognizes an output observation, not equality of the whole machine.
    """
    entry = graph.book_defs.get(name)
    if not isinstance(entry, tuple) or len(entry) != 2:
        return False
    form = entry[1]
    tree = read_sexp(form) if isinstance(form, str) else _as_tree(form)
    if (not isinstance(tree, list) or len(tree) < 4
            or tree[0] not in ("defun", "defund", "defun-nx", "defun-inline")
            or not isinstance(tree[2], list) or len(tree[2]) != 1
            or not isinstance(tree[2][0], str) or tree[2][0] in ("nil", "t")):
        return False
    argument = tree[2][0]

    def shape(term, env):
        if not isinstance(term, list) or not term:
            return False
        head = term[0]
        if not isinstance(head, str):
            return False
        if head == "consp" and len(term) == 2:
            valid, retained, path = value(term[1], env)
            return valid and retained and path
        if head == "and" and len(term) > 1:
            return all(shape(arg, env) for arg in term[1:])
        return False

    def value(term, env):
        # (valid value, retains input, is a selector path rather than a
        # reconstructed result).  Selecting a constructed list could hide
        # a constant result, e.g. (car (cons nil answer)).
        if isinstance(term, str):
            if term in env:
                return env[term]
            return (True, True, True) if term == argument else (term == "nil", False, True)
        if not isinstance(term, list) or not term:
            return False, False, False
        head = term[0]
        if not isinstance(head, str):
            return False, False, False
        if term == ["quote", "nil"] or term == ["quote", []]:
            return True, False, True
        if re.fullmatch(r"c[ad]+r", head) and len(term) == 2:
            child = value(term[1], env)
            return child if child[2] else (False, False, False)
        if (head == "if" and len(term) == 4 and shape(term[1], env)
                and (term[3] == "nil" or term[3] == ["quote", "nil"]
                     or term[3] == ["quote", []])):
            yes, no = value(term[2], env), value(term[3], env)
            return yes[0] and no[0], yes[1] or no[1], yes[2] and no[2]
        if head == "list" or (head == "cons" and len(term) == 3):
            parts = [value(arg, env) for arg in term[1:]]
            return all(p[0] for p in parts), any(p[1] for p in parts), False
        if head in ("let", "let*") and len(term) == 3 and isinstance(term[1], list):
            inner = dict(env)
            for binding in term[1]:
                if (not isinstance(binding, list) or len(binding) != 2
                        or not isinstance(binding[0], str)):
                    return False, False, False
                bound = value(binding[1], inner if head == "let*" else env)
                if not bound[0]:
                    return False, False, False
                inner[binding[0]] = bound
            return value(term[2], inner)
        return False, False, False

    valid, retained, _ = value(tree[-1], {})
    return valid and retained


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
        # Output-only refinement over unchanged inputs.  Unlike the
        # two-sided squares below, A need not occur on the input side, so
        # verify it really is a structural projection of the result.
        for observed, logical in ((conclusion[1], conclusion[2]),
                                  (conclusion[2], conclusion[1])):
            if len(observed) != 2 or not isinstance(observed[1], list) or not observed[1]:
                continue
            concrete = observed[1]
            a, c, l = observed[0], concrete[0], logical[0]
            if (all(isinstance(n, str) and n in graph.book_defs for n in (a, c, l))
                    and len({a, c, l}) == 3 and len(concrete) > 1
                    and concrete[1:] == logical[1:]
                    and all(not isinstance(arg, list) or (len(arg) == 2 and arg[0] == "quote")
                            for arg in concrete[1:])
                    and structural_result_projection(graph, a)):
                bridges[l].append((c, tname))
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
        # The same square read the other way, with the abstraction A from
        # the concrete state to the logical one (books/pagestore-refine.lisp,
        # lane arena-store-5): `(equal (A .. (C ..) ..) (L .. (A ..) ..))',
        # A of what the concrete C leaves is the logical L applied to A of
        # the state before.  C is a direct argument of A (or its `mv-nth'
        # when C returns several values); every call L on the other side
        # with a direct argument (A ..) is tied to C.  A is the same
        # function on both sides, so a commutation of two unrelated calls
        # does not qualify, and neither does C = L.
        for absd, logical in ((conclusion[1], conclusion[2]), (conclusion[2], conclusion[1])):
            a_head = absd[0]
            if a_head not in graph.book_defs:
                continue
            concretes = set()
            for arg in absd[1:]:
                call = arg
                if (isinstance(call, list) and len(call) == 3 and call[0] == "mv-nth"
                        and isinstance(call[2], list) and call[2]):
                    call = call[2]
                if (isinstance(call, list) and call and isinstance(call[0], str)
                        and call[0] in graph.book_defs and call[0] != a_head):
                    concretes.add(call[0])
            if not concretes:
                continue
            work = [logical]
            while work:
                term = work.pop()
                if not isinstance(term, list) or not term or term[0] == "quote":
                    continue
                work.extend(term[1:])
                head = term[0]
                if (isinstance(head, str) and head in graph.book_defs and head != a_head
                        and any(isinstance(arg, list) and arg and arg[0] == a_head
                                for arg in term[1:])):
                    for c in concretes - {head}:
                        bridges[head].append((c, tname))
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


def correspondence_bridges(graph: "Graph", theorems: dict) -> dict[str, list]:
    """Event -> [(reached export, linking event)] for a narrow :use join.

    Both events must be real correspondence statements for exports of the
    same abstract stobj: (R (exec ...) (logic ...)), with the same R.  The
    reached export's exec must directly call the subject export's exec,
    and its theorem must :use the subject theorem by name, without a
    substitution.  This attributes the component proof to the served
    operation; it does NOT equate exports, propagate call reachability, or
    transfer unrelated properties (including {preserved}).
    """
    suffix = "{correspondence}"
    entries = {}
    for name, (_, form) in theorems.items():
        if not name.endswith(suffix):
            continue
        export = name[:-len(suffix)]
        owner = graph.export_of.get(export)
        if owner is None:
            continue
        logic, execf = graph.stobjs[owner]["exports"][export]
        _, conclusion = split_statement(form)
        if (not logic or not execf or not isinstance(conclusion, list)
                or len(conclusion) != 3 or not isinstance(conclusion[0], str)
                or not all(isinstance(t, list) and t for t in conclusion[1:])
                or conclusion[1][0] != execf or conclusion[2][0] != logic):
            continue
        entries[name] = (export, owner, execf, conclusion[0], form)

    def used_names(form):
        tree = read_sexp(form)
        # Only literal :hints / :use; a name in prose, :in-theory, or a
        # computed hint is not an explicit lemma instance.
        options = dict(zip(tree[3::2], tree[4::2]))
        found = set()
        for hint in options.get(":hints", []):
            if not isinstance(hint, list):
                continue
            for i, item in enumerate(hint[:-1]):
                if item != ":use":
                    continue
                value = hint[i + 1]
                uses = ([value] if isinstance(value, str)
                        or (isinstance(value, list) and value
                            and isinstance(value[0], str) and value[0].startswith(":"))
                        else value)
                if not isinstance(uses, list):
                    continue
                for use in uses:
                    if isinstance(use, str):
                        found.add(use)
                    elif (isinstance(use, list) and len(use) == 2
                          and use[0] == ":instance" and isinstance(use[1], str)):
                        found.add(use[1])
        return found

    bridges = collections.defaultdict(list)
    for linking, (export, owner, execf, relation, form) in sorted(entries.items()):
        if export not in graph.reachable:
            continue
        for target in sorted(used_names(form)):
            if target not in entries or target == linking:
                continue
            _, old_owner, old_exec, old_relation, _ = entries[target]
            if (owner == old_owner and relation == old_relation
                    and old_exec != execf and old_exec in graph.edges.get(execf, ())):
                bridges[target].append((export, linking))
    return bridges


def load_rows() -> list:
    registry = json.loads((ROOT / "planning" / "proofs.json").read_text())
    return registry["proofs"] if isinstance(registry, dict) else registry


def audit(graph: Graph, books: "set[str] | None" = None):
    """(findings, hosted, unresolved) over the registry's events; with BOOKS,
    only the events whose theorem one of those books defines (`--book')."""
    theorems = theorem_forms(graph.books)
    if books is not None:
        theorems = {name: entry for name, entry in theorems.items() if entry[0] in books}
    bridges = equality_bridges(graph, theorems)
    correspondences = correspondence_bridges(graph, theorems)
    rows = load_rows()

    findings, hosted, unresolved = [], 0, []
    graph.bridged = []
    graph.correspondence_bridged = []
    graph.declared = []
    for row in rows:
        declared = {str(k).lower(): str(v).lower()
                    for k, v in (row.get("keystone_subjects") or {}).items()}
        for event in row.get("events", []):
            name = str(event).lower()
            entry = theorems.get(name)
            if books is not None and entry is None:
                continue
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
            if subject.via == "export" and correspondences.get(name):
                other, linking = correspondences[name][0]
                hosted += 1
                graph.correspondence_bridged.append((row["id"], name, other, linking))
                continue
            findings.append(Finding(row["id"], name, book, subjects))
    return findings, hosted, unresolved


def theorem_names_of(graph: "Graph", books: set[str]) -> set[str]:
    return {name for name, (book, _) in theorem_forms(graph.books).items() if book in books}


def load_baseline() -> dict:
    if not BASELINE.exists():
        return {"accepted": {}}
    return json.loads(BASELINE.read_text())


PLACEHOLDER = "no one has said why that is right"
DISPOSITIONS = ("SPEC", "HOST", "UNREACHABLE-IN-COMPOSITION")


def unexplained(accepted: dict) -> list[str]:
    """Baselined orphans whose reason is not a disposition.

    Each entry says SPEC (a model or specification theorem kept, and why),
    HOST (the packet that will host it) or UNREACHABLE-IN-COMPOSITION (AGENTS.md:
    a branch the composed machine cannot reach); a bare acceptance is a flag nobody
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
    parser.add_argument("--book", action="append", default=[], metavar="PATH",
                        help="with --summary or the listing: only the registry events "
                             "these books define (the graph is still the whole tree's)")
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
        if subject.via == "export":
            for other, linking in correspondence_bridges(graph, theorems).get(name, ()):
                print(f"hosted through the named correspondence {linking}: "
                      f"{other} (reached) uses {name}")
                print("  " + " -> ".join(graph.host_chain(other)))
                return 0
        if set(subject.functions) & graph.reachable:
            print("NOT hosted: its reached subject is applied only to a model's state "
                  "(a let-bound call of an unreached function), and no named equality ties "
                  "the model to a reached function")
        else:
            print("NOT hosted: no reached subject, and no named equality to a reached function")
        return 0
    chosen = ({str((pathlib.Path(b) if pathlib.Path(b).is_absolute() else ROOT / b)
                   .resolve().relative_to(ROOT)) for b in arguments.book}
              if arguments.book else None)
    if chosen is not None and arguments.baseline:
        print("reach_check: --baseline rewrites the whole baseline; not with --book",
              file=sys.stderr)
        return 2
    findings, hosted, unresolved = audit(graph, chosen)

    if arguments.baseline:
        write_baseline(findings)
        print(f"reach_check: baseline rewritten with {len(findings)} accepted "
              f"orphan(s) in {BASELINE.relative_to(ROOT)}")
        return 0

    accepted = load_baseline().get("accepted", {})
    fresh = [f for f in findings if f.key() not in accepted]
    stale = sorted(set(accepted) - {f.key() for f in findings})
    if chosen is not None:
        # Only this book's events were judged: a baselined orphan elsewhere
        # is not "now hosted", it was not looked at.
        names = theorem_names_of(graph, chosen)
        judged = {key for key in accepted if key.split(":", 1)[-1] in names}
        stale = [key for key in stale if key in judged]
        accepted = {key: accepted[key] for key in judged}

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
        if graph.unloaded_hosts:
            print("host files no image build loads (no seeds): "
                  + ", ".join(graph.unloaded_hosts))
        print(f"{hosted} registry events hosted, {len(findings)} orphaned, "
              f"{len(fresh)} of those unbaselined, {len(unresolved)} "
              f"unresolvable here")

    for proof_id, event, export, linking in graph.correspondence_bridged:
        print(f"reach_check: {proof_id}:{event} hosted through the named "
              f"correspondence {linking}: {export} (reached) uses {event}")

    untriaged = unexplained({key: accepted[key] for key in accepted
                             if key not in stale})
    for key in untriaged:
        print(f"reach_check: baselined without a SPEC or HOST disposition: {key}")
    return 1 if (arguments.strict and (fresh or untriaged)) else 0


if __name__ == "__main__":
    sys.exit(main())
