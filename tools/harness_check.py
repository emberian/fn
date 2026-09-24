#!/usr/bin/env python3
"""Two static lints over the harness: caller signatures, and waived failures.

Both exist because of one incident.  On 2026-09-19 `receive_bpa_request` -- a
host entry point -- gained a required keyword-only `bundle`.  Its callers in
`tools/` were updated; two in `tests/` were not.  Python raises nothing until
the line runs, nothing in the tree ran those two lines, and both integration
labs were dead for a day while every `make check` was green.  The one gate
that could have said so, `tests/test_four_node_lab.py`, had a skip keyed on a
failure message, so it turned the dead lab into a SKIP.

So: one lint for the break, one for the thing that hid it.

**signatures** binds every resolvable call in `tools/`, `tests/` and `bin/`
against the definition it names, the way CPython would at the call: missing
required parameters, unexpected keywords, too many positionals, a parameter
given twice.  It resolves a call only when it can do so exactly -- an
`import`ed module attribute, an imported function, a constructor, or
`self.<method>` inside a class whose bases are all in the corpus -- and counts
what it declined to resolve rather than guessing.  It answers the question the
incident asked: *does every caller agree with the signature it calls today?*

**acl2-arity** asks the same question of two corpora no certification reads:
the 25 `ld`ed files under `host/`, and **ACL2 forms spelled inside Python
string literals**.  The second is the sharper target and the one neither side
can see.  `d484e9a` gave `fn-served-open` a seventh formal and updated both
Lisp callers; `tests/test_served_differential.py` spells that call as TEXT, so
all seven of its tests raised `FN-SERVED-OPEN takes 7 arguments ... given 6`
instead of comparing bytes, and the bridge host and `books/served` had no
divergence check running for a day.

It is the same class of defect as the Python half -- `books/owner.lisp`
stopped being includable when `fn-served-open` and `fn-served-make-conn` grew
two fields in a sibling cluster -- but not the same *mechanism*, and that
decided the scope.  A book needs no lint: `certify-book` refuses a wrong
arity itself, and what let that break persist was a stale certificate being
reported for a book that no longer certified, which content-keyed
certificates (docs/proofs.md) are the fix for.  A host file is never
certified, and a Lisp form in a Python string is not Lisp to anything until
it reaches ACL2.  `tools/host_check.py` answers the host half dynamically and
only when `FN_ACL2` names an ACL2; this is the always-on static half.  A first
version ran over `books/` too and produced 31 findings, every one an artefact
of reading Lisp with a lint-grade reader rather than with ACL2, which is the
argument against a second reader of the books.  Docstrings are prose and are
skipped; a form holding a `{}` or a `%s` is not decided at all, because a
`" ".join(...)` in that slot stands for any number of arguments.  This half
gates. Deliberately malformed forms used as test data carry a same-line
`# acl2-arity-fixture: fn-name reason` declaration, counted on every run; a
declaration for one callee never waives another on that line.

**waivers** flags a skip whose predicate reads a FAILURE rather than a
dependency: `if "<text>" in str(error): skipTest(...)`, a skip guarded by a
non-zero return code, a `skipUnless` over a response code.  An environmental
skip names something that is missing; a waiver names something that is broken,
and a waiver with no defect identifier and no expiry outlives its defect in
silence.  A flagged site may declare itself with a `# waiver-ok: <reason>`
comment; every accepted declaration is printed on every run, and one that
carries none is a finding.  It reads one hop of intra-function assignment and
no further -- a verdict that reached a guard through a helper, a JSON file or
another process is beyond a static reader, and those need the triage in
`tests/README.md` instead.

    python3 tools/harness_check.py            # all three, human output
    python3 tools/harness_check.py --json build/harness.json
    python3 tools/harness_check.py --lint signatures

Exit code 1 on any finding of a lint that gates (`signatures`, `acl2-arity`,
`waivers`),
0 otherwise; `--report` never fails and only prints.
"""
from __future__ import annotations

import argparse
import ast
from dataclasses import dataclass, field
import io
import json
from pathlib import Path
import re
import sys
import tokenize

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

# Where the harness lives.  `books/` and `host/` are Lisp and are the
# acl2-arity lint's corpus, not this one's.
PYTHON_TREES = ("tools", "tests", "bin")


# --------------------------------------------------------------------------
# the Python corpus
# --------------------------------------------------------------------------


@dataclass
class Signature:
    """One `def`, reduced to what a call site has to satisfy."""

    where: str            # "tools/run_bp_receive.py:113"
    qualname: str
    posonly: list[str] = field(default_factory=list)
    positional: list[str] = field(default_factory=list)
    kwonly: list[str] = field(default_factory=list)
    defaulted: set[str] = field(default_factory=set)
    vararg: bool = False
    kwarg: bool = False

    @property
    def required_positional(self) -> list[str]:
        return [name for name in self.posonly + self.positional
                if name not in self.defaulted]

    def bind(self, positions: int, keywords: list[str]) -> list[str]:
        """Every way this call fails, as CPython would report it."""
        problems: list[str] = []
        slots = self.posonly + self.positional
        if positions > len(slots) and not self.vararg:
            problems.append(
                "takes {} positional argument{} and {} were given".format(
                    len(slots), "" if len(slots) == 1 else "s", positions))
        filled = set(slots[:positions])
        seen: set[str] = set()
        for name in keywords:
            if name in seen:
                problems.append("got multiple values for keyword {!r}".format(name))
            seen.add(name)
            if name in filled:
                problems.append("got multiple values for argument {!r}".format(name))
            elif name in self.posonly:
                if not self.kwarg:
                    problems.append(
                        "{!r} is positional-only".format(name))
            elif name not in self.positional and name not in self.kwonly:
                if not self.kwarg:
                    problems.append("got an unexpected keyword argument {!r}".format(name))
        missing = [name for name in slots[positions:]
                   if name not in self.defaulted and name not in seen]
        missing += [name for name in self.kwonly
                    if name not in self.defaulted and name not in seen]
        if missing:
            problems.append("missing {} required argument{}: {}".format(
                len(missing), "" if len(missing) == 1 else "s",
                ", ".join(repr(name) for name in missing)))
        return problems


def signature_of(node, where: str, qualname: str, drop_self: bool) -> Signature:
    spec = node.args
    posonly = [arg.arg for arg in spec.posonlyargs]
    positional = [arg.arg for arg in spec.args]
    if drop_self:
        if posonly:
            posonly = posonly[1:]
        elif positional:
            positional = positional[1:]
    slots = posonly + positional
    defaulted = set(slots[len(slots) - len(spec.defaults):]) if spec.defaults else set()
    for arg, default in zip(spec.kwonlyargs, spec.kw_defaults):
        if default is not None:
            defaulted.add(arg.arg)
    return Signature(where=where, qualname=qualname, posonly=posonly,
                     positional=positional,
                     kwonly=[arg.arg for arg in spec.kwonlyargs],
                     defaulted=defaulted, vararg=spec.vararg is not None,
                     kwarg=spec.kwarg is not None)


@dataclass
class Module:
    relative: str
    dotted: str           # "tools.run_bp_receive"
    tree: ast.Module
    functions: dict = field(default_factory=dict)     # name -> Signature
    classes: dict = field(default_factory=dict)       # name -> (Signature|None, bases)
    methods: dict = field(default_factory=dict)       # (class, method) -> Signature
    rebound: set = field(default_factory=set)         # names assigned at any level
    imports: dict = field(default_factory=dict)       # local name -> ("module"|"name", target)


def dotted_name(relative: str) -> str:
    return relative[:-len(".py")].replace("/", ".")


def collect(root: Path) -> dict:
    modules: dict[str, Module] = {}
    for tree_name in PYTHON_TREES:
        base = root / tree_name
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.py")):
            relative = path.relative_to(root).as_posix()
            if "/__pycache__/" in relative or "/inn_lab_fake/" in relative:
                # The INN stand-in is a separate program run as scripts, and
                # its `bin/` shims are executed by name, never imported.
                continue
            try:
                parsed = ast.parse(path.read_text(encoding="utf-8"), filename=relative)
            except SyntaxError as error:
                modules[relative] = Module(relative, dotted_name(relative),
                                           ast.Module(body=[], type_ignores=[]))
                modules[relative].functions = {}
                print("harness_check: {} does not parse: {}".format(relative, error),
                      file=sys.stderr)
                continue
            module = Module(relative, dotted_name(relative), parsed)
            _describe(module, relative)
            modules[relative] = module
    return modules


def _describe(module: Module, relative: str) -> None:
    for node in module.tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            module.functions[node.name] = signature_of(
                node, "{}:{}".format(relative, node.lineno), node.name, False)
        elif isinstance(node, ast.ClassDef):
            bases = [base.id for base in node.bases if isinstance(base, ast.Name)]
            bases += [base.attr for base in node.bases if isinstance(base, ast.Attribute)]
            initialiser = None
            for item in node.body:
                if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    static = any(isinstance(d, ast.Name) and d.id == "staticmethod"
                                 for d in item.decorator_list)
                    signature = signature_of(
                        item, "{}:{}".format(relative, item.lineno),
                        "{}.{}".format(node.name, item.name), not static)
                    module.methods[(node.name, item.name)] = signature
                    if item.name == "__init__":
                        initialiser = signature
            module.classes[node.name] = (initialiser, bases)
    for node in ast.walk(module.tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module.imports[alias.asname or alias.name.split(".")[0]] = (
                    "module", alias.name)
        elif isinstance(node, ast.ImportFrom):
            source = node.module or ""
            for alias in node.names:
                if alias.name == "*":
                    continue
                module.imports[alias.asname or alias.name] = (
                    "from", "{}.{}".format(source, alias.name) if source else alias.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                               ast.For, ast.AsyncFor, ast.withitem,
                               ast.NamedExpr)):
            for target in _targets(node):
                module.rebound.add(target)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            spec = node.args
            for arg in (spec.posonlyargs + spec.args + spec.kwonlyargs
                        + ([spec.vararg] if spec.vararg else [])
                        + ([spec.kwarg] if spec.kwarg else [])):
                module.rebound.add(arg.arg)
        elif isinstance(node, ast.ExceptHandler) and node.name:
            module.rebound.add(node.name)


def _targets(node) -> list[str]:
    found = []
    candidates = []
    if isinstance(node, ast.Assign):
        candidates = node.targets
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        candidates = [node.target]
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        candidates = [node.target]
    elif isinstance(node, ast.withitem):
        candidates = [node.optional_vars] if node.optional_vars else []
    elif isinstance(node, ast.NamedExpr):
        candidates = [node.target]
    for candidate in candidates:
        for inner in ast.walk(candidate):
            if isinstance(inner, ast.Name):
                found.append(inner.id)
    return found


# --------------------------------------------------------------------------
# resolving a call
# --------------------------------------------------------------------------


class Corpus:
    def __init__(self, modules: dict):
        self.modules = modules
        self.by_dotted = {module.dotted: module for module in modules.values()}
        self.by_leaf: dict[str, list] = {}
        for module in modules.values():
            self.by_leaf.setdefault(module.dotted.rsplit(".", 1)[-1], []).append(module)

    def module_named(self, dotted: str):
        """The module a dotted or bare name refers to, when exactly one does."""
        if dotted in self.by_dotted:
            return self.by_dotted[dotted]
        leaf = dotted.rsplit(".", 1)[-1]
        found = self.by_leaf.get(leaf, [])
        return found[0] if len(found) == 1 else None

    def method_of(self, module: Module, class_name: str, method: str, depth: int = 0):
        """A method on a class, following bases that are in the corpus."""
        if depth > 4:
            return None
        signature = module.methods.get((class_name, method))
        if signature is not None:
            return signature
        entry = module.classes.get(class_name)
        if entry is None:
            return None
        for base in entry[1]:
            if base in module.classes:
                found = self.method_of(module, base, method, depth + 1)
                if found is not None:
                    return found
                continue
            target = module.imports.get(base)
            if target is None or target[0] != "from":
                continue
            other = self.module_named(target[1].rsplit(".", 1)[0])
            if other is None:
                continue
            found = self.method_of(other, base, method, depth + 1)
            if found is not None:
                return found
        return None

    def defines_class(self, module: Module, class_name: str, depth: int = 0) -> bool:
        """True when every base of the class is in the corpus (so a missing
        method really is missing, rather than inherited from somewhere we
        cannot see)."""
        if depth > 4:
            return False
        entry = module.classes.get(class_name)
        if entry is None:
            return False
        for base in entry[1]:
            if base in ("object",):
                continue
            if base in module.classes:
                if not self.defines_class(module, base, depth + 1):
                    return False
                continue
            target = module.imports.get(base)
            if target is None or target[0] != "from":
                return False
            other = self.module_named(target[1].rsplit(".", 1)[0])
            if other is None or not self.defines_class(other, base, depth + 1):
                return False
        return True


def resolve(corpus: Corpus, module: Module, call: ast.Call, class_name: str | None):
    """The signature this call names, or None when it cannot be pinned down."""
    func = call.func
    if isinstance(func, ast.Name):
        name = func.id
        if name in module.rebound:
            return None
        target = module.imports.get(name)
        if target and target[0] == "from":
            owner = corpus.module_named(target[1].rsplit(".", 1)[0])
            leaf = target[1].rsplit(".", 1)[-1]
            if owner is not None:
                if leaf in owner.functions:
                    return owner.functions[leaf]
                if leaf in owner.classes and owner.classes[leaf][0] is not None:
                    return owner.classes[leaf][0]
            return None
        if name in module.functions:
            return module.functions[name]
        if name in module.classes and module.classes[name][0] is not None:
            return module.classes[name][0]
        return None
    if isinstance(func, ast.Attribute):
        base, attribute = func.value, func.attr
        if isinstance(base, ast.Name) and base.id == "self" and class_name:
            if not corpus.defines_class(module, class_name):
                return None
            return corpus.method_of(module, class_name, attribute)
        if isinstance(base, ast.Name):
            if base.id in module.rebound:
                return None
            target = module.imports.get(base.id)
            if target is None:
                return None
            if target[0] == "module":
                owner = corpus.module_named(target[1])
                if owner is None:
                    return None
                if attribute in owner.functions:
                    return owner.functions[attribute]
                if attribute in owner.classes and owner.classes[attribute][0] is not None:
                    return owner.classes[attribute][0]
                return None
            # `from tools import run_bp_receive` binds a module under "from".
            owner = corpus.module_named(target[1])
            if owner is None:
                return None
            if attribute in owner.functions:
                return owner.functions[attribute]
            if attribute in owner.classes and owner.classes[attribute][0] is not None:
                return owner.classes[attribute][0]
            return None
        if isinstance(base, ast.Attribute) and isinstance(base.value, ast.Name):
            target = module.imports.get(base.value.id)
            if target is None:
                return None
            owner = corpus.module_named("{}.{}".format(target[1], base.attr))
            if owner is None:
                return None
            if attribute in owner.functions:
                return owner.functions[attribute]
            return None
    return None


def signature_findings(root: Path) -> tuple[list[dict], dict]:
    modules = collect(root)
    corpus = Corpus(modules)
    findings: list[dict] = []
    counts = {"calls": 0, "resolved": 0, "undecidable": 0}
    for module in modules.values():
        stack: list[str] = []

        class Walk(ast.NodeVisitor):
            def visit_ClassDef(self, node):
                stack.append(node.name)
                self.generic_visit(node)
                stack.pop()

            def visit_Call(self, node):
                counts["calls"] += 1
                signature = resolve(corpus, module, node,
                                    stack[-1] if stack else None)
                if signature is None:
                    self.generic_visit(node)
                    return
                if any(isinstance(arg, ast.Starred) for arg in node.args) or \
                        any(keyword.arg is None for keyword in node.keywords):
                    # `f(*rest)` / `f(**rest)`: the call is only decidable at
                    # run time, so this lint declines it and says how often.
                    counts["undecidable"] += 1
                    self.generic_visit(node)
                    return
                counts["resolved"] += 1
                problems = signature.bind(
                    len(node.args), [keyword.arg for keyword in node.keywords])
                for problem in problems:
                    findings.append({
                        "lint": "signatures",
                        "where": "{}:{}".format(module.relative, node.lineno),
                        "callee": signature.qualname,
                        "defined": signature.where,
                        "problem": problem,
                    })
                self.generic_visit(node)

        Walk().visit(module.tree)
    findings.sort(key=lambda row: row["where"])
    return findings, counts


# --------------------------------------------------------------------------
# the ACL2 half
# --------------------------------------------------------------------------

# Heads that bind, quote or name rather than apply.  Each is handled
# explicitly below: guessing at a binder's shape is how an arity lint invents
# a call out of a variable in a binding list.
OPAQUE = {"quote", "declare", "xargs", "ignore", "ignorable", "type"}
DEFINERS = {"defun", "defund", "defun-nx", "defund-nx", "defmacro", "define"}
NAMED = {"defthm", "defthmd", "defrule", "defruled", "defconst", "deftheory",
         "in-theory", "verify-guards", "defstobj", "table"}


def acl2_applications(form, found: list) -> None:
    """Every `(f a ...)` in application position, with its argument count.

    Conservative in one direction only: a form this does not understand is
    descended into as an application, and the caller keeps only the heads that
    name a `defun` of this tree, so an unrecognised binder can at worst
    produce a finding about a variable that shares a function's name.  Every
    binder fn actually uses is handled here.
    """
    if not isinstance(form, list) or not form:
        return
    head = form[0]
    name = head if isinstance(head, str) else None
    if name in OPAQUE:
        return
    if name in ("let", "let*"):
        # (let <bindings> <declare>* <body>); a binding is (var val).
        if len(form) > 1 and isinstance(form[1], list):
            for binding in form[1]:
                if isinstance(binding, list):
                    for value in binding[1:]:
                        acl2_applications(value, found)
        for item in form[2:]:
            acl2_applications(item, found)
        return
    if name in ("mv-let", "mv?-let"):
        # (mv-let (vars) <term> <declare>* <body>)
        for item in form[2:]:
            acl2_applications(item, found)
        return
    if name in ("b*",):
        # (b* <bindings> <body>...); a binding is (<pattern> <term>...).
        if len(form) > 1 and isinstance(form[1], list):
            for binding in form[1]:
                if isinstance(binding, list):
                    for value in binding[1:]:
                        acl2_applications(value, found)
        for item in form[2:]:
            acl2_applications(item, found)
        return
    if name == "lambda":
        for item in form[2:]:
            acl2_applications(item, found)
        return
    if name == "cond":
        for clause in form[1:]:
            if isinstance(clause, list):
                for item in clause:
                    acl2_applications(item, found)
        return
    if name in ("case", "case-match"):
        if len(form) > 1:
            acl2_applications(form[1], found)
        for clause in form[2:]:
            if isinstance(clause, list):
                for item in clause[1:]:
                    acl2_applications(item, found)
        return
    if name in DEFINERS:
        # (defun <name> (<formals>) <rest>...): neither the name nor the
        # formals list is an application.
        for item in form[3:]:
            acl2_applications(item, found)
        return
    if name in NAMED:
        for item in form[2:]:
            acl2_applications(item, found)
        return
    if name is not None and not name.startswith((":", "*", "#")):
        found.append((name, len(form) - 1))
    for item in form[1:]:
        acl2_applications(item, found)


# A `{...}` in a `.format` template, an f-string's `{expr}`, a `%s`: one
# placeholder stands for one atom here, and a form that contains one is not
# decided at all -- `" ".join(...)` in that slot would expand to any number
# of arguments and an arity finding over it would be a guess.
PLACEHOLDER = "fn--harness-placeholder"
PLACEHOLDER_PATTERN = re.compile(r"\{[^{}]*\}|%[-#0-9.*]*[sdrifxX]")
ACL2_FORM = re.compile(r"\(\s*fn-[a-z0-9-]+")
ARITY_FIXTURE = re.compile(
    r"#\s*acl2-arity-fixture:\s*(fn-[a-z0-9-]+)\s+([^\s#].*)$")


def declared_arity_fixture(source_line: str, callee: str) -> bool:
    """Waive only the named synthetic form on the same Python source line."""
    try:
        comments = (token.string for token in tokenize.generate_tokens(
            io.StringIO(source_line).readline) if token.type == tokenize.COMMENT)
        return any((match := ARITY_FIXTURE.fullmatch(comment)) is not None
                   and match.group(1) == callee and match.group(2).strip()
                   for comment in comments)
    except tokenize.TokenError:
        return False


def acl2_in_string(text: str) -> str | None:
    """A Python string literal, as an ACL2 form, or None if it is not one."""
    if not ACL2_FORM.search(text):
        return None
    return PLACEHOLDER_PATTERN.sub(PLACEHOLDER, text)


def python_acl2_forms(root: Path):
    """Every ACL2 form a Python file spells in a string literal.

    This is the shape neither the Lisp side nor the Python side can see.
    `d484e9a` gave `fn-served-open` a seventh formal and updated both Lisp
    callers; `tests/test_served_differential.py:57` spells that call as TEXT,
    so all seven of its tests raised `FN-SERVED-OPEN takes 7 arguments ...
    given 6` instead of comparing bytes, and the bridge host and
    `books/served` had no divergence check running for a day.  A lint that
    reads only `def` and call sites misses it entirely.

    Yields (relative path, line, form).  A string that does not parse whole
    is a fragment of a larger expression and is skipped; the caller counts
    how many.
    """
    from tools import ledger
    for tree_name in PYTHON_TREES:
        base = root / tree_name
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.py")):
            relative = path.relative_to(root).as_posix()
            if "/__pycache__/" in relative:
                continue
            try:
                parsed = ast.parse(path.read_text(encoding="utf-8"),
                                   filename=relative)
            except SyntaxError:
                continue
            # Prose, not code.  A docstring that names `(fn-own-outcome
            # through fn-served-post-outcome)` in a sentence is not a call,
            # and four of the first eight findings were exactly that.
            docstrings = {id(node.value) for scope in ast.walk(parsed)
                          if isinstance(scope, (ast.Module, ast.ClassDef,
                                                ast.FunctionDef,
                                                ast.AsyncFunctionDef))
                          for node in scope.body[:1]
                          if isinstance(node, ast.Expr)
                          and isinstance(node.value, ast.Constant)
                          and isinstance(node.value.value, str)}
            for node in ast.walk(parsed):
                if id(node) in docstrings:
                    continue
                if isinstance(node, ast.Constant) and isinstance(node.value, str):
                    text = node.value
                elif isinstance(node, ast.JoinedStr):
                    text = "".join(
                        part.value if isinstance(part, ast.Constant)
                        and isinstance(part.value, str) else PLACEHOLDER
                        for part in node.values)
                else:
                    continue
                candidate = acl2_in_string(text)
                if candidate is None:
                    continue
                try:
                    forms = ledger.Reader(candidate).top_level()
                except Exception:
                    yield relative, node.lineno, None
                    continue
                # A string that IS ACL2, not a sentence that mentions some.
                # `"... posting is the principal's allowance (fn-auth-postingp,
                # RFC 3977 section 6.3.1.1). The feed was never reached."`
                # parses, and its top level is mostly bare words; a form does
                # not have bare words at its top level.  Two findings on
                # `tools/v0_matrix.py` were exactly that sentence.
                if not forms or not all(isinstance(form, list) and form
                                        for form, _line in forms):
                    yield relative, node.lineno, None
                    continue
                for form, _line in forms:
                    yield relative, node.lineno, form


def acl2_findings(root: Path) -> tuple[list[dict], dict]:
    from tools import ledger

    books = {relative: ledger.analyze_book(path, relative)
             for path, relative in ledger.book_paths()}
    hosts = ledger.load_hosts()
    tree = ledger.Tree(books, ledger.makefile_roots(), hosts)
    macros: set[str] = set()
    for book in books.values():
        macros |= book.macros
    for host in hosts.values():
        macros |= host.macros
    arity = {name: len(function.formals)
             for name, function in tree.functions.items()
             if isinstance(function.formals, list) and name not in macros}
    findings: list[dict] = []
    counts = {"definitions": len(arity), "applications": 0,
              "host_files": len(hosts)}
    # Host files only, and on purpose.  A book's arity is ACL2's own business:
    # `certify-book` refuses a wrong one, so a book needs no lint, and what
    # let the `books/owner` break persist was a stale certificate rather than
    # a missing check.  A host file is `ld`ed and never certified, so nothing
    # reads it until a bridge starts up -- which is the Python half's problem
    # exactly, in Lisp.  `tools/host_check.py` answers it dynamically and only
    # when FN_ACL2 names an ACL2; this is the always-on static half.
    sources: list[tuple[str, list]] = [
        (relative, host.forms) for relative, host in sorted(hosts.items())]
    for relative, forms in sources:
        for form, line in forms:
            applications: list = []
            acl2_applications(form, applications)
            for name, count in applications:
                if name not in arity:
                    continue
                counts["applications"] += 1
                if count != arity[name]:
                    findings.append({
                        "lint": "acl2-arity",
                        "where": "{}:{}".format(relative, line),
                        "callee": name,
                        "problem": "called with {} argument{} and takes {}".format(
                            count, "" if count == 1 else "s", arity[name]),
                    })
    # The same question of the ACL2 that Python spells as text.
    counts["python_strings"] = 0
    counts["undecidable_strings"] = 0
    counts["declared_fixtures"] = 0
    python_lines: dict[str, list[str]] = {}
    for relative, line, form in python_acl2_forms(root):
        if form is None:
            counts["undecidable_strings"] += 1
            continue
        counts["python_strings"] += 1
        applications = []
        acl2_applications(form, applications)
        if any(name == PLACEHOLDER for name, _ in applications) or \
                PLACEHOLDER in repr(form):
            counts["undecidable_strings"] += 1
            continue
        for name, count in applications:
            if name not in arity:
                continue
            counts["applications"] += 1
            if count != arity[name]:
                if relative.startswith("tests/"):
                    lines = python_lines.setdefault(
                        relative,
                        (root / relative).read_text(encoding="utf-8").splitlines())
                    if declared_arity_fixture(lines[line - 1], name):
                        counts["declared_fixtures"] += 1
                        continue
                findings.append({
                    "lint": "acl2-arity",
                    "where": "{}:{}".format(relative, line),
                    "callee": name,
                    "problem": "spelled in a Python string with {} argument{} "
                               "and takes {}".format(
                                   count, "" if count == 1 else "s", arity[name]),
                })
    findings.sort(key=lambda row: row["where"])
    return findings, counts


# --------------------------------------------------------------------------
# the raw Common Lisp half
# --------------------------------------------------------------------------
#
# `acl2-arity` binds calls to ACL2 `defun`s.  The native host's own adapter
# functions are raw Common Lisp `defun`s in files the image `load`s under
# `(set-raw-mode t)`; ACL2 never translates them, and SBCL compiles a call
# with the wrong number of positional arguments into a runtime error at that
# call, or -- when the image is built without full warnings -- into a call that
# binds its arguments one slot early.  host/native/bp-app.lisp called
# `fnn-bpapp-accept-locked' (nine required parameters) with eight, dropping
# the ingress, and the application planner refused every request
# (planning/evidence/stale-native-tests-2026-09-24.md, finding 1).  Nothing
# in `make check` read that call.  **raw-arity** does: every `defun` in a
# raw-loaded host file gives a lambda list, and every application of that
# name in a raw-loaded file must supply between its required and its
# positional maximum (unbounded under `&rest', `&body' or `&key').  Names
# defined twice, or that are also ACL2 functions, are counted and not
# decided.  Backquote templates are not walked except for their unquoted
# forms: a template is code only once a macro expands it.

# The adapter reaches an ACL2 function through a dispatcher that takes its
# name quoted and its arguments spread: `(fnn-core 'fn-x a b)' applies
# fn-x to (a b), and a state-returning dispatcher appends `state'.  The
# number is how many arguments the dispatcher adds.  Each must keep the
# lambda list (name &rest args), or the lint reports the table as stale.
RAW_DISPATCHERS = {"fnn-call": 0, "fnn-core": 0, "fnn-core-state": 1,
                   "fnn-owner-core": 1, "fnn-owner-action": 1,
                   "fnn-bpapp-core-record": 1}

RAW_LAMBDA_KEYWORDS = {"&optional", "&rest", "&body", "&key", "&aux",
                       "&allow-other-keys", "&whole", "&environment"}
RAW_OPAQUE = {"quote", "declare", "declaim", "function", "in-package",
              "defpackage", "defstruct", "define-condition", "deftype",
              "defsetf", "defconstant", "defparameter", "defvar"}


def raw_lambda_range(formals) -> tuple[int, int | None] | None:
    """(required, positional maximum or None) of a raw lambda list."""
    if not isinstance(formals, list):
        return None
    required = 0
    optional = 0
    mode = "required"
    unbounded = False
    for item in formals:
        text = str(item) if isinstance(item, str) else None
        if text in RAW_LAMBDA_KEYWORDS:
            mode = text
            if text in ("&rest", "&body", "&key"):
                unbounded = True
            continue
        if mode == "required":
            required += 1
        elif mode == "&optional":
            optional += 1
    return required, (None if unbounded else required + optional)


def raw_applications(form, found: list, shadowed: frozenset = frozenset()) -> None:
    """Every `(f a ...)` a raw Common Lisp form evaluates, with its count."""
    if not isinstance(form, list) or not form:
        return
    head_ = form[0]
    name = str(head_) if isinstance(head_, str) else None

    def walk(items, local=shadowed):
        for item in items:
            raw_applications(item, found, local)

    if name is None:
        walk(form)
        return
    if name in RAW_OPAQUE:
        return
    if name == "quasiquote":
        def unquoted(x):
            if isinstance(x, list) and x:
                if isinstance(x[0], str) and str(x[0]) in ("unquote", "unquote-splicing"):
                    walk(x[1:])
                else:
                    for item in x:
                        unquoted(item)
        unquoted(form[1:])
        return
    if name in ("let", "let*", "symbol-macrolet"):
        for binding in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
            if isinstance(binding, list):
                walk(binding[1:])
        walk(form[2:])
        return
    if name in ("multiple-value-bind", "destructuring-bind", "multiple-value-setq",
                "lambda", "the", "mv-let"):
        walk(form[2:])
        return
    if name in ("flet", "labels", "macrolet"):
        local = set(shadowed)
        bindings = form[1] if len(form) > 1 and isinstance(form[1], list) else []
        for binding in bindings:
            if isinstance(binding, list) and binding and isinstance(binding[0], str):
                local.add(str(binding[0]))
        local = frozenset(local)
        for binding in bindings:
            if isinstance(binding, list):
                walk(binding[2:], local if name == "labels" else shadowed)
        walk(form[2:], local)
        return
    if name in ("dolist", "dotimes"):
        if len(form) > 1 and isinstance(form[1], list):
            walk(form[1][1:])
        walk(form[2:])
        return
    if name in ("do", "do*"):
        for binding in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
            if isinstance(binding, list):
                walk(binding[1:])
        if len(form) > 2 and isinstance(form[2], list):
            walk(form[2])
        walk(form[3:])
        return
    if name == "cond":
        for clause in form[1:]:
            if isinstance(clause, list):
                walk(clause)
        return
    if name in ("case", "ecase", "ccase", "typecase", "etypecase", "ctypecase"):
        if len(form) > 1:
            raw_applications(form[1], found, shadowed)
        for clause in form[2:]:
            if isinstance(clause, list):
                walk(clause[1:])
        return
    if name in ("handler-case", "restart-case"):
        if len(form) > 1:
            raw_applications(form[1], found, shadowed)
        for clause in form[2:]:
            if isinstance(clause, list):
                walk(clause[2:])
        return
    if name == "handler-bind":
        for binding in (form[1] if len(form) > 1 and isinstance(form[1], list) else []):
            if isinstance(binding, list):
                walk(binding[1:])
        walk(form[2:])
        return
    if name in ("block", "return-from", "catch", "throw"):
        walk(form[2:] if name in ("block", "return-from") else form[1:])
        return
    if name in ("defun", "defmacro", "defun-inline", "defund", "defmethod"):
        walk(form[3:])
        return
    if name.startswith("with-") and len(form) > 1 and isinstance(form[1], list):
        walk(form[1][1:])
        walk(form[2:])
        return
    if name in ("funcall", "apply") and len(form) > 1:
        target = form[1]
        if (name == "funcall" and isinstance(target, list) and len(target) == 2
                and isinstance(target[0], str) and str(target[0]) == "function"
                and isinstance(target[1], str) and str(target[1]) not in shadowed):
            found.append((str(target[1]), len(form) - 2))
        walk(form[1:])
        return
    if name in RAW_DISPATCHERS and len(form) > 1:
        target = form[1]
        if (isinstance(target, list) and len(target) == 2
                and isinstance(target[0], str) and str(target[0]) == "quote"
                and isinstance(target[1], str)):
            found.append(("'" + str(target[1]).lower(),
                          len(form) - 2 + RAW_DISPATCHERS[name]))
    if name not in shadowed and not name.startswith((":", "&")):
        found.append((name, len(form) - 1))
    walk(form[1:])


def raw_definitions(sources: dict[str, list]) -> tuple[dict, set]:
    """Raw `defun` name -> (required, maximum, where); names defined twice."""
    seen: dict[str, list] = {}
    for relative, forms in sorted(sources.items()):
        def visit(form, line):
            if not isinstance(form, list) or not form or not isinstance(form[0], str):
                return
            name = str(form[0])
            if name in ("progn", "progn!", "eval-when", "locally"):
                for item in form[1:]:
                    visit(item, line)
                return
            if name == "defun" and len(form) >= 3 and isinstance(form[1], str):
                bounds = raw_lambda_range(form[2])
                if bounds is not None:
                    seen.setdefault(str(form[1]), []).append(
                        (bounds[0], bounds[1], "{}:{}".format(relative, line)))
        for form, line in forms:
            visit(form, line)
    defined = {}
    ambiguous = set()
    for name, rows in seen.items():
        if len({(low, high) for low, high, _ in rows}) == 1:
            defined[name] = rows[0]
        else:
            ambiguous.add(name)
    return defined, ambiguous


def raw_arity_scan(sources: dict[str, list], exclude: set[str] = frozenset(),
                   acl2_arity: dict[str, int] | None = None
                   ) -> tuple[list[dict], dict]:
    """Findings over SOURCES: relative path -> [(form, line)] of raw files.

    EXCLUDE names ACL2 functions (not decided as raw); ACL2_ARITY, when
    given, is the formal count of each ACL2 function a dispatcher may name.
    """
    defined, ambiguous = raw_definitions(sources)
    for name in list(defined):
        if name in exclude:
            del defined[name]
            ambiguous.add(name)
    acl2_arity = acl2_arity or {}
    findings: list[dict] = []
    counts = {"raw_files": len(sources), "raw_definitions": len(defined),
              "undecided_definitions": len(ambiguous), "applications": 0,
              "dispatched_applications": 0}
    if acl2_arity:
        for name in sorted(RAW_DISPATCHERS):
            row = defined.get(name)
            if row is None or (row[0], row[1]) != (1, None):
                findings.append({
                    "lint": "raw-arity", "where": row[2] if row else "tools/harness_check.py",
                    "callee": name,
                    "problem": "RAW_DISPATCHERS names it, but it is not a raw "
                               "(name &rest args) defun"})
    for relative, forms in sorted(sources.items()):
        for form, line in forms:
            applications: list = []
            raw_applications(form, applications)
            for name, count in applications:
                if name.startswith("'"):
                    callee = name[1:]
                    if callee not in acl2_arity:
                        continue
                    counts["dispatched_applications"] += 1
                    if count != acl2_arity[callee]:
                        findings.append({
                            "lint": "raw-arity",
                            "where": "{}:{}".format(relative, line),
                            "callee": callee,
                            "problem": "dispatched with {} argument{} (state "
                                       "included) and takes {}".format(
                                           count, "" if count == 1 else "s",
                                           acl2_arity[callee]),
                        })
                    continue
                if name not in defined:
                    continue
                low, high, where = defined[name]
                counts["applications"] += 1
                if count < low or (high is not None and count > high):
                    wanted = (str(low) if high == low else
                              "{} to {}".format(low, high) if high is not None
                              else "at least {}".format(low))
                    findings.append({
                        "lint": "raw-arity",
                        "where": "{}:{}".format(relative, line),
                        "callee": name,
                        "defined": where,
                        "problem": "called with {} argument{} and takes {}".format(
                            count, "" if count == 1 else "s", wanted),
                    })
    findings.sort(key=lambda row: row["where"])
    return findings, counts


def raw_arity_findings(root: Path) -> tuple[list[dict], dict]:
    from tools import ledger

    books = {relative: ledger.analyze_book(path, relative)
             for path, relative in ledger.book_paths()}
    hosts = ledger.load_hosts()
    tree = ledger.Tree(books, ledger.makefile_roots(), hosts)
    raw = ledger.raw_host_paths(tree)
    sources = {relative: hosts[relative].forms for relative in raw}
    macros: set[str] = set()
    for book in books.values():
        macros |= book.macros
    for host in hosts.values():
        macros |= host.macros
    arity = {name: len(function.formals)
             for name, function in tree.functions.items()
             if isinstance(function.formals, list) and name not in macros}
    # The ACL2-mode host wrappers (`fn-owner-*', `fn-tcl-host-*', ...) are
    # most of what the adapter dispatches to, and no book defines them.
    from tools import host_shape_check
    wrappers: list = []
    for relative, host in sorted(hosts.items()):
        if relative in raw:
            continue
        for form, _line in host.forms:
            host_shape_check.definitions_in(form, relative, True, wrappers)
    seen: dict[str, set] = {}
    for definition in wrappers:
        seen.setdefault(definition.name, set()).add(len(definition.formals))
    for name, lengths in seen.items():
        if name in macros or name in arity:
            continue
        if len(lengths) == 1:
            arity[name] = lengths.pop()
    return raw_arity_scan(sources, set(tree.functions) | set(seen), arity)


# --------------------------------------------------------------------------
# the waiver half
# --------------------------------------------------------------------------

SKIP_CALL = re.compile(r"\b(skipTest|SkipTest|skipIf|skipUnless|self\.skip)\b")
# A defect identifier: a decision, requirement, proof target, obligation or
# scenario the registries know, or an explicit expiry or owner.
IDENTIFIER = re.compile(
    r"\b(D\d{1,3}|REQ-[A-Z]+-\d+|[A-Z]{3}-\d{3}|PRF-\d{3}|OB-[A-Z0-9-]+|"
    r"SCN-[A-Z0-9-]+|expires \d{4}-\d{2}-\d{2}|owner )")
# The declaration a flagged site may carry, in the shape `tools/session_depth.py`
# already uses for its own waivers: a comment on or just above the skip, and a
# waiver with no reason is not a waiver.  It is accepted only when it names a
# registry identifier, an expiry or an owner -- or declares the site a
# capability probe (something the tree has not built yet) or an environment
# probe that has to read a command's output to learn that a dependency is
# absent -- neither of which is a skip over something that is broken.
# Accepted waivers are counted and printed on every run, so they cannot pile
# up unseen, and a declaration that says only "it is broken" is not accepted.
DECLARED = re.compile(r"waiver-ok:\s*(\S.*)")


def _source_segment(lines: list[str], node) -> str:
    start = max(node.lineno - 1, 0)
    end = getattr(node, "end_lineno", node.lineno)
    return "\n".join(lines[start:end])


# What a value has to come from for a skip over it to be a waiver.  An
# environmental predicate asks whether something EXISTS -- `shutil.which`,
# `Path.exists`, `sys.platform`, an import that failed, an environment
# variable.  A waiver asks what a run SAID: its exit status, its stderr, its
# reply.  A probe that shells out and reads the exit status to decide a tool
# is absent belongs on this side of the line too: that conflation is exactly
# what `tests/test_owner.py` got wrong, reporting "openssl is not available"
# for an openssl that was installed and had refused.
FAILURE_SOURCE = re.compile(
    r"\.returncode\b|\.rc\b|\.stderr\b|\.stdout\b|\.output\b|\.first_line\b"
    r"|\bin str\(|\bstr\(\s*\w*(?:error|exc|unavailable|failure|refus)\w*\s*\)"
    r"|\bnot \w+\.ok\b|\bexit_code\b|\bexitcode\b",
    re.IGNORECASE)
RESPONSE_CODE = re.compile(r'["\'][45]\d\d["\']')


def _reads_a_failure(test_source: str) -> str | None:
    """Does this predicate read a failure rather than a dependency?"""
    if FAILURE_SOURCE.search(test_source):
        return "the predicate reads a failure's text or exit status"
    if RESPONSE_CODE.search(test_source):
        return "the predicate reads an NNTP response code"
    return None


def _declaration(lines: list[str], node) -> str:
    """The `waiver-ok:` text on, or in the comment block above, this skip.

    A declaration runs from the `waiver-ok:` marker to the end of the comment
    block it sits in, so the reason can be a paragraph rather than one line.
    """
    start = max(node.lineno - 12, 0)
    end = getattr(node, "end_lineno", node.lineno)
    collected: list[str] = []
    for line in lines[start:end]:
        stripped = line.strip()
        if collected:
            if stripped.startswith("#"):
                collected.append(stripped.lstrip("# ").rstrip())
                continue
            break
        match = DECLARED.search(line)
        if match:
            collected.append(match.group(1).strip())
    return " ".join(collected).strip()


def waiver_findings(root: Path) -> tuple[list[dict], dict]:
    findings: list[dict] = []
    declarations: list[dict] = []
    counts = {"skip_sites": 0, "environmental": 0, "waivers": 0, "declared": 0}
    for tree_name in PYTHON_TREES:
        base = root / tree_name
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.py")):
            relative = path.relative_to(root).as_posix()
            if "/__pycache__/" in relative:
                continue
            text = path.read_text(encoding="utf-8")
            if not SKIP_CALL.search(text):
                continue
            lines = text.splitlines()
            try:
                parsed = ast.parse(text, filename=relative)
            except SyntaxError:
                continue
            for node in ast.walk(parsed):
                if not isinstance(node, ast.Call):
                    continue
                label = _skip_label(node)
                if label is None:
                    continue
                counts["skip_sites"] += 1
                segment = _source_segment(lines, node)
                guard = _enclosing_test(parsed, node, lines)
                reason = (_reads_a_failure(guard) or _reads_a_failure(segment)
                          or _reads_a_failure(_tainted(parsed, node, guard, lines)))
                if reason is None:
                    counts["environmental"] += 1
                    continue
                counts["waivers"] += 1
                declared = _declaration(lines, node)
                if declared and (IDENTIFIER.search(declared)
                                 or declared.lower().startswith(
                                     ("capability", "environment"))):
                    counts.setdefault("declared", 0)
                    counts["declared"] += 1
                    declarations.append({
                        "where": "{}:{}".format(relative, node.lineno),
                        "waiver": declared})
                    continue
                findings.append({
                    "lint": "waivers",
                    "where": "{}:{}".format(relative, node.lineno),
                    "problem": reason + ", and it carries no `waiver-ok:` "
                                        "declaration naming a defect "
                                        "identifier, an expiry, an owner, or "
                                        "a capability this tree has not built",
                    "source": " ".join(segment.split())[:200],
                })
    findings.sort(key=lambda row: row["where"])
    for row in sorted(declarations, key=lambda one: one["where"]):
        print("  waiver-ok {}: {}".format(row["where"], row["waiver"]))
    return findings, counts


def _skip_label(node: ast.Call) -> str | None:
    func = node.func
    names = ("skipTest", "skipUnless", "skipIf", "skip", "SkipTest")
    if isinstance(func, ast.Attribute) and func.attr in names:
        return func.attr
    if isinstance(func, ast.Name) and func.id in names:
        return func.id
    return None


def _tainted(parsed: ast.Module, call: ast.Call, guard: str,
             lines: list[str]) -> str:
    """The assignments the guard's names came from, inside the same function.

    `rc = done.returncode; ...; if rc != 0: skipTest(...)` is the same waiver
    as testing `done.returncode` in the `if` itself.  This follows one hop and
    only within one function body; a value that reached the guard through a
    helper, a JSON file or another process is beyond a static reader, and the
    lint says so rather than pretending otherwise.
    """
    mentioned = set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", guard))
    if not mentioned:
        return ""
    found = []
    for node in ast.walk(parsed):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not any(call is inner for inner in ast.walk(node)):
            continue
        for statement in ast.walk(node):
            if isinstance(statement, ast.Assign):
                names = {target.id for target in statement.targets
                         if isinstance(target, ast.Name)}
                if names & mentioned:
                    found.append(_source_segment(lines, statement.value))
    return "\n".join(found)


def _enclosing_test(parsed: ast.Module, call: ast.Call, lines: list[str]) -> str:
    """The `if` test, or the `except` clause, this skip sits under."""
    best = ""
    for node in ast.walk(parsed):
        if isinstance(node, ast.If):
            body = node.body + node.orelse
            if any(call is inner for item in body for inner in ast.walk(item)):
                best += _source_segment(lines, node.test) + "\n"
        elif isinstance(node, ast.ExceptHandler):
            if any(call is inner for inner in ast.walk(node)):
                best += _source_segment(
                    lines, node.type if node.type else node)[:200] + "\n"
    return best


# --------------------------------------------------------------------------


LINTS = {
    "signatures": (signature_findings, True),
    "acl2-arity": (acl2_findings, True),
    "raw-arity": (raw_arity_findings, True),
    "waivers": (waiver_findings, True),
}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--lint", action="append", default=[],
                        choices=sorted(LINTS),
                        help="run only these (default: all of them)")
    parser.add_argument("--json", default=None)
    parser.add_argument("--report", action="store_true",
                        help="print and always exit 0")
    parser.add_argument("--quiet", action="store_true",
                        help="one summary line per lint, findings only")
    args = parser.parse_args(argv)

    chosen = args.lint or sorted(LINTS)
    report = {"schema": 1, "root": str(ROOT), "lints": {}}
    failed = False
    for name in chosen:
        run, gates = LINTS[name]
        findings, counts = run(ROOT)
        report["lints"][name] = {"findings": findings, "counts": counts,
                                 "gates": gates}
        print("harness_check {}: {} finding{} ({})".format(
            name, len(findings), "" if len(findings) == 1 else "s",
            ", ".join("{} {}".format(value, key) for key, value in counts.items())))
        for finding in findings:
            print("  {} {}: {}".format(
                finding["where"], finding.get("callee", ""), finding["problem"]))
            if finding.get("defined"):
                print("      defined at {}".format(finding["defined"]))
        if findings and gates:
            failed = True
    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 1 if failed and not args.report else 0


if __name__ == "__main__":
    sys.exit(main())
