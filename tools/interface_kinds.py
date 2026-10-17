#!/usr/bin/env python3
"""What the image build will say about each declaration's :class and :kinds,
computed from the source (obstructions-8 item 68).

books/definterface.lisp checks each `(definterface NAME :class C :kinds K)`
against the image's world when host/native/build.lisp loads
host/interfaces.lisp: C must be NAME's symbol-class and K exactly the host
entry guard's kind checks (fn-di-world-kinds).  A wrong declaration stopped
image builds after a 25-minute wait (online-reclaim-8/9: "the image build
stops on a missing :kinds").  This reads the same source with the ledger's
non-evaluating reader and says it first -- `interface_emit --check` runs it.

THE KINDS, as fn-di-world-kinds takes them: the guard's conjuncts (the type
declarations' translations and each :guard, in declaration order; `and' and
`(if A B nil)' flattened), each `(RECOGNIZER FORMAL)' whose recognizer is a
key of *fn-entry-guard-kinds* (books/payload-kinds.lisp) and whose formal is
not a stobj, as (FORMAL RECOGNIZER) sorted by the formal's position -- ties
in REVERSE conjunct order, as fn-di-sort's insertion leaves them.

THE CLASS: :program for `:mode :program' or a `(program)' default earlier
in its file; :common-lisp-compliant when the
guards are verified (`:verify-guards t', or a guard / type declaration /
:stobjs / :guard-hints under the default eagerness, or eagerness 2 in the
file, or a `(verify-guards NAME)' or `(def-carried-writer NAME ...)' event
(the generator verifies an :ideal writer's guards) -- for any function of NAME's
mutual-recursion clique; eagerness 0 in the file verifies only those
two); :ideal otherwise.

It is an ESTIMATE, and says when it cannot judge: a guard conjunct whose head
is a macro defined in the tree, a type it does not translate, a
`verify-termination', or a definition it does not find is skipped, never
guessed.  ACL2 at image build stays the judge.

    python3 tools/interface_kinds.py          # every disagreement, and the skipped count
    python3 tools/interface_kinds.py NAME...  # what it computes for NAME
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

KINDS_BOOK = "books/payload-kinds.lisp"
KINDS_CONST = "*fn-entry-guard-kinds*"
DEFUN_HEADS = ("defun", "defund", "defun-nx", "defun-inline", "defund-inline")
NESTING = ("progn", "encapsulate", "local", "with-output", "defsection", "mutual-recursion")
# translate-declaration-to-guard's recognizer for a type symbol
TYPE_SYMBOLS = {"integer": "integerp", "string": "stringp", "symbol": "symbolp",
                "character": "characterp", "rational": "rationalp", "cons": "consp",
                "atom": "atom", "null": "null", "number": "acl2-numberp",
                "keyword": "keywordp"}
# compound types whose translation's first conjunct is (integerp X)
INTEGER_TYPES = ("integer", "unsigned-byte", "signed-byte", "mod")


def _s(x) -> str:
    return str(x).lower()


@dataclass
class Definition:
    name: str
    where: str
    form: list
    eagerness: int = 1             # the file's set-verify-guards-eagerness before it
    program: bool = False          # the file's default defun-mode is :program ((program))
    clique: tuple = ()             # its mutual-recursion clique (names), else ()


@dataclass
class Source:
    definitions: dict = field(default_factory=dict)
    verified: set = field(default_factory=set)       # names a verify-guards event names
    terminated: set = field(default_factory=set)     # names a verify-termination names
    macros: set = field(default_factory=set)
    kinds: tuple = ()


def read_source(files: list[tuple[str, str]]) -> Source:
    """FILES: (relative path, text).  Every definition, guard event and macro."""
    out = Source()
    for relative, text in files:
        eagerness = [1]
        program = [False]

        def visit(form, line, clique=()):
            name = ledger.head(form)
            expansion = ledger.generated_expansion(form)
            if expansion is not None:
                for item in expansion:
                    visit(item, line, clique)
                return
            if name == "mutual-recursion":
                names = tuple(_s(f[1]) for f in form[1:]
                              if isinstance(f, list) and len(f) > 1)
                for item in form[1:]:
                    visit(item, line, names)
                return
            if name in NESTING:
                for item in form[1:]:
                    visit(item, line, clique)
                return
            if name in ("program", "logic") and len(form) == 1:
                program[0] = name == "program"
            elif (name == "set-default-defun-mode" and len(form) > 1
                    and _s(form[1]) in (":program", ":logic")):
                program[0] = _s(form[1]) == ":program"
            elif (name == "set-verify-guards-eagerness" and len(form) > 1
                    and _s(form[1]) in ("0", "1", "2")):
                eagerness[0] = int(_s(form[1]))
            elif name in DEFUN_HEADS and len(form) >= 4 and isinstance(form[1], ledger.Sym):
                fn = _s(form[1])
                out.definitions.setdefault(fn, Definition(
                    fn, "{}:{}".format(relative, line), form, eagerness[0], program[0], clique))
            elif name == "verify-guards" and len(form) > 1:
                out.verified.add(_s(form[1]))
            elif name == "def-carried-writer" and len(form) > 1:
                # books/def-carried-writer.lisp issues (verify-guards FN) for
                # an :ideal FN in its scoped theory, and refuses the row
                # if that fails: the writer is :common-lisp-compliant after it.
                out.verified.add(_s(form[1]))
            elif name == "verify-termination" and len(form) > 1:
                out.terminated.add(_s(form[1]))
            elif name == "defmacro" and len(form) > 1:
                out.macros.add(_s(form[1]))
            elif name == "defconst" and len(form) > 2 and _s(form[1]) == KINDS_CONST:
                value = form[2]
                if isinstance(value, list) and value and _s(value[0]) == "quote":
                    value = value[1]
                out.kinds = tuple(_s(pair[0]) for pair in value
                                  if isinstance(pair, list) and pair)

        for form, line in ledger.Reader(text).top_level():
            visit(form, line)
    return out


def tree_files() -> list[tuple[str, str]]:
    """books/*.lisp and the ACL2-mode host files (the raw host is not ACL2)."""
    files = [(p.relative_to(ROOT).as_posix(), p.read_text(encoding="utf-8"))
             for p in sorted((ROOT / "books").glob("*.lisp"))]
    tree = ledger.load_tree()
    raw = ledger.raw_host_paths(tree)
    for relative in sorted(tree.hosts):
        if relative not in raw:
            files.append((relative, (ROOT / relative).read_text(encoding="utf-8")))
    return files


class CannotJudge(Exception):
    """The source alone does not decide it."""


def _declarations(form: list) -> list:
    """Each (KIND, VALUE) of FORM's declares, in order: ("type", (TYPE VARS...)),
    or ("xargs", (KEY, VALUE))."""
    out = []
    for item in form[3:-1]:
        if isinstance(item, list) and item and _s(item[0]) == "declare":
            for decl in item[1:]:
                if not isinstance(decl, list) or not decl:
                    continue
                if _s(decl[0]) == "xargs":
                    rest = decl[1:]
                    out.extend(("xargs", (_s(k), v)) for k, v in zip(rest[::2], rest[1::2]))
                elif _s(decl[0]) == "type" and len(decl) > 2:
                    out.append(("type", decl[1:]))
    return out


def _type_conjuncts(kind, var) -> list:
    if isinstance(kind, list) and kind:
        head = _s(kind[0])
        if head in INTEGER_TYPES:
            return [["integerp", var], ["range", var]]
        if head == "satisfies" and len(kind) == 2:
            return [[_s(kind[1]), var]]
        if head == "and":
            return [c for k in kind[1:] for c in _type_conjuncts(k, var)]
        if head in ("or", "member", "eql", "rational", "real", "complex"):
            return [["type", var]]
        raise CannotJudge(f"type {kind}")
    name = _s(kind)
    if name in TYPE_SYMBOLS:
        return [[TYPE_SYMBOLS[name], var]]
    if name in ("t",):
        return []
    raise CannotJudge(f"type {name}")


def _is_nil(x) -> bool:
    if isinstance(x, list):
        return len(x) == 2 and _s(x[0]) == "quote" and _s(x[1]) == "nil"
    return _s(x) == "nil"


def conjuncts(term, macros: set[str]) -> list:
    if isinstance(term, list) and term:
        head = _s(term[0])
        if head == "and":
            return [c for t in term[1:] for c in conjuncts(t, macros)]
        if head == "if" and len(term) == 4 and _is_nil(term[3]):
            return conjuncts(term[1], macros) + conjuncts(term[2], macros)
        if head in macros:
            raise CannotJudge(f"guard macro {head}")
        return [term]
    return [term]


def guard_conjuncts(definition: Definition, macros: set[str]) -> list:
    out = []
    for kind, value in _declarations(definition.form):
        if kind == "type":
            for var in value[1:]:
                out.extend(_type_conjuncts(value[0], var))
        elif value[0] == ":guard":
            out.extend(conjuncts(value[1], macros))
    return out


def stobj_formals(definition: Definition) -> set[str]:
    formals = [_s(f) for f in definition.form[2]] if isinstance(definition.form[2], list) else []
    stobjs = {f for f in formals if f == "state"}
    for kind, value in _declarations(definition.form):
        if kind == "xargs" and value[0] == ":stobjs":
            v = value[1]
            stobjs |= {_s(x) for x in v} if isinstance(v, list) else {_s(v)}
    return stobjs


def kinds(definition: Definition, source: Source) -> list[list[str]]:
    """[[FORMAL, RECOGNIZER], ...] as fn-di-world-kinds gives them."""
    formals = [_s(f) for f in definition.form[2]] if isinstance(definition.form[2], list) else []
    stobjs = stobj_formals(definition)
    checks = []
    for c in guard_conjuncts(definition, source.macros):
        if (isinstance(c, list) and len(c) == 2 and not isinstance(c[0], list)
                and not isinstance(c[1], list) and _s(c[0]) in source.kinds
                and _s(c[1]) in formals and _s(c[1]) not in stobjs):
            checks.append((formals.index(_s(c[1])), _s(c[1]), _s(c[0])))
    ordered = sorted(reversed(checks), key=lambda check: check[0])
    return [[formal, recognizer] for _, formal, recognizer in ordered]


def symbol_class(definition: Definition, source: Source) -> str:
    if definition.name in source.terminated:
        raise CannotJudge("verify-termination")
    xargs = dict(value for kind, value in _declarations(definition.form) if kind == "xargs")
    mode = _s(xargs.get(":mode", ":program" if definition.program else ":logic"))
    if mode == ":program":
        return "program"
    verified_event = any(n in source.verified for n in (definition.name, *definition.clique))
    setting = _s(xargs.get(":verify-guards", "")) if ":verify-guards" in xargs else None
    if setting == "t" or verified_event:
        return "common-lisp-compliant"
    if setting == "nil":
        return "ideal"
    guarded = (any(kind == "type" for kind, _ in _declarations(definition.form))
               or any(k in xargs for k in (":guard", ":stobjs", ":guard-hints")))
    if definition.eagerness == 2 or (definition.eagerness == 1 and guarded):
        return "common-lisp-compliant"
    return "ideal"


def judge(decls: list[dict], source: Source) -> tuple[list[str], int]:
    """(each disagreement as the image build would word it, the number skipped)."""
    out: list[str] = []
    skipped = 0
    for d in decls:
        definition = source.definitions.get(d["name"])
        if definition is None:
            skipped += 1
            continue
        where = "{}:{}".format(d["source"], d["line"])
        try:
            klass = symbol_class(definition, source)
            if d["class"] != klass:
                out.append("{}: {} is :{} (by its source, {}), declared :{}".format(
                    where, d["name"], klass, definition.where, d["class"]))
                continue
            computed = kinds(definition, source)
        except CannotJudge:
            skipped += 1
            continue
        if computed != d["kinds"]:
            out.append("{}: {}'s guard kinds are {} (the host entry guard's, by its source "
                       "{}), declared {}".format(where, d["name"], _spell(computed),
                                                 definition.where, _spell(d["kinds"])))
    return out, skipped


def _spell(pairs: list) -> str:
    return "(" + " ".join("({} {})".format(f, r) for f, r in pairs) + ")" if pairs else "NIL"


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("names", nargs="*")
    args = parser.parse_args(argv)
    source = read_source(tree_files())
    if args.names:
        for name in args.names:
            definition = source.definitions.get(name.lower())
            if definition is None:
                print(f"{name}: no definition found")
                continue
            try:
                print(f"(definterface {definition.name} :class :{symbol_class(definition, source)}"
                      f" :kinds {_spell(kinds(definition, source))})  ; {definition.where}")
            except CannotJudge as why:
                print(f"{name}: cannot judge from the source ({why})")
        return 0
    from tools import interface_emit
    problems, skipped = judge(interface_emit.declarations(), source)
    print(f"interface_kinds: {len(problems)} disagreement(s); {skipped} declaration(s) not judged")
    for problem in problems:
        print("  " + problem)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
