"""The guard kinds of a host-called entry, read from its source.

books/definterface.lisp refuses a declaration at image build unless its
`:kinds' equal `fn-di-world-kinds': the conjuncts of the entry's translated
guard that are one recognizer of *fn-entry-guard-kinds* (books/payload-
kinds.lisp) applied to one non-stobj formal, as (FORMAL RECOGNIZER) in
formal-position order (fn-di-sort's insertion order for ties).  That check
runs after a certify and an acquire, minutes into a native build.  This
computes the same list from the definition's source with the ledger's
non-evaluating reader, in seconds and with no ACL2, so `interface_emit.py
--kinds' finds a wrong `:kinds' before the image does (lane
online-reclaim-8 lost a build to fn-arx-file-count's missing ((f natp))).

It reads the guard as the source writes it: each `(xargs :guard G)' and each
`(type T V...)' declaration, in declaration order, conjuncts of `and'
flattened.  A `type' contributes the recognizer ACL2 translates it to
(integer, string, symbol, (integer ...) -> integerp; (satisfies P) -> P);
any other type contributes nothing a kind can match.  A guard that reaches a
kind only through a macro other than `and' is not seen; the image's check
remains the authority, and this only finds the disagreement sooner.
"""
from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import ledger  # noqa: E402

KINDS_BOOK = "books/payload-kinds.lisp"
DEFINERS = {"defun", "defund", "defun-inline", "defund-inline"}
WRAPPERS = {"encapsulate", "progn", "local", "with-output", "mutual-recursion",
            "defsection"}
TYPE_RECOGNIZERS = {"integer": "integerp", "string": "stringp", "symbol": "symbolp"}


def entry_guard_kinds(root: Path = ROOT) -> list[str]:
    """The recognizers of *fn-entry-guard-kinds*, from its defconst."""
    source = (root / KINDS_BOOK).read_text(encoding="utf-8")
    for form, _line in ledger.Reader(source).top_level():
        if (ledger.head(form) == "defconst" and len(form) > 2
                and str(form[1]) == "*fn-entry-guard-kinds*"):
            value = form[2]
            if isinstance(value, list) and value and str(value[0]) == "quote":
                value = value[1]
            return [str(pair[0]) for pair in value if isinstance(pair, list) and pair]
    raise ValueError("{}: no defconst *fn-entry-guard-kinds*".format(KINDS_BOOK))


def _collect(forms, into: dict, where: str) -> None:
    for form in forms:
        name = ledger.head(form)
        if name in DEFINERS and len(form) > 2 and isinstance(form[1], ledger.Sym):
            into.setdefault(str(form[1]), (where, form))
        elif name in WRAPPERS:
            _collect(form[1:], into, where)


def definitions(root: Path = ROOT) -> dict[str, tuple[str, list]]:
    """Every defun in books/ and the ACL2-mode host files: name -> (file, form)."""
    found: dict[str, tuple[str, list]] = {}
    for pattern in ("books/*.lisp", "host/*.lisp"):
        for path in sorted(root.glob(pattern)):
            relative = str(path.relative_to(root))
            try:
                forms = [f for f, _ in ledger.Reader(
                    path.read_text(encoding="utf-8", errors="replace")).top_level()]
            except ledger.ReadError:
                continue
            _collect(forms, found, relative)
    return found


def _conjuncts(term) -> list:
    if isinstance(term, list) and term and str(term[0]) == "and":
        out: list = []
        for part in term[1:]:
            out.extend(_conjuncts(part))
        return out
    return [term]


def _type_conjuncts(spec, variables) -> list:
    if isinstance(spec, ledger.Sym) and str(spec) in TYPE_RECOGNIZERS:
        return [[ledger.Sym(TYPE_RECOGNIZERS[str(spec)]), v] for v in variables]
    if isinstance(spec, list) and spec:
        head = str(spec[0])
        if head == "integer":
            return [[ledger.Sym("integerp"), v] for v in variables]
        if head == "satisfies" and len(spec) == 2:
            return [[spec[1], v] for v in variables]
    return []


def guard_conjuncts(form: list) -> tuple[list, set[str]]:
    """The guard's conjuncts in declaration order, and the stobj formals."""
    conjuncts: list = []
    stobjs: set[str] = set()
    for item in form[3:]:
        if ledger.head(item) != "declare":
            continue
        for decl in item[1:]:
            head = ledger.head(decl)
            if head == "xargs":
                for index in range(1, len(decl) - 1, 2):
                    key = str(decl[index])
                    if key == ":guard":
                        conjuncts.extend(_conjuncts(decl[index + 1]))
                    elif key == ":stobjs":
                        value = decl[index + 1]
                        stobjs.update(str(s) for s in (value if isinstance(value, list)
                                                       else [value]))
            elif head == "type" and len(decl) > 2:
                conjuncts.extend(_type_conjuncts(decl[1], decl[2:]))
    return conjuncts, stobjs


def kinds_of(form: list, kinds: list[str]) -> list[list[str]]:
    """fn-di-world-kinds of a defun form: [[formal, recognizer], ...]."""
    formals = [str(f) for f in form[2]] if isinstance(form[2], list) else []
    conjuncts, stobjs = guard_conjuncts(form)
    if "state" in formals:
        stobjs.add("state")
    checks = []
    for c in conjuncts:
        if (isinstance(c, list) and len(c) == 2 and isinstance(c[0], ledger.Sym)
                and isinstance(c[1], ledger.Sym) and str(c[1]) in formals
                and str(c[1]) not in stobjs and str(c[0]) in kinds):
            checks.append((formals.index(str(c[1])), str(c[1]), str(c[0])))
    # fn-di-sort: insert each conjunct, from the last to the first, after
    # every check at a position not greater than its own.
    ordered: list = []
    for check in reversed(checks):
        at = 0
        while at < len(ordered) and not check[0] < ordered[at][0]:
            at += 1
        ordered.insert(at, check)
    return [[formal, recognizer] for _p, formal, recognizer in ordered]


def disagreements(decls: list[dict], defs: dict, kinds: list[str]) -> list[str]:
    """Each declaration whose :kinds is not what its definition's guard gives."""
    out: list[str] = []
    for d in decls:
        found = defs.get(d["name"])
        if found is None:
            continue
        computed = kinds_of(found[1], kinds)
        if computed != d["kinds"]:
            out.append("{}:{}: {} declares :kinds {} but its guard ({}) gives {}".format(
                d["source"], d["line"], d["name"], render(d["kinds"]), found[0],
                render(computed)))
    return out


def render(kinds: list[list[str]]) -> str:
    if not kinds:
        return "NIL"
    return "(" + " ".join("({} {})".format(f, r) for f, r in kinds) + ")"
