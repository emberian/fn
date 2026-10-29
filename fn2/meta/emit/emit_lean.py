#!/usr/bin/env python3
"""Emit fn2/meta/Fn2/Instances/LayerA.lean from the registry ACL2 printed.

Input: the S-expression `print-registry.lsp` writes (the world tables
fn2-machine-kinds, fn2-columns, fn2-core-children and fn2-owed, in
declaration order). Output: Lean terms of the structures in Fn2/Decl.lean.

The emitter is a function of the registry and nothing else. Two rules keep it
honest (LEAN-METATHEORY.md section 4):
  * every key of every row is either consumed or named in OMITTED; an unknown
    key stops the emission, so a macro that starts recording something new is
    noticed rather than silently dropped;
  * an ACL2 term (a formula, an initialiser, a capacity) is emitted as its
    printed text in `Opaque`, never as an interpreted Lean term.

The eight Q1 labels the registry does not hold today (the router fallback and
the executor's seven) are NOT emitted here: they are a hand-declared case
source in Fn2/Instances/LayerAFacts.lean, flagged there, until the executor
registers its case source in the world (DSL-METATHEORY section 3.2).

Usage: emit_lean.py REGISTRY.sexp OUT.lean [SOURCE-LABEL]
"""
import re
import sys

# ---------------------------------------------------------------- reader

TOKEN = re.compile(r"""\s*(?:(;[^\n]*)|(\()|(\))|(')|("(?:[^"\\]|\\.)*")|(#\\\S)|([^\s()'"]+))""", re.S)


def read_all(text):
    toks = []
    pos = 0
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m or m.end() == pos:
            if text[pos:].strip() == "":
                break
            raise SystemExit(f"emit: unreadable input at offset {pos}: {text[pos:pos+40]!r}")
        pos = m.end()
        if m.group(1) is None and m.end() > m.start() and any(m.groups()[1:]):
            toks.append(m)
    i = 0

    def form():
        nonlocal i
        if i >= len(toks):
            raise SystemExit("emit: unexpected end of input")
        m = toks[i]
        i += 1
        _, lp, rp, q, s, ch, atom = m.groups()
        if lp:
            out = []
            while True:
                if i >= len(toks):
                    raise SystemExit("emit: unbalanced input")
                if toks[i].group(3):
                    i += 1
                    return List(out)
                out.append(form())
        if rp:
            raise SystemExit("emit: unexpected )")
        if q:
            return List([Atom("QUOTE"), form()])
        if s:
            return Str(s[1:-1].replace('\\"', '"').replace("\\\\", "\\"))
        if ch:
            return Atom(ch)
        return Atom(atom)

    forms = []
    while i < len(toks):
        forms.append(form())
    return forms


class Atom(str):
    pass


class Str(str):
    pass


class List(list):
    pass


def show(x):
    """The ACL2 printed text of a term, as ACL2 printed it."""
    if isinstance(x, List):
        if len(x) == 2 and x[0] == "QUOTE":
            return "'" + show(x[1])
        return "(" + " ".join(show(e) for e in x) + ")"
    if isinstance(x, Str):
        return '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'
    return str(x)


def is_nil(x):
    return isinstance(x, Atom) and x == "NIL"


def as_list(x):
    if is_nil(x):
        return []
    if not isinstance(x, List):
        raise SystemExit(f"emit: expected a list, got {show(x)}")
    return list(x)


def plist(row, name):
    xs = as_list(row)
    if len(xs) % 2:
        raise SystemExit(f"emit: odd plist in {name}")
    out = {}
    for k, v in zip(xs[::2], xs[1::2]):
        if not (isinstance(k, Atom) and k.startswith(":")):
            raise SystemExit(f"emit: non-keyword key {show(k)} in {name}")
        out[k] = v
    return out


def check_keys(d, consumed, omitted, where):
    unknown = set(d) - set(consumed) - set(omitted)
    missing = set(consumed) - set(d)
    if unknown or missing:
        raise SystemExit(f"emit: {where}: unknown keys {sorted(unknown)}, missing keys {sorted(missing)}")


# ---------------------------------------------------------------- symbols

class Syms:
    def __init__(self):
        self.order = []
        self.lean = {}
        self.used = set()

    def __call__(self, atom):
        if not isinstance(atom, Atom) or is_nil(atom) or atom.startswith("#"):
            raise SystemExit(f"emit: expected a symbol, got {show(atom)}")
        a = str(atom)
        if a not in self.lean:
            kw = a.startswith(":")
            base = ("k_" if kw else "s_") + re.sub(r"[^a-z0-9]", "_", a.lstrip(":").lower())
            name, n = base, 1
            while name in self.used:
                n += 1
                name = f"{base}_{n}"
            self.used.add(name)
            self.lean[a] = name
            self.order.append(a)
        return "." + self.lean[a]


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def opaque(x):
    return "⟨" + lean_str(show(x)) + "⟩"


def lean_list(items, indent):
    if not items:
        return "[]"
    pad = " " * indent
    return "[\n" + ",\n".join(pad + "  " + i for i in items) + "\n" + pad + "]"


# ---------------------------------------------------------------- rows

KINDS = {":U8": ".u8", ":U16": ".u16", ":U32": ".u32", ":U60": ".u60", ":U64": ".u64", ":BOOL": ".bool"}


def col_kind(k, sym):
    if isinstance(k, Atom) and str(k) in KINDS:
        return KINDS[str(k)]
    if isinstance(k, List) and len(k) == 3 and k[0] == ":ENUM":
        tags = ", ".join(sym(t) for t in as_list(k[2]))
        return f"(.enum {sym(k[1])} [{tags}])"
    raise SystemExit(f"emit: unknown column kind {show(k)}")


def columns(cols, sym):
    out = []
    for c in as_list(cols):
        c = as_list(c)
        if len(c) != 2:
            raise SystemExit(f"emit: column spec of length {len(c)}: {show(List(c))}")
        out.append(f"⟨{sym(c[0])}, {col_kind(c[1], sym)}⟩")
    return out


def pairs(xs, sym, second):
    out = []
    for p in as_list(xs):
        p = as_list(p)
        if len(p) != 2:
            raise SystemExit(f"emit: expected a pair, got {show(List(p))}")
        out.append(f"({sym(p[0])}, {second(p[1])})")
    return out


MACHINE_KEYS = [":STATES", ":COLUMNS", ":ACCOUNTS", ":BUDGET", ":CONTINUATIONS", ":OBSERVES", ":CAPACITY", ":INITIAL"]
# Recorded by defmachine but not part of the model: :layout duplicates :columns;
# :packed and :obligations are deleted by DSL-METATHEORY 5.2; :calling-convention is
# not authoritative until R5e (DSL-METATHEORY 1.2, A1).
MACHINE_OMITTED = [":LAYOUT", ":PACKED", ":CALLING-CONVENTION", ":OBLIGATIONS"]
COLUMNS_KEYS = [":COLUMNS", ":ROWS-BOUND", ":EXTRA-FIELDS", ":INIT-NAME"]
# Reasons are prose; the model records which fields exist, not why.
COLUMNS_OMITTED = [":COLUMN-REASONS", ":EXTRA-FIELD-REASONS"]
CHILD_KEYS = [":STOBJ", ":INIT", ":PROFILEP", ":REFERENCE", ":ORDER", ":WHY"]
OWED_KEYS = [":VARS", ":FORMULA", ":TEETH", ":DOC", ":STATUS"]

REFERENCE = {":STATE": ".state", ":ENVIRONMENT": ".environment"}
ORDER = {":FOUNDATION": ".foundation", ":MACHINE": ".machine", ":EXTENSION": ".extension"}


def machine(name, row, sym):
    d = plist(row, name)
    check_keys(d, MACHINE_KEYS, MACHINE_OMITTED, f"machine {name}")
    b = plist(d[":BUDGET"], f"{name} budget")
    check_keys(b, [":BYTES", ":STEPS", ":DESCRIPTORS"], [], f"machine {name} budget")
    fields = [
        f"name := {sym(name)}",
        f"states := [{', '.join(sym(s) for s in as_list(d[':STATES']))}]",
        f"columns := {lean_list(columns(d[':COLUMNS'], sym), 6)}",
        f"accounts := [{', '.join(sym(s) for s in as_list(d[':ACCOUNTS']))}]",
        f"budget := ⟨{b[':BYTES']}, {b[':STEPS']}, {b[':DESCRIPTORS']}⟩",
        f"continuations := {lean_list(pairs(d[':CONTINUATIONS'], sym, sym), 6)}",
        f"observes := {lean_list(pairs(d[':OBSERVES'], sym, sym), 6)}",
        f"capacity := {opaque(d[':CAPACITY'])}",
        f"initial := {lean_list(pairs(d[':INITIAL'], sym, opaque), 6)}",
    ]
    return "{ " + ",\n    ".join(fields) + " }"


def columns_decl(name, row, sym):
    d = plist(row, name)
    check_keys(d, COLUMNS_KEYS, COLUMNS_OMITTED, f"columns {name}")
    extras = [sym(as_list(e)[0]) for e in as_list(d[":EXTRA-FIELDS"])]
    fields = [
        f"name := {sym(name)}",
        f"columns := {lean_list(columns(d[':COLUMNS'], sym), 6)}",
        f"rowsBound := {opaque(d[':ROWS-BOUND'])}",
        f"extraFields := [{', '.join(extras)}]",
        f"initName := {sym(d[':INIT-NAME'])}",
    ]
    return "{ " + ",\n    ".join(fields) + " }", len(as_list(d[":COLUMNS"])), len(extras)


def child_decl(name, row, sym):
    d = plist(row, name)
    check_keys(d, CHILD_KEYS, [], f"core child {name}")
    ref, order = str(d[":REFERENCE"]), str(d[":ORDER"])
    if ref not in REFERENCE or order not in ORDER:
        raise SystemExit(f"emit: core child {name}: reference {ref}, order {order}")
    fields = [
        f"field := {sym(name)}",
        f"stobj := {sym(d[':STOBJ'])}",
        f"init := {opaque(d[':INIT'])}",
        f"profilep := {opaque(d[':PROFILEP'])}",
        f"reference := {REFERENCE[ref]}",
        f"order := {ORDER[order]}",
        f"why := {lean_str(str(d[':WHY']))}",
    ]
    return "{ " + ",\n    ".join(fields) + " }"


def owed_decl(name, row, sym):
    d = plist(row, name)
    check_keys(d, OWED_KEYS, [], f"owed {name}")
    fields = [
        f"name := {sym(name)}",
        f"vars := [{', '.join(sym(v) for v in as_list(d[':VARS']))}]",
        f"formula := {opaque(d[':FORMULA'])}",
        f"teeth := [{', '.join(sym(t) for t in as_list(d[':TEETH']))}]",
        f"doc := {lean_str(str(d[':DOC']))}",
        f"status := {sym(d[':STATUS'])}",
    ]
    return "{ " + ",\n    ".join(fields) + " }"


def table(reg, key):
    for entry in reg[1:]:
        if as_list(entry)[0] == key:
            return [as_list(r) for r in as_list(as_list(entry)[1])]
    raise SystemExit(f"emit: no table {key}")


def main():
    src, out = sys.argv[1], sys.argv[2]
    label = sys.argv[3] if len(sys.argv) > 3 else "unlabelled"
    forms = read_all(open(src).read())
    if len(forms) != 1 or as_list(forms[0])[0] != ":FN2-REGISTRY":
        raise SystemExit("emit: expected one (:FN2-REGISTRY ...) form")
    reg = as_list(forms[0])
    sym = Syms()

    def rows(key):
        # each row is (NAME . PLIST): a list whose head is the name
        return [(r[0], List(r[1:])) for r in table(reg, key)]

    machines = [machine(n, r, sym) for n, r in rows(":MACHINE-KINDS")]
    cols = [columns_decl(n, r, sym) for n, r in rows(":COLUMNS")]
    children = [child_decl(n, r, sym) for n, r in rows(":CORE-CHILDREN")]
    owed = [owed_decl(n, r, sym) for n, r in rows(":OWED")]
    machine_rows = rows(":MACHINE-KINDS")
    n_phases = sum(len(as_list(plist(r, n)[":CONTINUATIONS"])) for n, r in machine_rows)
    n_events = sum(len(as_list(plist(r, n)[":OBSERVES"])) for n, r in machine_rows)

    L = []
    L.append("-- GENERATED by fn2/meta/emit/emit_lean.py from fn2/meta/emit/registry.sexp,")
    L.append("-- which fn2/meta/emit/print-registry.lsp printed from the ACL2 world after including")
    L.append(f"-- fn2/books/reference ({label}). Do not edit: change a declaration or a macro and re-emit.")
    L.append(f"-- Counts: {len(machines)} machines, {len(cols)} columns tables, {len(children)} core children,")
    L.append(f"-- {len(owed)} owed rows, {len(sym.order)} symbols; catalogue {n_phases} continuation phases")
    L.append(f"-- + {n_events} observed events = {n_phases + n_events} machine-owned Q1 cases.")
    L.append("import Fn2.Decl")
    L.append("")
    L.append("namespace Fn2.Instances.LayerA")
    L.append("open Fn2.Decl")
    L.append("")
    L.append("/-- Every symbol the registry names, as a finite type (the registry's alphabet). -/")
    L.append("inductive Sym where")
    for a in sym.order:
        L.append(f"  | {sym.lean[a]}")
    L.append("  deriving DecidableEq, Repr")
    L.append("")
    L.append("/-- The ACL2 spelling of each symbol, as the world printed it. -/")
    L.append("def Sym.acl2 : Sym → String")
    for a in sym.order:
        L.append(f"  | .{sym.lean[a]} => {lean_str(a)}")
    L.append("")
    L.append(f"def source : String := {lean_str(label)}")
    L.append("")
    L.append("/-- `fn2-machine-kinds`, in declaration order. -/")
    L.append("def machines : List (MachineDecl Sym) := " + lean_list(machines, 0))
    L.append("")
    L.append("/-- `fn2-columns`, in declaration order. -/")
    L.append("def columnsTables : List (ColumnsDecl Sym) := " + lean_list([c[0] for c in cols], 0))
    L.append("")
    L.append("/-- `fn2-core-children`, in declaration order. -/")
    L.append("def coreChildren : List (CoreChildDecl Sym) := " + lean_list(children, 0))
    L.append("")
    L.append("/-- `fn2-owed`, in declaration order. -/")
    L.append("def owed : List (OwedDecl Sym) := " + lean_list(owed, 0))
    L.append("")
    L.append("/-- The registry as one Lean term. -/")
    L.append("def registry : Registry Sym where")
    L.append("  machines := machines")
    L.append("  columns := columnsTables")
    L.append("  coreChildren := coreChildren")
    L.append("  owed := owed")
    L.append("")
    L.append("end Fn2.Instances.LayerA")
    L.append("")
    open(out, "w").write("\n".join(L))
    print(f"EMIT machines={len(machines)} columns={len(cols)} children={len(children)} owed={len(owed)} "
          f"symbols={len(sym.order)} phases={n_phases} events={n_events} machine-cases={n_phases + n_events} "
          f"declarations={len(machines) + len(cols) + len(children) + len(owed)} -> {out}")


if __name__ == "__main__":
    main()
