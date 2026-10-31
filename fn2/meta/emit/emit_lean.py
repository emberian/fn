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


# ---------------------------------------------------------------- objects and terms

CHAR_NAMES = {"Space": " ", "Newline": "\n", "Tab": "\t", "Page": "\f", "Rubout": "\x7f",
              "Return": "\r", "Linefeed": "\n", "Null": "\x00"}


def die(msg):
    raise SystemExit(f"emit: {msg}")


def ident(name):
    if "«" in name or "»" in name:
        die(f"unrepresentable name {name}")
    return f"«{name}»"


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def val(x):
    """A quoted ACL2 object as a Lean `Val`."""
    if isinstance(x, List):
        items, tail = [], None
        xs = list(x)
        i = 0
        while i < len(xs):
            if isinstance(xs[i], Atom) and xs[i] == "." and i == len(xs) - 2:
                tail = xs[i + 1]
                break
            items.append(xs[i])
            i += 1
        if tail is None:
            return "(Val.ofList [" + ", ".join(val(e) for e in items) + "])"
        out = val(tail)
        for e in reversed(items):
            out = f"(Val.cons {val(e)} {out})"
        return out
    if isinstance(x, Str):
        return f"(Val.str {lean_str(str(x))})"
    a = str(x)
    if a.startswith("#\\"):
        c = a[2:]
        c = CHAR_NAMES.get(c, c)
        if len(c) != 1:
            die(f"character {a}")
        return f"(Val.chr (Char.ofNat {ord(c)}))"
    if re.fullmatch(r"[+-]?\d+", a):
        i = int(a)
        return f"(Val.int {i})" if i >= 0 else f"(Val.int ({i}))"
    if re.fullmatch(r"[+-]?\d+/\d+", a) or a.startswith("#C"):
        die(f"a number outside the subset: {a}")
    if a == "NIL":
        return "Val.nil"
    if a == "T":
        return "Val.t"
    return f"(Val.sym {lean_str(a)})"


def is_lambda(x):
    return isinstance(x, List) and len(x) == 3 and x[0] == "LAMBDA"


# ---------------------------------------------------------------- deep terms (registry data)

def term(t):
    if isinstance(t, List):
        if len(t) == 0:
            return ".quote Val.nil"
        if t[0] == "QUOTE":
            return f"(.quote {val(t[1])})"
        if is_lambda(t[0]):
            formals = [str(v) for v in as_list(t[0][1])]
            return (f"(.lam [{', '.join(lean_str(v) for v in formals)}] {term(t[0][2])} "
                    f"[{', '.join(term(a) for a in t[1:])}])")
        return f"(.app {lean_str(str(t[0]))} [{', '.join(term(a) for a in t[1:])}])"
    a = str(t)
    if re.fullmatch(r"[+-]?\d+", a) or isinstance(t, Str) or a in ("NIL", "T") or a.startswith(":"):
        return f"(.quote {val(t)})"
    return f"(.var {lean_str(a)})"



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


def lean_list(items, indent):
    if not items:
        return "[]"
    pad = " " * indent
    return "[\n" + ",\n".join(pad + "  " + i for i in items) + "\n" + pad + "]"


# ---------------------------------------------------------------- rows

KINDS = {":U8": ".u8", ":U16": ".u16", ":U32": ".u32", ":U60": ".u60", ":U64": ".u64",
         ":BOOL": ".bool", ":LINK": ".link"}
# The protocol's common keys (DSL-METATHEORY 2.2): :decl-id is checked against the row's
# identity; :layer :book :requires are consumed into Common; the three below are event text.
COMMON_CONSUMED = [":DECL-ID", ":LAYER", ":BOOK", ":REQUIRES"]
COMMON_OMITTED = [":GENERATED", ":SIGNATURE", ":REUSE"]
TABLE = {":COLUMNS": ".columns", ":MACHINE": ".machine", ":OPERATION-SET": ".operationSet",
         ":CORE-CHILD": ".coreChild", ":SQUARE": ".square", ":CORRESPONDENCE": ".correspondence",
         ":COMMAND": ".command", ":COST": ".cost", ":SCHEMA": ".schema", ":PORT": ".port",
         ":WAIT": ".wait"}


def col_kind(k, sym):
    if isinstance(k, Atom) and str(k) in KINDS:
        return KINDS[str(k)]
    if isinstance(k, List) and len(k) == 3 and k[0] == ":ENUM":
        tags = ", ".join(sym(t) for t in as_list(k[2]))
        return f"(.enum {sym(k[1])} [{tags}])"
    die(f"unknown column kind {show(k)}")


def columns(cols, sym):
    out = []
    for c in as_list(cols):
        c = as_list(c)
        if len(c) != 2:
            die(f"column spec of length {len(c)}: {show(List(c))}")
        out.append(f"⟨{sym(c[0])}, {col_kind(c[1], sym)}⟩")
    return out


def pairs(xs, sym, second):
    out = []
    for p in as_list(xs):
        p = as_list(p)
        if len(p) != 2:
            die(f"expected a pair, got {show(List(p))}")
        out.append(f"({sym(p[0])}, {second(p[1])})")
    return out


def tagged_term(x, where):
    xs = as_list(x)
    if not (len(xs) == 2 and xs[0] == ":TERM"):
        die(f"{where}: expected (:TERM t), got {show(x)}")
    return term(xs[1])


def common(name, d, sym, table):
    did = as_list(d[":DECL-ID"])
    if not (len(did) == 2 and str(did[0]) == table and str(did[1]) == str(name)):
        die(f"{name}: :decl-id {show(d[':DECL-ID'])} is not ({table} {name})")
    book = d[":BOOK"]
    bs = as_list(book) if isinstance(book, List) else [book]
    btext = str(bs[-1]) if bs else str(book)
    return f"⟨{sym(d[':LAYER'])}, {lean_str(btext)}, {val(d[':REQUIRES'])}⟩"


def row_dict(name, row, consumed, omitted, where):
    d = plist(row, name)
    check_keys(d, consumed + COMMON_CONSUMED, omitted + COMMON_OMITTED, where)
    return d


def struct(fields):
    return "{ " + ",\n    ".join(fields) + " }"


MACHINE_KEYS = [":STATES", ":COLUMNS", ":TABLE", ":HOLDS", ":ADMISSION", ":TAKEN", ":BUDGET",
                ":CONTINUATIONS", ":OBSERVES", ":CAPACITY", ":INITIAL", ":CASES"]
# :layout duplicates :columns; :packed is deleted by DSL-METATHEORY 5.2; :calling-convention is not
# authoritative; the step-language arms are consumed translated, from the embedding (LayerAKinds).
MACHINE_OMITTED = [":LAYOUT", ":PACKED", ":CALLING-CONVENTION", ":ARMS", ":SUBARMS", ":OBSERVE-ARMS",
                   ":STOPS"]


def arm_entries(xs, sym):
    # (TAG FN . CONTRACT): a step-form kind's skeleton has no contract; an older kind's arm table
    # carries its hand contract (:cost :writes :next :uses :language ...) as data
    out = []
    for e in as_list(xs):
        e = as_list(e)
        if len(e) < 2:
            die(f"arm entry {show(List(e))}")
        out.append(f"({sym(e[0])}, {sym(e[1])}, {val(List(e[2:]))})")
    return out


def machine(name, row, sym):
    d = plist(row, name)
    step_form = ":ARMS" in d
    consumed = MACHINE_KEYS + ([":STOPS"] if step_form else [])
    omitted = [k for k in MACHINE_OMITTED if k != ":STOPS"]
    check_keys(d, consumed + COMMON_CONSUMED,
               [k for k in omitted if (k in d)] + ([":CALLBACKS"] if ":CALLBACKS" in d else [])
               + COMMON_OMITTED, f"machine {name}")
    b = plist(d[":BUDGET"], f"{name} budget")
    check_keys(b, [":BYTES", ":STEPS", ":DESCRIPTORS"], [], f"machine {name} budget")

    def init(v):
        xs = as_list(v)
        if len(xs) == 2 and xs[0] == ":FUNCTION":
            return f".function {sym(xs[1])}"
        return f".value {tagged_term(v, f'{name} :initial')}"

    holds = [f"({sym(as_list(h)[0])}, [{', '.join(sym(k) for k in as_list(h)[1:])}])" for h in as_list(d[":HOLDS"])]
    cases = []
    for c in as_list(d[":CASES"]):
        c = as_list(c)
        cases.append(f"({sym(c[0])}, {sym(c[1])}, {sym(c[2])})")
    stops = as_list(d[":STOPS"]) if step_form else []
    fields = [
        f"name := {sym(name)}",
        f"states := [{', '.join(sym(s) for s in as_list(d[':STATES']))}]",
        f"columns := {lean_list(columns(d[':COLUMNS'], sym), 6)}",
        f"table := {lean_list(columns(d[':TABLE'], sym), 6)}",
        f"holds := [{', '.join(holds)}]",
        f"admission := {val(d[':ADMISSION'])}",
        f"taken := {val(d[':TAKEN'])}",
        f"budget := ⟨{b[':BYTES']}, {b[':STEPS']}, {b[':DESCRIPTORS']}⟩",
        f"continuations := {lean_list(arm_entries(d[':CONTINUATIONS'], sym), 6)}",
        f"observes := {lean_list(arm_entries(d[':OBSERVES'], sym), 6)}",
        f"capacity := {tagged_term(d[':CAPACITY'], f'{name} :capacity')}",
        f"initial := {lean_list(pairs(d[':INITIAL'], sym, init), 6)}",
        f"cases := {lean_list(cases, 6)}",
        f"stops := [{', '.join(sym(s) for s in stops)}]",
        f"stepForm := {'true' if step_form else 'false'}",
        f"common := {common(name, d, sym, ':MACHINE')}",
    ]
    return struct(fields), len(as_list(d[":CONTINUATIONS"])), len(as_list(d[":OBSERVES"]))


def columns_decl(name, row, sym):
    # reasons are prose: the model records which fields exist, not why
    # :callbacks is the generated callback map (defmachine-callback's signatures, a manifest of
    # emitted functions like :generated): omitted by name, with the prose reasons
    d = row_dict(name, row, [":COLUMNS", ":ROWS-BOUND", ":EXTRA-FIELDS", ":INIT-NAME", ":PUT-POLICY"],
                 [":COLUMN-REASONS", ":EXTRA-FIELD-REASONS"]
                 + ([":CALLBACKS"] if ":CALLBACKS" in plist(row, name) else []), f"columns {name}")
    fields = [
        f"name := {sym(name)}",
        f"columns := {lean_list(columns(d[':COLUMNS'], sym), 6)}",
        f"rowsBound := {int(str(d[':ROWS-BOUND']))}",
        f"extraFields := {val(d[':EXTRA-FIELDS'])}",
        f"initName := {sym(d[':INIT-NAME'])}",
        f"putPolicy := [{', '.join(sym(s) for s in as_list(d[':PUT-POLICY']))}]",
        f"common := {common(name, d, sym, ':COLUMNS')}",
    ]
    return struct(fields)


REFERENCE = {":STATE": ".state", ":ENVIRONMENT": ".environment"}
ORDER = {":FOUNDATION": ".foundation", ":MACHINE": ".machine", ":EXTENSION": ".extension"}


def child_decl(name, row, sym):
    d = row_dict(name, row, [":STOBJ", ":INIT", ":PROFILEP", ":REFERENCE", ":ORDER", ":WHY"], [],
                 f"core child {name}")
    ref, order = str(d[":REFERENCE"]), str(d[":ORDER"])
    if ref not in REFERENCE or order not in ORDER:
        die(f"core child {name}: reference {ref}, order {order}")
    fields = [
        f"field := {sym(name)}",
        f"stobj := {sym(d[':STOBJ'])}",
        f"init := {tagged_term(d[':INIT'], f'{name} :init')}",
        f"profilep := {tagged_term(d[':PROFILEP'], f'{name} :profilep')}",
        f"reference := {REFERENCE[ref]}",
        f"order := {ORDER[order]}",
        f"why := {lean_str(str(d[':WHY']))}",
        f"common := {common(name, d, sym, ':CORE-CHILD')}",
    ]
    return struct(fields)


SQUARE_DATUM = [(":TEMPLATE", "template"), (":OWNER", "owner"), (":ORIGIN", "origin"), (":CASE", "case"),
                (":CASE-SOURCE", "caseSource"), (":BOUNDARY", "boundary"), (":CONTRACT", "contract"),
                (":SIDES", "sides"), (":SHARED", "shared"), (":CLAIM", "claim"),
                (":SHARED-HANDLER-MUTATION", "sharedHandlerMutation"), (":STATEMENT", "statement"),
                (":TEETH", "teeth"), (":CHECKER", "checker"), (":PROOF", "proof"),
                (":CHECKS", "checks")]


def square_row(name, row, sym):
    # :formula is the untranslated source of :translated (owed.lisp): omitted by name, the term is carried
    d = row_dict(name, row, [k for k, _ in SQUARE_DATUM] + [":SCHEMA", ":VARS", ":DOC", ":TRANSLATED"],
                 [":FORMULA"], f"square {name}")
    fields = [f"name := {sym(name)}", f"schema := {sym(d[':SCHEMA'])}"]
    fields += [f"{f} := {val(d[k])}" for k, f in SQUARE_DATUM]
    fields += [f"vars := [{', '.join(sym(v) for v in as_list(d[':VARS']))}]",
               f"doc := {lean_str(str(d[':DOC']))}",
               f"translated := {tagged_term(d[':TRANSLATED'], f'{name} :translated')}",
               f"common := {common(name, d, sym, ':SQUARE')}"]
    return struct(fields)


def cost_decl(name, row, sym):
    d = row_dict(name, row, [":BYTES", ":STEPS", ":DESCRIPTORS", ":TABLES", ":OWN-WRITES", ":EFFECTS",
                             ":TARGET", ":ANSWERS", ":CHILD", ":DOC", ":PROOF"], [], f"cost {name}")
    child = "none" if is_nil(d[":CHILD"]) else f"(some {sym(d[':CHILD'])})"
    fields = [
        f"fn := {sym(name)}",
        f"bytes := {tagged_term(d[':BYTES'], name)}",
        f"steps := {tagged_term(d[':STEPS'], name)}",
        f"descriptors := {tagged_term(d[':DESCRIPTORS'], name)}",
        f"tables := {val(d[':TABLES'])}", f"ownWrites := {val(d[':OWN-WRITES'])}",
        f"effects := {val(d[':EFFECTS'])}", f"target := {val(d[':TARGET'])}",
        f"answers := {val(d[':ANSWERS'])}", f"child := {child}",
        f"doc := {lean_str(str(d[':DOC']))}", f"proof := {val(d[':PROOF'])}",
        f"common := {common(name, d, sym, ':COST')}",
    ]
    return struct(fields)


def wait_decl(name, row, sym):
    d = row_dict(name, row, [":KIND", ":READY", ":GRANT", ":PARK", ":DOC"], [], f"wait {name}")
    park = "none" if is_nil(d[":PARK"]) else f"(some {sym(d[':PARK'])})"
    fields = [f"name := {sym(name)}", f"kind := {sym(d[':KIND'])}", f"ready := {sym(d[':READY'])}",
              f"grant := {sym(d[':GRANT'])}", f"park := {park}", f"doc := {lean_str(str(d[':DOC']))}",
              f"common := {common(name, d, sym, ':WAIT')}"]
    return struct(fields)


# The tables carried as DeclRow: every key the emitter knows for the table (consumed as data),
# and the keys it omits by name. A key outside both stops the emission.
GENERIC = {
    ":OPERATION-SETS": (".operationSet", ":OPERATION-SET",
                        [":ENUMS", ":CASES", ":DOC", ":ROLE", ":SELECTORS"], [":CALLBACKS"]),
    ":COMMANDS": (".command", ":COMMAND",
                  [":GRAMMAR", ":KEYWORD", ":SYNTAX", ":PROTOCOL-STATES", ":STATE-REFUSAL", ":BLOCK",
                   ":BLOCK-REFUSAL", ":HAND-OFF", ":HELP", ":SPEC", ":REPLIES", ":PORT", ":VERB", ":REQUEST",
                   ":RESULT", ":EFFECT", ":RETRY", ":GRANT", ":METER", ":REASONS", ":CARRIER", ":WIRE",
                   ":BINDS", ":REFUSES", ":LOSES"], []),
    ":PORTS": (".port", ":PORT", [":VERBS", ":FIELDS", ":REASONS", ":OUTCOMES"], []),
    ":SCHEMAS": (".schema", ":SCHEMA", [":ID", ":KEY", ":VALUE", ":MERGE", ":PAGE-KIND", ":LAYOUTS", ":COMPARE", ":FOLD"], []),
    ":CORRESPONDENCES": (".correspondence", ":CORRESPONDENCE", [], []),
    ":LAYOUTS": (".layout", None, [":LAYOUT", ":VALUE-WIDTH", ":PHASE", ":FIELDS", ":MAX-SIZE", ":ENCODE",
                                   ":DECODE", ":DECODE-STEP", ":START", ":SIZE", ":ROUNDTRIP-HYPS"], []),
    ":ARM-CONTRACTS": (".armContract", None, [":CONTINUATIONS", ":OBSERVES", ":UNREACHED"], []),
}


def generic_row(table_key, name, row, sym):
    tbl, decl_kind, known, omitted = GENERIC[table_key]
    d = plist(row, name)
    if decl_kind is not None:
        check_keys(d, [], known + omitted + COMMON_CONSUMED + COMMON_OMITTED, f"{table_key} {name}")
        missing = [k for k in COMMON_CONSUMED if k not in d]
        if missing:
            die(f"{table_key} {name}: missing {missing}")
        common(name, d, sym, decl_kind)
    else:
        check_keys(d, [], known + omitted, f"{table_key} {name}")
    fields = [f"({sym(Atom(k))}, {val(v)})" for k, v in d.items()
              if k not in COMMON_OMITTED and k not in omitted]
    return f"{{ table := {tbl}, name := {sym(name)}, fields := [{', '.join(fields)}] }}"


def table(reg, key):
    for entry in reg[1:]:
        if as_list(entry)[0] == key:
            return [as_list(r) for r in as_list(as_list(entry)[1])]
    die(f"no table {key}")


def main():
    src, out = sys.argv[1], sys.argv[2]
    label = sys.argv[3] if len(sys.argv) > 3 else "unlabelled"
    forms = read_all(open(src).read())
    top = as_list(forms[0])
    if str(top[0]) != ":FN2-WORLD":
        die("expected one (:FN2-WORLD (:REGISTRY ...) (:EMBED ...)) form")
    reg = as_list(top[1])
    sym = Syms()

    def rows(key):
        # each row is (NAME . PLIST): a list whose head is the name
        return [(r[0], List(r[1:])) for r in table(reg, key)]

    known = {":COLUMNS", ":MACHINE-KINDS", ":CORE-CHILDREN", ":SQUARES", ":COSTS", ":WAITS", ":OWED",
             ":CORE-INSTANCE"} | set(GENERIC)
    for entry in reg[1:]:
        k = str(as_list(entry)[0])
        if k not in known:
            die(f"a registry table the emitter does not know: {k}")
    if table(reg, ":OWED"):
        die("fn2-owed has rows again: defthm-owed writes fn2-squares (owed.lisp); model it before emitting")
    ms = [machine(n, r, sym) for n, r in rows(":MACHINE-KINDS")]
    machines = [m[0] for m in ms]
    n_phases = sum(m[1] for m in ms)
    n_events = sum(m[2] for m in ms)
    cols = [columns_decl(n, r, sym) for n, r in rows(":COLUMNS")]
    children = [child_decl(n, r, sym) for n, r in rows(":CORE-CHILDREN")]
    squares = [square_row(n, r, sym) for n, r in rows(":SQUARES")]
    costs = [cost_decl(n, r, sym) for n, r in rows(":COSTS")]
    waits = [wait_decl(n, r, sym) for n, r in rows(":WAITS")]
    generic = []
    counts = {}
    for key in GENERIC:
        rs = [generic_row(key, n, r, sym) for n, r in rows(key)]
        counts[key] = len(rs)
        generic += rs
    for s in ["RUN", "OBSERVE", "READY-PREV", "READY-NEXT", "WAIT-REASON"]:
        sym(Atom(s if s in ("READY-PREV", "READY-NEXT", "WAIT-REASON") else ":" + s))

    L = []
    L.append("-- GENERATED by fn2/meta/emit/emit_lean.py from fn2/meta/emit/world.sexp, which")
    L.append("-- fn2/meta/emit/print-registry.lsp printed from the ACL2 world after including")
    L.append(f"-- fn2/books/reference ({label}). Do not edit: change a declaration or a macro and re-emit.")
    L.append(f"-- Counts: {len(machines)} machines, {len(cols)} columns tables, {len(children)} core children,")
    L.append(f"-- {len(squares)} squares, {len(costs)} costs, {len(waits)} waits, "
             + ", ".join(f"{counts[k]} {k.lower().strip(':')}" for k in GENERIC) + f"; {len(sym.order)} symbols;")
    L.append(f"-- catalogue {n_phases} continuation phases + {n_events} observed events = {n_phases + n_events} machine cases.")
    L.append("import Fn2.Decl")
    L.append("")
    L.append("set_option maxRecDepth 100000")
    L.append("set_option maxHeartbeats 0")
    L.append("")
    L.append("namespace Fn2.Instances.LayerA")
    L.append("open Fn2.Decl Fn2.ACL2")
    L.append("")
    L.append("/-- Every symbol the registry names, as a finite type (the registry's alphabet). -/")
    L.append("inductive Sym where")
    for a in sym.order:
        L.append(f"  | {sym.lean[a]}")
    L.append("  deriving DecidableEq")

    L.append("")
    L.append("/-- The ACL2 spelling of each symbol, as the world printed it. -/")
    L.append("def Sym.acl2 : Sym → String")
    for a in sym.order:
        L.append(f"  | .{sym.lean[a]} => {lean_str(a)}")
    L.append("")
    L.append("instance : Repr Sym := ⟨fun s _ => Std.Format.text s.acl2⟩")
    L.append("")
    L.append(f"def source : String := {lean_str(label)}")
    L.append("")
    for (nm, ty, items, doc) in [("machines", "MachineDecl", machines, "fn2-machine-kinds"),
                                 ("columnsTables", "ColumnsDecl", cols, "fn2-columns"),
                                 ("coreChildren", "CoreChildDecl", children, "fn2-core-children"),
                                 ("squares", "SquareRow", squares, "fn2-squares"),
                                 ("costs", "CostDecl", costs, "fn2-costs"),
                                 ("waits", "WaitDecl", waits, "fn2-waits"),
                                 ("otherRows", "DeclRow", generic, "the other tables, as data")]:
        L.append(f"/-- `{doc}`, in declaration order. -/")
        L.append(f"def {nm} : List ({ty} Sym) := " + lean_list(items, 0))
        L.append("")
    L.append("/-- The registry as one Lean term. -/")
    L.append("def registry : Registry Sym where")
    L.append("  machines := machines")
    L.append("  columns := columnsTables")
    L.append("  coreChildren := coreChildren")
    L.append("  squares := squares")
    L.append("  costs := costs")
    L.append("  waits := waits")
    L.append("  rows := otherRows")
    L.append("")
    L.append("end Fn2.Instances.LayerA")
    L.append("")
    open(out, "w").write("\n".join(L))
    print(f"EMIT machines={len(machines)} columns={len(cols)} children={len(children)} squares={len(squares)} "
          f"costs={len(costs)} waits={len(waits)} "
          + " ".join(f"{k.lower().strip(':')}={counts[k]}" for k in GENERIC)
          + f" symbols={len(sym.order)} machine-cases={n_phases + n_events} -> {out}")


if __name__ == "__main__":
    main()
