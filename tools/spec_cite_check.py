#!/usr/bin/env python3
"""Every Lisp name a specification or document cites is one the tree defines.

PKT-312: specs/bp-node-machine.md named the retired `fn-bpn-limits-compose`
four times, a theorem whose statement is false at the new widths, and no tool
noticed: `tools/ledger.py` checks the registry's theorem names and
`tools/cite_check.py` checks repository paths, while a spec's prose cites
theorems by name.  This tool reads every backquoted span of `specs/*.md` and
`docs/*.md` that is exactly one `fn...-...` symbol and asks whether any book,
test book or host file defines it (tools/ledger.py's tree: defun, defthm,
defconst, defmacro, defstobj, encapsulate signatures, and the host files'
definitions).  Case is ignored, as ACL2's reader ignores it.

Not checked, by visible rule (each counted in the summary):
  * template: the span holds `*`, `<` or `>` (`fn-bpn-*`, `fn-<rec>-shapep`);
  * short: one segment after the prefix (`fn-bpn`, `fn-host`, `fn-e`,
    `fnn-sha256`): prefixes (docs/prefixes.md), magics, record kinds, programs
    and images, which prose names without their being Lisp definitions;
  * tag: a `-vN` suffix (`fn-hybrid-v1`, `fn-peering-v1`): a versioned
    domain-separation tag or format name, octets rather than a name.
Resolved besides a definition (PKT-446): a record's own name
(`(fn-defrecord fn-node-state ...)`), and a slash abbreviation
(`fnn-metadata-config-frame/-decode`) whose every expansion is defined.
Literal backquoted defstobj, defun and defthm names in a macro also resolve
when a book invokes that macro at the start of a line -- the same book, or
any other (a generator macro defined in one book and invoked in another).
Names concatenated from a definer's first argument also resolve when its
source helpers emit them in definition positions. Unsupported name
expressions and unknown conditions remain unresolved.
Named exemptions (tools/spec_cite_exemptions.json `exemptions`) are names a
person judged are not definitions, each with a reason.  The `stale` section
names, per packet, the citations known to be stale and not yet repaired,
each with the files that still cite it: they are reported and counted, never
silent, and `--strict` fails on any citation that is neither defined nor
listed, and on any listed entry that no longer occurs (so the list only
shrinks as the repairs land).

    python3 tools/spec_cite_check.py --summary --strict     # make check
    python3 tools/spec_cite_check.py --list                 # every unresolved citation
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
EXEMPTIONS = ROOT / "tools" / "spec_cite_exemptions.json"
SPAN = re.compile(r"`([^`\n]+)`")
SYMBOL = re.compile(r"fn[a-z0-9]*-[a-z0-9\-*+?!<>=/%.]*[a-z0-9*+?!<>=%]", re.I)
TAG = re.compile(r".*-v[0-9]+")


@dataclass
class Result:
    checked: int = 0
    resolved: int = 0
    ruled: dict = field(default_factory=lambda: {"template": 0, "short": 0, "tag": 0})
    exempted: dict = field(default_factory=dict)       # name -> count
    stale: dict = field(default_factory=dict)          # name -> [file:line]
    unlisted: dict = field(default_factory=dict)       # name -> [file:line]
    unused: list = field(default_factory=list)         # listed entries no longer cited

    @property
    def ok(self) -> bool:
        return not self.unlisted and not self.unused


def rule_for(name: str) -> str | None:
    if any(ch in name for ch in "*<>"):
        return "template"
    if name.count("-") == 1:
        return "short"
    if TAG.fullmatch(name):
        return "tag"
    return None


def citations(documents):
    """(name lowered, "file:line") for every single-symbol backquoted span."""
    for relative, text in documents:
        for number, line in enumerate(text.splitlines(), 1):
            for match in SPAN.finditer(line):
                span = match.group(1).strip()
                if SYMBOL.fullmatch(span):
                    yield span.lower(), f"{relative}:{number}"


def abbreviated(name: str) -> list[str]:
    """`fn-store-metadata-config-frame/-decode' is prose for two names: the
    first, and the first with its last segment replaced by each `/-SUFFIX'
    (`fn-store-metadata-config-decode').  A span without `/-' is itself."""
    if "/-" not in name:
        return [name]
    first, *suffixes = name.split("/-")
    stem = first.rsplit("-", 1)[0]
    return [first] + [f"{stem}-{suffix}" for suffix in suffixes]


def check(defined: set, documents, exemptions: dict) -> Result:
    named = {name.lower(): reason for name, reason in exemptions.get("exemptions", {}).items()}
    listed = {}  # name -> (packet, set of files)
    for packet, entries in exemptions.get("stale", {}).items():
        for name, files in entries.items():
            listed[name.lower()] = (packet, set(files))
    result = Result()
    seen_listed: set = set()
    seen_named: set = set()
    for name, where in citations(documents):
        result.checked += 1
        if name in defined or all(n in defined for n in abbreviated(name)):
            result.resolved += 1
            continue
        rule = rule_for(name)
        if rule:
            result.ruled[rule] += 1
            continue
        if name in named:
            seen_named.add(name)
            result.exempted[name] = result.exempted.get(name, 0) + 1
            continue
        file = where.rsplit(":", 1)[0]
        if name in listed and file in listed[name][1]:
            seen_listed.add((name, file))
            result.stale.setdefault(name, []).append(where)
            continue
        result.unlisted.setdefault(name, []).append(where)
    for name, reason in sorted(named.items()):
        if not isinstance(reason, str) or not reason.strip():
            result.unused.append(f"exemption {name}: no reason given")
    for name in sorted(set(named) - seen_named):
        result.unused.append(f"exemption {name}: no longer cited")
    for name, (packet, files) in sorted(listed.items()):
        for file in sorted(files):
            if (name, file) not in seen_listed:
                result.unused.append(f"{packet} {name} in {file}: no longer an unresolved citation there")
    return result


def macro_generated_definitions(text: str, corpus: str | None = None) -> set[str]:
    """Literal definitions in macro templates invoked somewhere.

    The invocation may be in the same book or, when CORPUS carries the
    joined text of every book, in any of them: a generator macro defined
    in one book and invoked in another (books/output-tariff-family.lisp's
    def-family-tariffs, invoked by books/output-tariff-families.lisp)
    defines its template's literal names in the world just the same."""
    from ledger import Reader

    where = text if corpus is None else corpus
    # books/recovery-profile-buffer.lisp defines its stobj through a macro;
    # books/output-tariff-family.lisp's generator backquotes one progn and
    # defines every name the spec cites inside it.
    names = set()
    for macro in re.finditer(r"^[ \t]*\(defmacro\s+([^\s()]+)", text, re.M | re.I):
        name = macro.group(1)
        if not re.search(r"^\(" + re.escape(name) + r"(?=[\s)])", where, re.M | re.I):
            continue
        # Read just this form to keep the search inside the macro's body.
        reader = Reader(text)
        reader.pos = macro.start()
        reader.form()
        body = text[macro.end():reader.pos]
        for tick in re.finditer(r"`", body):
            # The backquoted region is one form: a definition, or a progn
            # (or list of) definitions anywhere inside it.  Only the fn-
            # prefixed names the checker's domain covers are harvested.
            region = Reader(body)
            region.pos = tick.start()
            try:
                region.form()
            except Exception:
                continue
            template = body[tick.start():region.pos]
            names.update(re.findall(
                r"\((?:defstobj|defun|defthm)\s+(fn[a-z0-9]*-[a-z0-9\-*+?!<>=/%.]*)",
                template, re.I))
    return {name.lower() for name in names}


def concatenated_macro_definitions(text: str, calls=None) -> set[str]:
    """Read definition names constructed from a definer's first argument.

    This is a deliberately limited, source-only expansion of name/list
    expressions, not a Lisp runner. Helpers and constants come from the
    definer's book. Unknown operations/conditions stay unknown; we never
    union conditional branches or treat a referenced name as a definition.
    Definition bodies are opaque: only their name slots matter here.
    """
    from ledger import Reader, Sym, head

    class Prefix(Sym):
        pass

    class NameText(str):
        pass

    class JoinedNameText(NameText):
        pass

    class BuiltName(Prefix):
        pass

    unknown = object()
    forms = [form for form, _ in Reader(text).top_level()]
    functions = {str(f[1]): f for f in forms
                 if head(f) in ("defun", "defmacro") and len(f) >= 4}
    constants = {str(f[1]): f[2] for f in forms
                 if head(f) == "defconst" and len(f) == 3}
    declarations = {"defun", "defun-nx", "defthm", "defconst", "defstobj"}
    steps = 0

    def nilp(x):
        return x == [] or isinstance(x, Sym) and x == "nil"

    def truth(x):
        return unknown if x is unknown else not nilp(x)

    def equal(a, b):
        if a is unknown or b is unknown:
            return unknown
        if nilp(a) or nilp(b):
            return nilp(a) and nilp(b)
        if isinstance(a, Sym) != isinstance(b, Sym):
            return False
        if isinstance(a, list) and isinstance(b, list):
            parts = [equal(x, y) for x, y in zip(a, b)]
            return unknown if unknown in parts else len(a) == len(b) and all(parts)
        return a == b

    def car(x):
        return unknown if x is unknown else x[0] if isinstance(x, list) and x else []

    def cdr(x):
        if x is unknown:
            return unknown
        if not isinstance(x, list) or not x:
            return []
        return x[2] if len(x) == 3 and x[1] == Sym(".") else x[1:]

    def template(x, env):
        if not isinstance(x, list):
            return x
        if head(x) == "unquote":
            return evaluate(x[1], env)
        # Do not descend into a theorem's statement/hints or a function's
        # implementation: a DEFUN mentioned there is not an emitted event.
        if head(x) in declarations:
            return [x[0], template(x[1], env)]
        if head(x) == "quasiquote":
            return unknown  # nested template levels are not modelled
        result = []
        for item in x:
            if head(item) == "unquote-splicing":
                value = evaluate(item[1], env)
                result.extend(value if isinstance(value, list) else [unknown])
            else:
                result.append(template(item, env))
        return result

    def evaluate(x, env):
        nonlocal steps
        steps += 1
        if steps > 100000:
            raise ValueError("name expansion exceeded its work budget")
        if isinstance(x, Sym):
            if x in env:
                return env[x]
            if x in constants:
                return evaluate(constants[x], env)
            return x if x in ("nil", "t") or x.startswith(":") else unknown
        if not isinstance(x, list) or not x:
            return x
        op, args = head(x), x[1:]
        if op == "quote":
            return args[0]
        if op == "quasiquote":
            return template(args[0], env)
        if op in ("let", "let*"):
            scope = dict(env)
            for binding in args[0]:
                scope[binding[0]] = evaluate(binding[1], scope if op == "let*" else env)
            return evaluate(args[-1], scope)
        if op == "if":
            condition = truth(evaluate(args[0], env))
            return unknown if condition is unknown else evaluate(args[1] if condition else args[2], env)
        if op == "cond":
            for clause in args:
                condition = truth(evaluate(clause[0], env))
                if condition is unknown:
                    return unknown
                if condition:
                    return evaluate(clause[-1], env)
            return []
        if op in ("and", "or"):
            value = Sym("t") if op == "and" else []
            for arg in args:
                value = evaluate(arg, env)
                condition = truth(value)
                if condition is unknown or condition == (op == "or"):
                    break
            return value
        values = [evaluate(arg, env) for arg in args]
        if op in functions:
            function = functions[op]
            if len(values) != len(function[2]) or any(str(a).startswith("&") for a in function[2]):
                return unknown
            return evaluate(function[-1], dict(zip(function[2], values)))
        if op == "list":
            return values
        if op == "cons":
            a, b = values
            return [a] + b if isinstance(b, list) else [a] if nilp(b) else [a, Sym("."), b]
        if op == "append":
            if any(v is unknown or not (isinstance(v, list) or nilp(v)) for v in values):
                return unknown
            return [item for v in values if isinstance(v, list) for item in v]
        if re.fullmatch(r"c[ad]+r", op):
            value = values[0]
            for letter in reversed(op[1:-1]):
                value = car(value) if letter == "a" else cdr(value)
            return value
        if any(v is unknown for v in values):
            return unknown
        if op in ("endp", "null", "not", "atom", "consp", "symbolp"):
            value = values[0]
            answer = {"endp": not isinstance(value, list) or not value,
                      "null": not truth(value), "not": not truth(value),
                      "atom": not isinstance(value, list) or not value,
                      "consp": isinstance(value, list) and bool(value),
                      "symbolp": isinstance(value, Sym) or value == []}[op]
            return Sym("t") if answer else []
        if op in ("eq", "equal", "eql"):
            answer = equal(*values)
            return unknown if answer is unknown else Sym("t") if answer else []
        if op in ("assoc-eq", "assoc-equal"):
            for row in [] if nilp(values[1]) else values[1]:
                answer = equal(car(row), values[0])
                if answer is unknown:
                    return unknown
                if answer:
                    return row
            return []
        if op in ("member-eq", "member-equal"):
            for i, item in enumerate([] if nilp(values[1]) else values[1]):
                answer = equal(item, values[0])
                if answer is unknown:
                    return unknown
                if answer:
                    return values[1][i:]
            return []
        if op == "strip-cdrs":
            return [cdr(row) for row in values[0]]
        if op == "symbol-name" and isinstance(values[0], Sym):
            value = str(values[0]).upper()
            return NameText(value) if isinstance(values[0], Prefix) else value
        if (op == "concatenate" and values[0] == Sym("string")
                and all(isinstance(v, str) and not isinstance(v, Sym) for v in values[1:])):
            value = "".join(values[1:])
            return JoinedNameText(value) if any(isinstance(v, NameText) for v in values[1:]) else value
        if op in ("length", "len"):
            return len(values[0])
        if op == "subseq":
            return values[0][values[1]:values[2] if len(values) > 2 else None]
        if op == "intern-in-package-of-symbol" and isinstance(values[0], str) and not isinstance(values[0], Sym):
            return BuiltName(values[0].lower()) if isinstance(values[0], JoinedNameText) else Sym(values[0].lower())
        return unknown

    def emitted(x):
        if head(x) in declarations:
            return {str(x[1])} if isinstance(x[1], BuiltName) and SYMBOL.fullmatch(x[1]) else set()
        if head(x) in ("progn", "encapsulate"):
            return set().union(*(emitted(y) for y in x[1:]))
        return set()

    names = set()
    for call in forms if calls is None else calls:
        macro = functions.get(head(call))
        if not macro or head(macro) != "defmacro" or len(call) < 2 or not isinstance(call[1], Sym):
            continue
        # Bind the actual macro arguments, including keyword arguments as
        # unevaluated source forms. Only the first argument carries provenance.
        formals = macro[2]
        if not formals or not isinstance(formals[0], Sym) or formals[0].startswith("&"):
            continue
        env = {formals[0]: Prefix(call[1])}
        rest = call[2:]
        try:
            keywords = False
            keyword_values = {}
            keyword_formals = set()
            for formal in formals[1:]:
                if formal == Sym("&key"):
                    keywords = True
                    if len(rest) % 2:
                        raise ValueError("unpaired keyword argument")
                    for key, value in zip(rest[::2], rest[1::2]):
                        if not isinstance(key, Sym):
                            raise ValueError("non-symbol keyword argument")
                        keyword_values.setdefault(key, value)
                    continue
                if not isinstance(formal, Sym) or formal.startswith("&"):
                    raise ValueError("unsupported macro argument")
                if keywords:
                    key = Sym(":" + formal)
                    keyword_formals.add(key)
                    env[formal] = keyword_values.get(key, [])
                else:
                    env[formal], rest = rest[0], rest[1:]
            if (keywords and keyword_values.keys() - keyword_formals) or (not keywords and rest):
                raise ValueError("unexpected macro argument")
            steps = 0
            expansion = evaluate(macro[-1], env)
            if head(expansion) == "make-event":
                expansion = evaluate(expansion[1], {})
            names |= emitted(expansion)
        except (ValueError, TypeError, IndexError, RecursionError):
            # Unsupported source is unresolved, never an exemption.
            continue
    return names


def defined_names() -> set:
    sys.path.insert(0, str(ROOT / "tools"))
    import ledger  # noqa: E402
    tree = ledger.load_tree()
    names = set(tree.functions) | set(tree.theorems) | set(tree.constrained)
    for book in tree.books.values():
        names |= book.definitions
    for host in tree.hosts.values():
        names |= host.defines | host.macros
    # A record's own name, `(fn-defrecord fn-node-state ...)'
    # (books/defrecord.lisp): prose names the record kind by it.
    books = sorted((ROOT / "books").glob("*.lisp"))
    book_texts = [path.read_text(encoding="utf-8", errors="replace") for path in books]
    books_corpus = "\n".join(book_texts)
    # Restrict helper expansion to books which construct names, and actual
    # top-level invocations. Comments, quoted examples and function bodies
    # cannot manufacture a definer invocation.
    definers = [text for text in book_texts
                if re.search(r"\(defmacro\s", text, re.I) and re.search(r"\(concatenate\s", text, re.I)]
    macro_names = {str(form[1]) for text in definers
                   for form, _ in ledger.Reader(text).top_level() if ledger.head(form) == "defmacro"}
    calls = [form for text in book_texts for form, _ in ledger.Reader(text).top_level()
             if ledger.head(form) in macro_names]
    for text in definers:
        names |= concatenated_macro_definitions(text, calls)
    for text in book_texts:
        names |= set(re.findall(r"^\s*\(fn-defrecord\s+([^\s()]+)", text, re.M | re.I))
        names |= macro_generated_definitions(text, books_corpus)
        # A named theory, `(deftheory fn-tcl-cheap-rules ...)', and an
        # abstract stobj's exported, recognizer and creator names,
        # `(fn-arena-seal-buffer :logic ... :exec ...)' inside `defabsstobj'.
        names |= set(re.findall(r"\(deftheory\s+([a-z][^\s()]*)", text, re.I))
        names |= set(re.findall(r"\((fn[^\s()]*)\s+:logic\s", text, re.I))
        # A def-generic's exports (books/def-representation-generic.lisp), each
        # its :exports row's second word, `(:update fn-arena-seal-buffer :logic ...)',
        # as host_check.stobj_names reads them.
        names |= set(re.findall(r"\(:(?:read|update)\s+(fn[^\s()]*)\s+:logic\s", text, re.I))
        # A cursor's generated step (books/def-cursor.lisp: def-cursor and
        # def-cursor/output intern NAME-STEP), `(def-cursor/output fn-nnw-stream ...)'.
        names |= {name + "-step" for name in re.findall(
            r"^\s*\(def-cursor(?:/output)?\s+([^\s()]+)", text, re.M | re.I)}
    # Named rows and sections a definer macro introduces by its first
    # argument: a carried relation, `(def-carried fn-owner-served-carried ...)'
    # (books/def-carried.lisp), a raw host section,
    # `(def-section fnn-quantum-mux-finish ...)' (host/native/owner.lisp), and an
    # octet buffer stobj, `(def-buffer fn-octets-ctl)' (books/def-buffer.lisp).
    for path in sorted((ROOT / "books").glob("*.lisp")) + sorted((ROOT / "host").rglob("*.lisp")):
        text = path.read_text(encoding="utf-8", errors="replace")
        names |= set(re.findall(r"^\s*\(def-(?:carried|section|buffer)\s+([^\s()]+)", text, re.M | re.I))
    # A raw host function defined inside a top-level LET over private state,
    # `(let* (...) (labels (...) (defun fnn-raw-dispatch-apply ...)))'
    # (host/native/raw-trap.lisp): ledger's host reading keeps top-level forms.
    for path in sorted((ROOT / "host").rglob("*.lisp")):
        text = path.read_text(encoding="utf-8", errors="replace")
        names |= set(re.findall(r"^[ \t]+\(defun\s+(fnn-[^\s()]+)", text, re.M | re.I))
    return {name.lower() for name in names}


def documents(root: Path = ROOT):
    for directory in ("specs", "docs"):
        for path in sorted((root / directory).glob("*.md")):
            yield path.relative_to(root).as_posix(), path.read_text(encoding="utf-8")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 on an unlisted unresolved citation or an unused entry")
    parser.add_argument("--summary", action="store_true", help="counts and failures only")
    parser.add_argument("--list", action="store_true", help="every unresolved citation")
    args = parser.parse_args(argv)
    exemptions = json.loads(EXEMPTIONS.read_text(encoding="utf-8"))
    result = check(defined_names(), list(documents()), exemptions)
    stale_count = sum(len(v) for v in result.stale.values())
    print(f"spec-cite: {result.checked} single-name citations in specs/ and docs/; "
          f"{result.resolved} defined; by rule {result.ruled['template']} template, "
          f"{result.ruled['short']} short, {result.ruled['tag']} tag; "
          f"{sum(result.exempted.values())} exempted ({len(result.exempted)} names, reasons in "
          f"{EXEMPTIONS.relative_to(ROOT)}); {stale_count} known stale "
          f"({len(result.stale)} names, listed by packet); "
          f"{sum(len(v) for v in result.unlisted.values())} unlisted")
    if args.list:
        for name, where in sorted(result.stale.items()):
            print(f"  stale {name}: {', '.join(where)}")
    for name, where in sorted(result.unlisted.items()):
        print(f"  UNDEFINED {name}: {', '.join(where)} (no book, test book or host file defines it)")
    for line in result.unused:
        print(f"  UNUSED {line}")
    return 1 if args.strict and not result.ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
