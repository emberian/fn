#!/usr/bin/env python3
"""Report hint names absent from a book's repository include world.

This is a name check, not ACL2 admission or rune-class validation. Local
imports/definitions are visible in their own book but are not exported.
External-source names absent from the builtin catalog are UNCHECKED. If
external sources are unavailable, unresolved external provenance is also
UNCHECKED (except names defined elsewhere in this repo). Computed theories/hints are
SKIPPED, never evidence of a pass. No Lisp is evaluated. Exit status is zero:
this deliberately has neither a strict mode nor build-gate integration.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
import os
import re
import shutil
from dataclasses import dataclass, field
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ledger
from ledger import Sym, head

ROOT = Path(__file__).resolve().parents[1]


class LocatedReader(ledger.Reader):
    """Add source positions to the existing reader, without a second grammar."""
    def __init__(self, text):
        super().__init__(text)
        self.lines = {}
        self.newlines = [i for i, c in enumerate(text) if c == "\n"]

    def line(self, position):
        return bisect_right(self.newlines, position) + 1

    def form(self):
        self.skip_space()
        line = self.line(self.pos)
        value = super().form()
        if isinstance(value, (list, Sym)):
            self.lines[id(value)] = line
        return value


def symbol(value):
    if not isinstance(value, Sym):
        return None
    name = str(value)
    return name.removeprefix('acl2::').removeprefix('acl2:')


@dataclass(frozen=True, order=True)
class Reference:
    book: str
    line: int
    event: str
    name: str


@dataclass
class Book:
    path: str
    definitions: set = field(default_factory=set)
    exports: set = field(default_factory=set)
    includes: list = field(default_factory=list)  # (path, local, external)
    references: set = field(default_factory=set)
    skipped: list = field(default_factory=list)


@dataclass
class Report:
    findings: list = field(default_factory=list)
    unchecked: list = field(default_factory=list)
    skipped: list = field(default_factory=list)
    books: int = 0


class Scanner:
    def __init__(self, path, text):
        self.book = Book(path)
        self.reader = LocatedReader(text)
        self.forms = self.reader.top_level()
        self.text = text
        self.macros = {str(f[1]): f for f, _ in self.forms if head(f) == 'defmacro'}
        self.expanding = set()

    def line(self, value, fallback):
        return self.reader.lines.get(id(value), fallback)

    def skip(self, value, event, line, reason):
        self.book.skipped.append((self.book.path, self.line(value, line), event, reason))

    def name(self, value, event, line):
        name = symbol(value)
        if name and name not in ('nil', 't') and not name.startswith(':'):
            self.book.references.add(Reference(self.book.path, self.line(value, line), event, name))

    def rune(self, value, event, line):
        if isinstance(value, Sym):
            self.name(value, event, line)
        elif isinstance(value, list) and value and str(value[0]).startswith(':'):
            if len(value) > 1:
                self.name(value[1], event, line)
        else:
            self.skip(value, event, line, 'computed rune')

    def theory(self, value, event, line):
        kind = head(value)
        if value == Sym('nil') or value == []:
            return
        if kind in ('enable', 'disable', 'enable*', 'disable*'):
            for item in value[1:]:
                self.rune(item, event, line)
        elif kind in ('e/d', 'e/d*'):
            for side in value[1:]:
                if head(side) in ('unquote', 'unquote-splicing'):
                    self.skip(side, event, line, 'computed e/d list')
                elif isinstance(side, list):
                    for item in side:
                        self.rune(item, event, line)
                elif side != Sym('nil'):
                    self.skip(side, event, line, 'computed e/d list')
        elif kind == 'quote' and len(value) == 2:
            if isinstance(value[1], list):
                for item in value[1]:
                    self.rune(item, event, line)
            elif value[1] != Sym('nil'):
                self.name(value[1], event, line)
        elif kind in ('union-theories', 'intersection-theories', 'set-difference-theories',
                      'append'):
            for item in value[1:]:
                self.theory(item, event, line)
        elif kind == 'theory' and len(value) == 2 and head(value[1]) == 'quote':
            self.name(value[1][1], event, line)
        else:
            self.skip(value, event, line, 'computed theory')

    def lemma(self, value, event, line):
        if isinstance(value, Sym):
            self.name(value, event, line)
        elif head(value) in (':instance', ':functional-instance') and len(value) > 1:
            self.lemma(value[1], event, line)
        elif isinstance(value, list) and value and str(value[0]).startswith(':'):
            self.rune(value, event, line)
        elif isinstance(value, list):
            for item in value:
                self.lemma(item, event, line)
        else:
            self.skip(value, event, line, 'computed lemma')

    def expand(self, value, event, line):
        if value in (Sym('t'), Sym('nil')) or value == []:
            return
        kind = head(value)
        if kind == ':free' and len(value) > 2:
            self.expand(value[2], event, line)
        elif kind == ':with' and len(value) > 2:
            self.rune(value[1], event, line)
            self.expand(value[2], event, line)
        elif kind and not kind.startswith(':'):
            self.name(value[0], event, line)
        elif isinstance(value, list):
            for item in value:
                self.expand(item, event, line)
        else:
            self.skip(value, event, line, 'computed expansion')

    def hints(self, value, event, line):
        if not isinstance(value, list) or head(value) in ('quote', 'quasiquote'):
            self.skip(value, event, line, 'computed hints')
            return
        for clause in value:
            if not isinstance(clause, list) or not clause or type(clause[0]) is not str:
                self.skip(clause, event, line, 'computed hint')
                continue
            for key, arg in zip(clause[1::2], clause[2::2]):
                if key == ':in-theory':
                    self.theory(arg, event, line)
                elif key in (':use', ':by'):
                    self.lemma(arg, event, line)
                elif key == ':expand':
                    self.expand(arg, event, line)
                elif key == ':induct' and isinstance(arg, list) and arg:
                    self.name(arg[0], event, line)

    def hint_options(self, value, event, line):
        if not isinstance(value, list) or head(value) in ('quote', 'quasiquote'):
            return
        for index, item in enumerate(value[:-1]):
            if item in (':hints', ':guard-hints'):
                self.hints(value[index + 1], event, line)
        for item in value:
            if isinstance(item, list):
                self.hint_options(item, event, line)

    def event(self, form, line, local=False, suppressed=False):
        kind = head(form)
        if not kind:
            return
        line = self.line(form, line)
        if kind in ledger.TRANSPARENT | {'mutual-recursion', 'with-prover-step-limit', 'with-prover-time-limit'}:
            for child in form[1:]:
                self.event(child, line, local or kind == 'local', suppressed)
            return
        if kind == 'encapsulate':
            if len(form) > 1 and not suppressed:
                names = ledger.encapsulated_names(form[1])
                self.book.definitions.update(names)
                if not local:
                    self.book.exports.update(names)
            for child in form[2:]:
                self.event(child, line, local, suppressed)
            return
        if kind in ledger.SUPPRESSING - {'thm'}:
            for child in form[1:]:
                self.event(child, line, local, True)
            return
        if kind in ('quote', 'quasiquote', 'defmacro'):
            if kind == 'defmacro' and not suppressed:
                self.macros[str(form[1])] = form
                self.define({str(form[1])}, local)
            return
        if kind.startswith('def') and len(form) > 1 and not isinstance(form[1], Sym):
            self.skip(form, kind, line, 'computed event name')
            return
        if kind == 'make-event':
            self.skip(form, kind, line, 'computed event')
            if len(form) == 2 and head(form[1]) in ('quote', 'quasiquote'):
                child = (form[1][1] if head(form[1]) == 'quote' else substitute(form[1][1], {}))
                self.event(child, line, local, suppressed)
            return
        if kind == 'include-book' and len(form) > 1 and not suppressed:
            options = ledger.keyword_plist(form[2:])
            external = ':dir' in options
            target = (str(form[1]) if external else
                      ledger.resolve((Path(self.book.path).parent / str(form[1])).with_suffix('.lisp').as_posix()))
            self.book.includes.append((target, local, external))
            return
        expansions = {'fn-defrecord': ledger.defrecord_expansion,
                      'fn-defrecord-export': ledger.defrecord_export_expansion,
                      'def-loop': ledger.def_loop_expansion,
                      'defkeystone': ledger.defkeystone_expansion,
                      'defprotocol': ledger.defprotocol_expansion}
        if kind == 'defevent' and not suppressed:
            opts = ledger.keyword_plist(form[2:])
            self.define({str(opts[k]) for k in (':encode', ':decode', ':recognizer')
                         if isinstance(opts.get(k), Sym) and opts[k] != 'nil'}, local)
            return
        if kind in expansions:
            if suppressed:
                self.skip(form, kind, line, 'suppressed macro expansion')
                return
            for child in expansions[kind](form):
                self.event(child, line, local, suppressed)
            return
        if kind in self.macros and kind not in self.expanding:
            self.expanding.add(kind)
            macro = self.macros[kind]
            env = macro_bindings(macro[2], form[1:])
            for child in templates(macro[3:], env):
                self.event(child, line, local, suppressed)
            self.expanding.remove(kind)
            return
        if not suppressed:
            facts = ledger.Book(self.book.path)
            ledger.record(facts, form, line, local=local, suppressed=False)
            self.define(facts.definitions | set(facts.theories), local)
            if kind in ('defun-inline', 'defund-inline', 'define'):
                self.define({str(form[1])}, local)
                if kind.endswith('-inline'):
                    self.define({str(form[1]) + '$inline'}, local)
            if kind == 'defun-sk':
                opts = ledger.keyword_plist(form[4:])
                quantifier = next((head(x) for x in form[3:] if head(x) in ('forall', 'exists')), None)
                suffix = '-necc' if quantifier == 'forall' else '-suff'
                self.define({str(opts.get(':skolem-name', str(form[1]) + '-witness')),
                             str(opts.get(':thm-name', str(form[1]) + suffix))}, local)
            if kind == 'defstobj':
                self.define(stobj_names(form), local)
            if kind == 'defabsstobj':
                for item in walk(form):
                    if isinstance(item, list) and len(item) > 2 and item[1] == ':logic':
                        self.define({str(item[0])}, local)
        event = (str(form[1]) if len(form) > 1 and isinstance(form[1], Sym)
                 and kind not in ('in-theory', 'thm') else kind)
        if kind in ('in-theory', 'deftheory'):
            self.theory(form[-1], event, line)
        else:
            self.hint_options(form, event, line)

    def define(self, names, local):
        self.book.definitions.update(names)
        if not local:
            self.book.exports.update(names)

    def scan(self):
        for form, line in self.forms:
            self.event(form, line)
        return self.book


def macro_bindings(formals, actuals):
    env, rest, mode = {}, list(actuals), 'required'
    for formal in formals:
        if formal in ('&key', '&rest', '&optional', '&body'):
            mode = str(formal)
            continue
        name = formal[0] if isinstance(formal, list) else formal
        default = literal(formal[1], env) if isinstance(formal, list) and len(formal) > 1 else Sym('nil')
        if mode in ('&rest', '&body'):
            env[str(name)] = rest
            break
        if mode == '&key':
            env[str(name)] = ledger.keyword_plist(rest).get(':' + str(name), default)
        else:
            env[str(name)] = rest.pop(0) if rest else default
    return env


def literal(value, env):
    """Small, data-only template substitutions; unknown computations stay None."""
    if isinstance(value, Sym):
        return env.get(str(value), value if value in ('nil', 't') or value.startswith(':') else None)
    if not isinstance(value, list):
        return value
    kind = head(value)
    if kind == 'quote':
        return value[1]
    args = [literal(x, env) for x in value[1:]]
    if any(x is None for x in args):
        return None
    if kind == 'symbol-name' and args:
        return str(args[0]).upper()
    if kind in ('intern-in-package-of-symbol', 'intern$') and args:
        return Sym(str(args[0]).lower())
    if kind == 'concatenate' and args and args[0] == 'string':
        return ''.join(str(x) for x in args[1:])
    if kind == 'list':
        return args
    if kind == 'append' and all(isinstance(x, list) or x == 'nil' for x in args):
        return [v for x in args if isinstance(x, list) for v in x]
    return None


def substitute(value, env):
    if not isinstance(value, list):
        return value
    if head(value) == 'unquote':
        return literal(value[1], env)
    result = []
    for child in value:
        if head(child) == 'unquote-splicing':
            expanded = literal(child[1], env)
            result.extend(expanded if isinstance(expanded, list) else [None])
        else:
            result.append(substitute(child, env))
    return result


def templates(value, env):
    """Read invoked macro templates, as spec_cite_check does, with arguments.

    Computed names are supported only for literal symbol/string construction;
    this does not execute Lisp or pretend to evaluate arbitrary make-event.
    """
    if head(value) == 'quasiquote':
        yield substitute(value[1], env)
    elif head(value) in ('let', 'let*') and len(value) > 2:
        inner = dict(env)
        for binding in value[1]:
            if isinstance(binding, list) and len(binding) == 2:
                inner[str(binding[0])] = literal(binding[1], inner if head(value) == 'let*' else env)
        yield from templates(value[2:], inner)
    elif isinstance(value, list):
        for child in value:
            yield from templates(child, env)


def walk(value):
    yield value
    if isinstance(value, list):
        for child in value:
            yield from walk(child)


def stobj_names(form):
    """DEFSTOBJ's mechanically named logical entries, including :renaming."""
    name = str(form[1])
    names = {name, name + 'p', 'create-' + name}
    for field in form[2:]:
        if not isinstance(field, list) or not field or not isinstance(field[0], Sym):
            continue
        fname = str(field[0])
        options = ledger.keyword_plist(field[1:])
        if head(options.get(':type')) in ('hash-table', 'stobj-table'):
            names.update(fname + suffix for suffix in
                         ('p', '-get', '-put', '-boundp', '-rem', '-count', '-clear', '-init'))
            continue
        array = head(options.get(':type')) == 'array'
        names.update({fname + 'p', fname + ('i' if array else ''),
                      'update-' + fname + ('i' if array else '')})
        if array:
            names.update({fname + '-length', 'resize-' + fname})
    for i, item in enumerate(form[:-1]):
        if item == ':renaming' and isinstance(form[i + 1], list):
            for old, new in form[i + 1]:
                names.discard(str(old))
                names.add(str(new))
    return names


def acl2_source():
    """Locate the configured install; never execute its launcher or Lisp."""
    if os.environ.get('ACL2_SYSTEM_BOOKS'):
        return Path(os.environ['ACL2_SYSTEM_BOOKS']).parent
    import acl2_slots
    launcher = acl2_slots.configured_acl2()
    path = Path(shutil.which(launcher) or launcher).expanduser().resolve()
    if path.is_file():
        text = path.read_text(errors='replace') if path.stat().st_size < 65536 else ''
        match = re.search(r'--core\s+["\']([^"\']+)["\']', text)
        if match:
            return Path(match[1]).parent
    return None


class ExternalNames:
    """Source provenance only: outside the supplied builtin catalog is UNCHECKED.

    Read literal event headers with the same extraction convention documented
    in acl2-builtins.txt. This is NOT an ACL2 world inventory. Missing source
    or unreadable system syntax keeps unknown names unchecked, never passed.
    """
    def __init__(self, source):
        self.source = source
        self.core = set()
        self.cache = {}
        if source:
            for path in source.glob('*.lisp'):
                if path.name != 'doc.lisp':
                    self.core.update(self.headers(path.read_text(errors='replace')))

    @staticmethod
    def headers(text):
        return {name.lower().removeprefix('acl2::') for name in re.findall(
            r'^\s*\(def[a-z0-9!*+/-]*\s+([a-zA-Z0-9*+/<>=!?$%:_-]+)', text, re.M | re.I)}

    def system(self, references):
        names, seen = set(), set()
        pending = [self.source / 'books' / (p + '.lisp') for p in references] if self.source else []
        incomplete = bool(references) and not self.source
        while pending:
            path = pending.pop().resolve()
            if path in seen:
                continue
            seen.add(path)
            if path not in self.cache:
                try:
                    text = path.read_text()
                    forms = ledger.Reader(text).top_level()
                    found, includes = self.headers(text), []
                    def events(form):
                        kind = head(form)
                        if kind == 'local':
                            return
                        if kind == 'include-book':
                            base = self.source / 'books' if ':dir' in form else path.parent
                            includes.append((base / str(form[1])).with_suffix('.lisp'))
                        elif kind in ledger.TRANSPARENT | {'encapsulate'}:
                            for child in form[1:]:
                                events(child)
                    for form, _ in forms:
                        events(form)
                        for item in walk(form):
                            if (head(item) and head(item).startswith('def') and len(item) > 1
                                    and isinstance(item[1], Sym)):
                                found.add(str(item[1]))
                    self.cache[path] = found, includes, False
                except (OSError, ledger.ReadError):
                    self.cache[path] = set(), [], True
            found, includes, failed = self.cache[path]
            names.update(found)
            pending.extend(includes)
            incomplete |= failed
        return names, incomplete


def audit(root=ROOT, only=None, source=None):
    root = Path(root)
    books = {}
    pending = (list(only) if only is not None else
               [str(p.relative_to(root)) for directory in ('books', 'tests/acl2')
                for p in sorted((root / directory).glob('*.lisp'))])
    targets = set(pending)
    errors = []
    while pending:
        path = pending.pop()
        if path in books:
            continue
        try:
            book = Scanner(path, (root / path).read_text()).scan()
        except (ledger.ReadError, OSError) as exc:
            book = Book(path)
            errors.append((path, 1, '<reader>', str(exc)))
        books[path] = book
        pending.extend(p for p, _, external in book.includes if not external and p not in books)
    all_names = set().union(*(b.definitions for b in books.values()))
    builtins = ledger.acl2_builtins()
    provenance = ExternalNames(source)
    report = Report(books=len(targets), skipped=errors)
    for path in sorted(targets):
        book = books[path]
        visible = set(book.definitions) | builtins
        external = set()
        visited = set()
        pending = list(book.includes)
        while pending:
            target, _, system = pending.pop()
            if system:
                external.add(target)
            elif target not in visited:
                visited.add(target)
                child = books[target]
                visible.update(child.exports)
                pending.extend(item for item in child.includes if not item[1])
        system_names, incomplete = provenance.system(external)
        for ref in sorted(book.references):
            if ref.name not in visible:
                if (ref.name not in all_names and
                        (ref.name in provenance.core or ref.name in system_names or incomplete)):
                    report.unchecked.append(ref)
                else:
                    report.findings.append(ref)
        report.skipped.extend(book.skipped)
    return report


def summary(report):
    return (f'hint-names: {len(report.findings)} findings / '
            f'{len(report.unchecked)} unchecked / {len(report.skipped)} skipped '
            f'({report.books} books; report-only)')


def table(report):
    lines = ['STATUS BOOK:LINE EVENT NAME']
    for status, refs in (('FINDING', report.findings), ('UNCHECKED', report.unchecked)):
        for ref in refs:
            lines.append(f'{status} {ref.book}:{ref.line} {ref.event} {ref.name.upper()}')
    return lines


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--summary', action='store_true')
    parser.add_argument('--table', action='store_true')
    parser.add_argument('--explain', metavar='NAME', help='show last textual change in git history')
    parser.add_argument('--books', nargs='+', help='restrict to these repository books')
    args = parser.parse_args(argv)
    only = [str(Path(p).with_suffix('.lisp')) for p in args.books] if args.books else None
    report = audit(only=only, source=acl2_source())
    if args.table:
        print('\n'.join(table(report)))
    if args.explain:
        name = args.explain
        # -S is literal and case-sensitive; source convention is lowercase.
        result = subprocess.run(['git', 'log', '-S', name.lower(), '--oneline', '-1', '--',
                                 'books', 'tests/acl2'], cwd=ROOT, text=True, capture_output=True)
        print(f'{name.upper()}: {result.stdout.strip() or "no textual change found"}')
        print('History is a textual change, not evidence that an event was removed.')
    if args.summary or not (args.table or args.explain):
        print(summary(report))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
