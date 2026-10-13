#!/usr/bin/env python3
"""Check a closed, counted inventory of every single-world source site.

Read books/, host/, and tests/acl2/ without evaluating Lisp. Context never
suppresses a site: wrappers, macros, make-event and templates are all scanned.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
import sys

try:
    from . import ledger
except ImportError:
    # Native preflight uses -I -S, which omits even the script's directory.
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import ledger

ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOTS = ('books', 'host', 'tests/acl2')
IMPLEMENTATIONS = frozenset({'fn-arena-extent', 'fn-cat-paged', 'fn-hist-paged'})
GENERATOR = 'GENERATOR'  # Distinct from a normalized literal symbol.
GENERATOR_LIBRARIES = {
    'books/def-representation-generic.lisp':
        'def-generic / def-representation macro templates; each expansion is checked at its call site',
    'books/def-representation.lisp':
        'def-generic / def-representation macro templates; each expansion is checked at its call site',
}
# The defmacros in these libraries. def-generic always emits an attachable
# introduction; def-representation emits attachment + introduction for :generic t.
GENERATOR_MACROS = {
    'def-generic': 'books/def-representation-generic.lisp',
    'def-representation': 'books/def-representation.lisp',
}
# Source sites, not expansion events: a representation-call is one source site.
# Repeated pairs mean repeated expected occurrences. No filename is exempt.
ALLOWED_SITES = {
    'books/payload-arena.lisp': (
        ('attachment', 'fn-arena'), ('introduction', 'fn-arena')),
    'books/catalog.lisp': (
        ('attachment', 'fn-cat'), ('introduction', 'fn-cat')),
    'books/history-columns.lisp': (
        ('attachment', 'fn-hist'), ('introduction', 'fn-hist')),
    'books/def-representation-generic.lisp': (
        ('introduction', GENERATOR),),
    'books/def-representation.lisp': (
        ('introduction', GENERATOR), ('attachment', GENERATOR)),
    # Positive and must-fail generator fixtures, each by its exact name.
    'tests/acl2/def-generic-tests.lisp': (
        ('introduction', 'dgt-g'),
        ('introduction', 'dgt-g2'),
        ('introduction', 'dgt-g3'),
        ('introduction', 'dgt-g4'),
        ('introduction', 'dgt-g5'),
        ('introduction', 'dgt-g6'),
        ('introduction', 'dgt-g7'),
        ('introduction', 'dgt-gs'),
        ('introduction', 'dgt-gs-bad'),
        ('introduction', 'dgt-gs-unsound')),
    'tests/acl2/def-representation-tests.lisp': (
        ('representation-call', 'drt-gen'),
        ('representation-call', 'drt-r7'),
        ('representation-call', 'drt-v8')),
    'tests/acl2/def-representation-index-tests.lisp': (
        ('introduction', 'dri'),),
}


@dataclass(frozen=True)
class Site:
    book: str
    line: int
    order: int
    name: str
    kind: str
    computed: bool = False

    @property
    def location(self):
        return f'{self.book}:{self.line}'

    @property
    def key(self):
        return self.kind, self.name


def symbol(value):
    if not isinstance(value, ledger.Sym):
        return None
    name = str(value).lower()
    return name.rsplit(':', 1)[-1] if not name.startswith(':') else name


def head(form):
    return symbol(form[0]) if isinstance(form, list) and form else None


class SourceReader(ledger.Reader):
    """Retain exact source lines for conservative nested diagnostics."""
    def __init__(self, source):
        super().__init__(source)
        self.lines = {}

    def form(self):
        self.skip_space()
        line = self.line(self.pos)
        value = super().form()
        if isinstance(value, (list, ledger.Sym)):
            self.lines[id(value)] = line
        return value


def occurrences(form):
    """Every relevant occurrence, regardless of its enclosing context."""
    pending = [(form, None, False)]
    while pending:
        value, parent, emitting = pending.pop()
        if isinstance(value, list):
            event_head = head(value)
            emitting = emitting or event_head in {'defmacro', 'make-event'}
            options = ledger.keyword_plist(value[2:])
            if event_head == 'defabsstobj' and ':attachable' in options:
                yield 'introduction', value, value, False
            elif event_head in GENERATOR_MACROS:
                if event_head == 'def-generic':
                    yield 'introduction', value, value, False
                elif (symbol(options.get(':generic')) == 't' or
                      ':generic' in options and symbol(options[':generic']) != 'nil' or
                      len(value) > 1 and symbol(value[1]) is None):
                    # Computed arguments cannot hide a call behind :generic nil.
                    yield 'representation-call', value, value, False
                else:
                    yield 'concrete-introduction', value, value, emitting
            elif event_head in {'defstobj', 'defabsstobj'}:
                yield 'concrete-introduction', value, value, emitting
            pending.extend((child, value, emitting) for child in reversed(value))
        elif symbol(value) == 'attach-stobj':
            yield 'attachment', value, parent, False


def site_name(kind, value, parent):
    argument = None
    has_argument = isinstance(parent, list) and len(parent) > 1
    if kind == 'attachment':
        has_argument = has_argument and head(parent) == 'attach-stobj' and parent[0] is value
    if not has_argument:
        return '<computed>', True
    argument = parent[1]
    literal = symbol(argument)
    if literal is not None:
        return literal, False
    # Only comma/unquote names match the GENERATOR entries in the libraries.
    return (GENERATOR if head(argument) in {'unquote', 'unquote-splicing'}
            else '<computed>'), True


def events(form, locations=None):
    """Admitted source event positions, excluding quoted templates and bodies."""
    event_head = head(form)
    if event_head == 'def-representation' and len(form) > 1:
        # This generator emits implementation, attachment, generic together
        # for :generic t. Otherwise it introduces one concrete abstract stobj.
        name = form[1]
        options = ledger.keyword_plist(form[2:])
        if symbol(options.get(':generic')) == 't':
            impl = ledger.Sym(str(name) + '-cols')
            generated = [[ledger.Sym('defabsstobj'), impl],
                         [ledger.Sym('attach-stobj'), name, impl],
                         [ledger.Sym('defabsstobj'), name, ledger.Sym(':attachable'), ledger.Sym('t')]]
        else:
            generated = [[ledger.Sym('defabsstobj'), name]]
        for event in generated:
            if locations is not None:
                locations[id(event)] = locations[id(form)]
            yield event
        return
    if event_head in {'local', 'progn', 'progn!', 'defsection-progn'}:
        children = form[1:]
    elif event_head in {'encapsulate', 'defsection'}:
        children = form[2:]
    elif event_head in {'with-output', 'with-guard-checking-event',
                  'with-prover-step-limit', 'with-prover-time-limit'}:
        children = form[-1:]
    else:
        yield form
        return
    for child in children:
        yield from events(child, locations)


def check(root=ROOT):
    root = Path(root)
    findings = []
    sites = []
    concrete = []
    admitted_attachments = defaultdict(list)
    admitted_generics = defaultdict(list)
    for folder in SOURCE_ROOTS:
        for path in sorted((root / folder).rglob('*.lisp')):
            book = path.relative_to(root).as_posix()
            try:
                reader = SourceReader(path.read_text())
                forms = reader.top_level()
            except (OSError, UnicodeError, ledger.ReadError) as error:
                findings.append(f'{book}: READ: {error}')
                continue
            order = 0
            for form, line in forms:
                for event in events(form, reader.lines):
                    order += 1
                    event_head = head(event)
                    if event_head not in {'attach-stobj', 'defabsstobj', 'def-generic', 'defstobj'}:
                        continue
                    name = symbol(event[1]) if len(event) > 1 else None
                    if name is None:
                        findings.append(f'{book}:{line}: MALFORMED: {event_head} needs a literal stobj name')
                        continue
                    location = reader.lines.get(id(event), line)
                    options = ledger.keyword_plist(event[2:])
                    if event_head == 'attach-stobj':
                        admitted_attachments[name].append(Site(book, location, order, name, 'attachment'))
                    elif event_head == 'def-generic' or ':attachable' in options:
                        admitted_generics[name].append(Site(book, location, order, name, 'introduction'))
                for kind, value, parent, emitting in occurrences(form):
                    name, computed = site_name(kind, value, parent)
                    site = Site(book, reader.lines.get(id(value), line), order, name, kind, computed)
                    if kind == 'concrete-introduction':
                        concrete.append((site, emitting))
                    else:
                        sites.append(site)
    generics = {s.name for s in sites if s.kind in {'introduction', 'representation-call'} and not s.computed}
    for site, emitting in concrete:
        if site.name in generics or site.computed and emitting:
            # Reintroductions and computed macro/event emissions are not inert
            # unrelated concrete definitions (RR-A2's hidden bare defabsstobj).
            sites.append(Site(site.book, site.line, site.order, site.name,
                              'introduction', site.computed))
    actual = defaultdict(list)
    for site in sites:
        actual[(site.book, site.key)].append(site)
        if site.computed and (site.book not in GENERATOR_LIBRARIES or site.name != GENERATOR):
            findings.append(f'{site.location}: GENERATOR-OUTSIDE-LIBRARY: {site.name} {site.kind} needs a listed comma-name library site')
            if site.kind == 'attachment':
                findings.append(f'{site.location}: OUTSIDE-OWNER: attach-stobj {site.name} has no literal owner')
    expected = {(book, key): count for book, entries in ALLOWED_SITES.items()
                for key, count in Counter(entries).items()}
    for book, key in sorted(actual.keys() | expected.keys()):
        found = actual[(book, key)]
        wanted = expected.get((book, key), 0)
        location = found[0].location if found else f'{book}:1'
        kind, name = key
        if not wanted:
            findings.append(f'{location}: UNLISTED-SITE: {kind} {name}; found {len(found)}, expected 0')
        elif not found:
            findings.append(f'{location}: MISSING-SITE: {kind} {name}; found 0, expected {wanted}')
        elif len(found) != wanted:
            findings.append(f'{location}: SITE-COUNT: {kind} {name}; found {len(found)}, expected {wanted}')
    # Retain the earlier semantic refusals as additional diagnostics. The
    # closed inventory is decisive even when an event is not admitted source.
    introductions = defaultdict(list)
    attachments = defaultdict(list)
    for site in sites:
        if site.computed:
            continue
        if site.kind == 'representation-call':
            attachments[site.name].append(site)
            introductions[site.name].append(site)
        else:
            (attachments if site.kind == 'attachment' else introductions)[site.name].append(site)
    for name, group in introductions.items():
        group.sort(key=lambda s: (s.book, s.line))
        for site in group[1:]:
            findings.append(f'{site.location}: SECOND-INTRODUCTION: {name} first introduced at {group[0].location}')
    for name, group in attachments.items():
        group.sort(key=lambda s: (s.book, s.line))
        for site in group[1:]:
            findings.append(f'{site.location}: SECOND-ATTACHMENT: {name} first attached at {group[0].location}')
        owners = {s.book for s in introductions[name]}
        for site in group:
            if name in IMPLEMENTATIONS:
                findings.append(f'{site.location}: IMPLEMENTATION-AS-GENERIC: {name} is a concrete implementation')
            if site.book not in owners:
                findings.append(f'{site.location}: OUTSIDE-OWNER: attach-stobj {name} is outside its introducing book')
    for site in sites:
        if site.computed or site.kind not in {'introduction', 'representation-call'}:
            continue
        if site.book.startswith('tests/acl2/') and site.key in ALLOWED_SITES.get(site.book, ()):
            continue
        if not any(g.book == site.book and g.line == site.line
                   for g in admitted_generics[site.name]):
            findings.append(f'{site.location}: MISSING-PRECEDING-ATTACH: {site.name} needs an admitted attachment and introduction; source emission is unresolved')
    for name, group in admitted_generics.items():
        for site in group:
            # Only individually listed fixture introductions may omit an
            # attachment. This does not skip any source in a test book.
            if site.book.startswith('tests/acl2/') and site.key in ALLOWED_SITES.get(site.book, ()):
                continue
            if not any(a.book == site.book and a.order < site.order
                       for a in admitted_attachments[name]):
                findings.append(f'{site.location}: MISSING-PRECEDING-ATTACH: {name} needs attach-stobj before introduction in this book')
    return findings, len(sites), sum(expected.values())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    findings, sites, expected = check(args.root)
    for finding in findings:
        print(finding)
    if findings:
        return 1
    print(f'one_world_check: {sites} source sites, {expected} expected sites; 0 findings')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
