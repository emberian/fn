#!/usr/bin/env python3
"""Refuse production attachable stobjs introduced in more than one world.

Read every certifiable source root, never evaluate Lisp. Admitted events
establish ownership and ordering; all nested source, including templates and
macro bodies, is checked conservatively for attachments and introductions.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
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
IMPLEMENTATIONS = frozenset({'fn-arena-extent', 'fn-cat-paged', 'fn-hist-paged'})
TEST_EXEMPTIONS = {
    'tests/acl2/def-generic-tests.lisp': (
        ('dgt-g', 'dgt-gs'), 'generator fixtures; never attached'),
    'tests/acl2/def-representation-tests.lisp': (
        ('drt-gen',), 'attaches drt-gen-cols in the same book'),
    'tests/acl2/def-representation-index-tests.lisp': (
        ('dri',), 'generator fixture; never attached'),
}
SOURCE_ROOTS = ('books', 'host', 'tests/acl2')
GENERATOR_LIBRARIES = {
    'books/def-representation-generic.lisp':
        'def-generic / def-representation macro templates; each expansion is checked at its call site',
    'books/def-representation.lisp':
        'def-generic / def-representation macro templates; each expansion is checked at its call site',
}


@dataclass(frozen=True)
class Site:
    book: str
    line: int
    order: int
    name: str
    attachable: bool = False

    @property
    def location(self):
        return f'{self.book}:{self.line}'


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
    """Inspect every symbol, even outside function position or inside quotes."""
    pending = [(form, None)]
    while pending:
        value, parent = pending.pop()
        if isinstance(value, list):
            options = ledger.keyword_plist(value[2:])
            if head(value) == 'def-generic' or (head(value) == 'defabsstobj'
                                              and ':attachable' in options):
                yield 'introduction', value, value
            elif head(value) in {'defstobj', 'defabsstobj'}:
                yield 'concrete-introduction', value, value
            pending.extend((child, value) for child in reversed(value))
        elif symbol(value) == 'attach-stobj':
            yield 'attachment', value, parent


def events(form):
    """Admitted source event positions, excluding quoted templates and bodies."""
    event_head = head(form)
    if event_head == 'def-representation' and len(form) > 1:
        # This generator emits implementation, attachment, generic together
        # for :generic t. Otherwise it introduces one concrete abstract stobj.
        name = form[1]
        options = ledger.keyword_plist(form[2:])
        if symbol(options.get(':generic')) == 't':
            impl = ledger.Sym(str(name) + '-cols')
            yield [ledger.Sym('defabsstobj'), impl]
            yield [ledger.Sym('attach-stobj'), name, impl]
            yield [ledger.Sym('defabsstobj'), name, ledger.Sym(':attachable'), ledger.Sym('t')]
        else:
            yield [ledger.Sym('defabsstobj'), name]
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
        yield from events(child)


def check(root=ROOT):
    root = Path(root)
    introductions = defaultdict(list)
    attachments = defaultdict(list)
    findings = []
    nested = []
    for folder in SOURCE_ROOTS:
        for path in sorted((root / folder).rglob('*.lisp')):
            book = path.relative_to(root).as_posix()
            if book in TEST_EXEMPTIONS:
                continue
            try:
                reader = SourceReader(path.read_text())
                forms = reader.top_level()
            except (OSError, UnicodeError, ledger.ReadError) as error:
                findings.append(f'{book}: READ: {error}')
                continue
            order = 0
            for form, line in forms:
                admitted = set()
                for event in events(form):
                    order += 1
                    event_head = head(event)
                    if event_head not in {'defstobj', 'defabsstobj', 'def-generic', 'attach-stobj'}:
                        continue
                    name = symbol(event[1]) if len(event) > 1 else None
                    if name is None:
                        findings.append(f'{book}:{line}: MALFORMED: {event_head} needs a literal stobj name')
                        continue
                    admitted.add(id(event))
                    options = ledger.keyword_plist(event[2:])
                    attachable = (event_head == 'def-generic' or
                                  (event_head == 'defabsstobj' and ':attachable' in options))
                    site = Site(book, reader.lines.get(id(event), line), order, name, attachable)
                    (attachments if event_head == 'attach-stobj' else introductions)[name].append(site)
                for kind, value, parent in occurrences(form):
                    is_attachment_head = (head(parent) == 'attach-stobj' and parent[0] is value)
                    if id(parent) in admitted and (kind != 'attachment' or is_attachment_head):
                        continue
                    has_argument = (isinstance(parent, list) and len(parent) > 1 and
                                    (kind != 'attachment' or is_attachment_head))
                    name = symbol(parent[1]) if has_argument else None
                    generator = has_argument and name is None
                    nested.append((kind, Site(book, reader.lines.get(id(value), line),
                                              order, name or '<computed>'), generator))
    generics = {name for name, sites in introductions.items() if any(s.attachable for s in sites)}
    owners = {name: next(s.book for s in introductions[name] if s.attachable)
              for name in generics}
    owner_books = set(owners.values())
    for kind, site, generator in nested:
        if kind == 'concrete-introduction' and site.name not in generics:
            continue
        if generator:
            if site.book not in GENERATOR_LIBRARIES:
                findings.append(f'{site.location}: GENERATOR-OUTSIDE-LIBRARY: {site.name} {kind} needs a named generator library')
            continue
        if kind == 'attachment' and site.name in IMPLEMENTATIONS:
            findings.append(f'{site.location}: IMPLEMENTATION-AS-GENERIC: {site.name} is a concrete implementation')
        owner = owners.get(site.name)
        if site.book == owner or (owner is None and site.book in owner_books):
            continue
        reason = 'OUTSIDE-OWNER' if kind == 'attachment' else 'SECOND-INTRODUCTION'
        findings.append(f'{site.location}: {reason}: {site.name} {kind} in nested source outside its owner book')
    for name in sorted(attachments):
        if len(attachments[name]) > 1:
            for site in attachments[name][1:]:
                findings.append(f'{site.location}: SECOND-ATTACHMENT: {name} first attached at {attachments[name][0].location}')
        for site in attachments[name]:
            if name in IMPLEMENTATIONS:
                findings.append(f'{site.location}: IMPLEMENTATION-AS-GENERIC: {name} is a concrete implementation')
            elif name not in generics:
                findings.append(f'{site.location}: NO-GENERIC: {name} has no attachable introduction')
                findings.append(f'{site.location}: OUTSIDE-OWNER: attach-stobj {name} has no owner book')
            else:
                if site.book != owners[name]:
                    findings.append(f'{site.location}: OUTSIDE-OWNER: attach-stobj {name} belongs in {owners[name]}')
    for name in sorted(generics):
        sites = introductions[name]
        if any(name in names for names, _reason in TEST_EXEMPTIONS.values()):
            findings.append(f'{sites[0].location}: TEST-ONLY-SCOPE: {name} is exempt only in its named test book')
        if len(sites) != 1:
            for site in sites[1:]:
                findings.append(f'{site.location}: SECOND-INTRODUCTION: {name} first introduced at {sites[0].location}')
        for site in sites:
            if site.attachable and not any(a.book == site.book and a.order < site.order
                                           for a in attachments[name]):
                findings.append(f'{site.location}: MISSING-PRECEDING-ATTACH: {name} needs attach-stobj before introduction in this book')
    return findings, len(generics), sum(len(v) for v in attachments.values())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    findings, generics, attachments = check(args.root)
    for finding in findings:
        print(finding)
    if findings:
        return 1
    print(f'one_world_check: {generics} attachable generics, {attachments} attachment sites; '
          f'{len(TEST_EXEMPTIONS)} named test-only exemptions; 0 findings')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
