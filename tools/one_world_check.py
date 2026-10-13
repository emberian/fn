#!/usr/bin/env python3
"""Refuse production attachable stobjs introduced in more than one world.

Read books/ and host/ as source, never Lisp evaluation. Quoted generator
outputs and function/macro bodies are data here, not admitted events.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

try:
    from . import ledger
except ImportError:
    import ledger

ROOT = Path(__file__).resolve().parents[1]
IMPLEMENTATIONS = frozenset({'fn-arena-extent', 'fn-cat-paged', 'fn-hist-paged'})
TEST_EXEMPTIONS = {
    'dgt-g': 'tests/acl2/def-generic-tests: generator fixture; never attached',
    'dgt-gs': 'tests/acl2/def-generic-tests: generator fixture; never attached',
    'drt-gen': 'tests/acl2/def-representation-tests: attaches drt-gen-cols in the same book',
    'dri': 'tests/acl2/def-representation-index-tests: generator fixture; never attached',
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
    return name.removeprefix('acl2::').removeprefix('acl2:')


def events(form):
    """Admitted source event positions, excluding quoted templates and bodies."""
    head = ledger.head(form)
    if head == 'def-representation' and len(form) > 1:
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
    if head in {'local', 'progn', 'progn!', 'defsection-progn'}:
        children = form[1:]
    elif head in {'encapsulate', 'defsection'}:
        children = form[2:]
    elif head in {'with-output', 'with-guard-checking-event',
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
    for folder in ('books', 'host'):
        for path in sorted((root / folder).rglob('*.lisp')):
            book = path.relative_to(root).as_posix()
            try:
                forms = ledger.Reader(path.read_text()).top_level()
            except (OSError, UnicodeError, ledger.ReadError) as error:
                findings.append(f'{book}: READ: {error}')
                continue
            order = 0
            for form, line in forms:
                for event in events(form):
                    order += 1
                    head = ledger.head(event)
                    if head not in {'defstobj', 'defabsstobj', 'def-generic', 'attach-stobj'}:
                        continue
                    name = symbol(event[1]) if len(event) > 1 else None
                    if name is None:
                        findings.append(f'{book}:{line}: MALFORMED: {head} needs a literal stobj name')
                        continue
                    options = ledger.keyword_plist(event[2:])
                    attachable = (head == 'def-generic' or
                                  (head == 'defabsstobj' and symbol(options.get(':attachable')) == 't'))
                    site = Site(book, line, order, name, attachable)
                    (attachments if head == 'attach-stobj' else introductions)[name].append(site)
    generics = {name for name, sites in introductions.items() if any(s.attachable for s in sites)}
    for name in sorted(attachments):
        if len(attachments[name]) > 1:
            for site in attachments[name][1:]:
                findings.append(f'{site.location}: SECOND-ATTACHMENT: {name} first attached at {attachments[name][0].location}')
        for site in attachments[name]:
            if name in IMPLEMENTATIONS:
                findings.append(f'{site.location}: IMPLEMENTATION-AS-GENERIC: {name} is a concrete implementation')
            elif name not in generics:
                findings.append(f'{site.location}: NO-GENERIC: {name} has no attachable introduction')
            else:
                owners = {s.book for s in introductions[name] if s.attachable}
                if site.book not in owners:
                    findings.append(f'{site.location}: OUTSIDE-OWNER: attach-stobj {name} belongs in {", ".join(sorted(owners))}')
    for name in sorted(generics):
        sites = introductions[name]
        if name in TEST_EXEMPTIONS:
            findings.append(f'{sites[0].location}: TEST-ONLY-SCOPE: {name} is exempt only in tests/acl2')
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
