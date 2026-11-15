#!/usr/bin/env python3
"""Extract the actual working-resource leaves without rewriting their forms.

--check-base SHA compares every moved event, including macro invocations and
function signatures, byte for byte with that source commit. No ACL2 is run.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import subprocess
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
# (stage, source, destination, selected names; None selects executable events)
MOVES = [
 ('reserve', 'runs-page', 'run-geometry', {'*fn2-run-page-size*'}),
 ('reserve', 'runs', 'run-geometry', {'*fn2-run-max-levels*'}),
 ('reserve', 'c-snapshot', 'c-snapshot-state', {'fn2-csnapshot', 'fn2-csnapshot-ownerp'}),
 ('reserve', 'checkpoint-future-resources', 'checkpoint-future-working', None),
 ('reserve', 'checkpoint-metadata-resources', 'checkpoint-working-reserve', {
  '*fn2-checkpoint-window-count*', 'fn2-checkpoint-window-length', 'fn2-checkpoint-windows',
  'fn2-checkpoint-root1', 'fn2-checkpoint-window-class-demand', 'fn2-checkpoint-window-roomp',
  'fn2-checkpoint-windows-reserve-loop', 'fn2-checkpoint-admission-roomp',
  'fn2-checkpoint-root1-reserve', 'fn2-checkpoint-root1-workspaces'}),
 ('release', 'checkpoint-metadata-manifest', 'checkpoint-metadata-manifest-state', {'fn2-checkpoint-metadata-manifest'}),
 ('release', 'checkpoint-metadata-release', 'checkpoint-working-release', {'fn2-checkpoint-working-release-step'}),
]
HEADERS = {
 'run-geometry': ('Shared run page and writer-level geometry.', ['format-base'], ':c'),
 'c-snapshot-state': ('Held source-cut state and exact ownership, below live C operations.', ['columns'], ':c'),
 'checkpoint-future-working': ('B-owned future leases and exact pool handback; live registration is separate.', ['std/util/bstar:system', 'checkpoint-member', 'commit-format'], ':b'),
 'checkpoint-working-reserve': ('Actual HELD-cut working-lease admission, independent of source construction.', ['run-geometry', 'c-snapshot-state', 'checkpoint-future-working'], ':c'),
 'checkpoint-metadata-manifest-state': ('Manifest continuation state, independent of its source builder.', ['columns'], ':c'),
 'checkpoint-working-release': ('Actual one-lease cleanup; its composed caller establishes release permission.', ['checkpoint-working-reserve', 'checkpoint-metadata-manifest-state', 'arm-children'], ':c'),
}


def selected(form, names):
    if not isinstance(form, lr.Lst) or len(form.items) < 2:
        return False
    head, name = lr.flat(form.items[0]).lower(), lr.flat(form.items[1]).lower()
    if names is None:
        return head not in {'in-package', 'include-book', 'fn2-book-layer', 'defcorechild'}
    return name in names


def extract(text, names):
    parsed = lr.parse(text)
    nodes = [f for f in parsed.forms if selected(f, names)]
    return nodes, [text[n.start:n.end] for n in nodes]


def header(name):
    title, includes, layer = HEADERS[name]
    lines = ['; ' + title, '(in-package "ACL2")']
    for book in includes:
        if book.endswith(':system'):
            lines.append('(include-book "' + book[:-7] + '" :dir :system)')
        else:
            lines.append('(include-book "' + book + '")')
    return '\n'.join(lines + ['(fn2-book-layer ' + layer + ')', '']) + '\n'


def write_stage(stage):
    outputs = {}
    for group, source, dest, names in MOVES:
        if group != stage:
            continue
        path = ROOT / 'books' / (source + '.lisp')
        text = path.read_text()
        nodes, events = extract(text, names)
        if not nodes:
            raise ValueError('No unmoved events in ' + source)
        outputs.setdefault(dest, []).extend(events)
        parsed = lr.parse(text)
        package = lr.match('(in-package "ACL2")', parsed, deep=False)
        assert len(package) == 1
        edits = [(n.start, n.end, '') for n in nodes]
        edits.append((package[0].end, package[0].end, '\n(include-book "' + dest + '")'))
        path.write_text(lr.write(text, edits))
        print(source, '->', dest, len(events), 'exact events')
    for dest, events in outputs.items():
        path = ROOT / 'books' / (dest + '.lisp')
        if path.exists():
            raise ValueError('Refusing to overwrite ' + str(path))
        path.write_text(header(dest) + '\n\n'.join(events) + '\n')
    if stage == 'reserve':
        path = ROOT / 'books/checkpoint-future-resources.lisp'
        text = path.read_text()
        nodes = [n for n in lr.parse(text).forms if isinstance(n, lr.Lst)
                 and lr.flat(n.items[0]).lower() == 'defcorechild']
        assert len(nodes) == 2
        registrations = [text[n.start:n.end] for n in nodes]
        path.write_text('; Live registration of the B-owned future working leases.\n'
                        '(in-package "ACL2")\n(include-book "checkpoint-future-working")\n'
                        '(include-book "core-children")\n(fn2-book-layer :b)\n\n'
                        + '\n\n'.join(registrations) + '\n')


def check_base(base, stages):
    total = 0
    for stage, source, dest, names in MOVES:
        if stage not in stages:
            continue
        before = subprocess.check_output(['git', 'show', base + ':books/' + source + '.lisp'], cwd=ROOT, text=True)
        _, old = extract(before, names)
        _, new = extract((ROOT / 'books' / (dest + '.lisp')).read_text(), names)
        # Two sources contribute distinct constants to run-geometry.
        if names is not None:
            new = [f for f in new if selected(lr.parse(f).forms[0], names)]
        assert old == new, (source, dest, 'moved form/signature changed')
        remaining, _ = extract((ROOT / 'books' / (source + '.lisp')).read_text(), names)
        assert not remaining, (source, 'duplicate definition retained')
        total += len(old)
    print('Exact moved events/signatures:', total)


def main():
    p = argparse.ArgumentParser(__doc__)
    p.add_argument('--stage', choices=('reserve', 'release', 'all'), default='all')
    p.add_argument('--write', action='store_true')
    p.add_argument('--check-base')
    a = p.parse_args()
    stages = ['reserve', 'release'] if a.stage == 'all' else [a.stage]
    if a.write:
        for stage in stages:
            write_stage(stage)
    if a.check_base:
        check_base(a.check_base, stages)


if __name__ == '__main__':
    main()
