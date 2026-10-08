#!/usr/bin/env python3
"""Compare literal ACL2 event statements across a proof-only change.

This checks source events, not macro expansion: unchanged macro calls and an
unchanged generator are required separately. Formula/body bytes and rule classes
are compared; only :hints / :guard-hints may vary. Added local defthms are allowed.
"""
import argparse
from collections import Counter
from pathlib import Path
import subprocess

from lisp_rewrite import Atom, Lst, parse, write


def statements(text):
    result = {}

    def raw(node):
        edits = []

        # Hints are proof metadata only in a declaration's XARGS.  A keyword
        # appearing in executable/quoted data must remain part of the body.
        if node.items[0].low in ('defun', 'defmacro'):
            for declaration in node.items[3:]:
                if not (isinstance(declaration, Lst) and declaration.items and
                        getattr(declaration.items[0], 'low', '') == 'declare'):
                    continue
                for spec in declaration.items[1:]:
                    if not (isinstance(spec, Lst) and spec.items and
                            getattr(spec.items[0], 'low', '') == 'xargs'):
                        continue
                    items = spec.items
                    for i in range(1, len(items), 2):
                        x = items[i]
                        if i + 1 == len(items):
                            raise ValueError('xargs option without value')
                        if isinstance(x, Atom) and x.low in (':hints', ':guard-hints'):
                            edits.append((x.start - node.start,
                                          items[i + 1].end - node.start, ''))
        return write(text[node.start:node.end], edits)

    def walk(node, local=False):
        if not isinstance(node, Lst) or not node.items:
            return
        items = node.items
        head = getattr(items[0], 'low', '')
        if head in ('defthm', 'defun', 'defmacro', 'defstobj', 'defabsstobj', 'def-representation'):
            name = items[1].text
            key = (head, name)
            if key in result:
                raise ValueError(f'duplicate event: {key}')
            if head == 'defthm':
                # Compare every non-hint option too, including rule classes.
                parts = [text[items[2].start:items[2].end]]
                i = 3
                while i < len(items):
                    if items[i].low != ':hints':
                        parts.append(text[items[i].start:items[i + 1].end])
                    i += 2
                result[key] = (local, tuple(parts))
            else:
                result[key] = (local, raw(node))
            return
        for child in items[1:]:
            walk(child, local or head == 'local')

    for form in parse(text).forms:
        walk(form)
    return result


def compare(before, after):
    old, new = statements(before), statements(after)
    errors = []
    for key, value in old.items():
        if new.get(key) != value:
            errors.append(f'changed or removed: {key[0]} {key[1]}')
    added = []
    for key in new.keys() - old.keys():
        if key[0] == 'defthm' and new[key][0]:
            added.append(key[1])
        else:
            errors.append(f'added non-lemma event: {key[0]} {key[1]}')
    return Counter(k[0] for k in old), added, errors


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('base')
    ap.add_argument('files', nargs='+')
    ap.add_argument('--head', default='HEAD', help='revision, or WORKTREE')
    args = ap.parse_args()
    failed = False
    for file in args.files:
        before = subprocess.check_output(['git', 'show', f'{args.base}:{file}']).decode()
        after = (Path(file).read_text() if args.head == 'WORKTREE' else
                 subprocess.check_output(['git', 'show', f'{args.head}:{file}']).decode())
        counts, added, errors = compare(before, after)
        print(f'{file}: {dict(sorted(counts.items()))}; added local lemmas={len(added)}; differences={len(errors)}')
        for error in errors:
            print(error)
        failed |= bool(errors)
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
