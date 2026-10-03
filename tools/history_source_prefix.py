#!/usr/bin/env python3
"""Emit the ordered, source-loaded P3 bootstrap for native_source_runner.

Proof events stay inside each book's encapsulate; this is execution, not a
certificate. Attachment occurs before the canonical generic history book.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import proof_repl
from proof_repl import encapsulated, forms, head_and_name

BOOKS = [
    'history-columns-logic', 'history-columns-foundation',
    'history-pages-resident', 'history-paged', 'history-paged-adopt',
    'history-image-build-rows', 'history-pages-relocate-step',
    'history-pages-relocate-run', 'history-image-row-step', 'history-root-credit',
]


def quote(path: Path) -> str:
    return json.dumps(str(path))


def generate(source: Path, dependencies: Path, world: Path, output: Path) -> None:
    source = source.resolve(); dependencies = dependencies.resolve(); world = world.resolve()
    # Include normalization is relative to the selected actual source tree.
    proof_repl.ROOT = source
    hashes = {}
    def text(path):
        hashes[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        return path.read_text()
    result = ['(in-package "ACL2")']
    # The ordinary build's attachments precede any held-record vocabulary.
    for book in ('codec-attach', 'records-attach-concrete', 'payload-arena-attach'):
        result.append('(include-book ' + quote(world / 'books' / book) + ')')
    result.append('(set-cbd ' + quote(source / 'books')[:-1] + '/")')
    # These exact compatible cached dependencies were also used by the fresh
    # canonical source session. They do not introduce generic fn-hist.
    for book in ('consumer-event-index', 'history-records'):
        result.append('(include-book ' + quote(dependencies / 'books' / book) + ')')
    result.append('(include-book ' + quote(world / 'books/memory-credits') + ')')
    skip = {'books/' + book for book in BOOKS}
    skip.update({'books/consumer-event-index', 'books/history-records',
                 'books/history-pages-placed', 'books/history-pages-relocate',
                 'books/memory-credits'})
    for name in BOOKS:
        path = source / 'books' / (name + '.lisp')
        hoisted, body = encapsulated(text(path), path.parent, skip, 25)
        result.extend(hoisted)
        if body: result.append(body)
    result.append('(attach-stobj fn-hist fn-hist-paged)')
    path = source / 'books/history-columns.lisp'
    hoisted, body = encapsulated(text(path), path.parent, skip, 25)
    result.extend(hoisted); result.append(body)
    # The exact producer used by the native private candidate.
    path = source / 'books/history-image-builder.lisp'
    matches = [f for f in forms(text(path)) if head_and_name(f)[1] == 'fn-his-build-source-count']
    if len(matches) != 1: raise ValueError('missing actual source count producer')
    result.extend(matches)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('\n\n'.join(result) + '\n')
    events = output.with_suffix('.events.lisp')
    normal = []
    path = source / 'host/history-root-host.lisp'
    normal.extend(f for f in forms(text(path)) if head_and_name(f)[0] == 'defun')
    path = source / 'host/owner-host.lisp'
    normal.extend(f for f in forms(text(path)) if head_and_name(f)[1] == 'fn-owner-orcp-capture')
    path = source / 'books/history-capture-state.lisp'
    normal.extend(f for f in forms(text(path)) if head_and_name(f)[1] in
                  ('fn-history-root-roster-heldp', 'fn-owner-history-reset-status'))
    path = source / 'host/interfaces.lisp'
    normal.extend(f for f in forms(text(path)) if head_and_name(f)[0] == 'definterface'
                  and head_and_name(f)[1] in {
                      'create-fn-hrecs$s', 'create-fn-hist$p', 'fn-hist$p-adopt-stage',
                      'fn-hist$p-root-index-next', 'fn-hist$p-root-generation',
                      'fn-hist$p-read', 'fn-hist$p-append', 'fn-hist$p-candidate-word',
                      'fn-hist$p-dispose', 'fn-hrecs$s-dispose'}
                  or head_and_name(f)[0] == 'definterface' and
                  head_and_name(f)[1].startswith(('fn-hroot-', 'fn-owner-hroot-', 'fn-owner-orcp-load-catalog')))
    events.write_text('\n\n'.join(normal) + '\n')
    output.with_suffix('.json').write_text(json.dumps({
        'kind': 'ordered source execution prefix, not certification',
        'source': str(source), 'dependencies': str(dependencies), 'world': str(world),
        'source_sha256': hashes, 'prefix': str(output), 'events': str(events),
        'raw_after': ['host/native/io.lisp:' + str(source / 'host/native/io.lisp'),
                      'host/native/owner.lisp:' + str(source / 'host/native/owner.lisp'),
                      'host/native/owner.lisp:' + str(source / 'host/native/history-root.lisp')],
    }, indent=2) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('source-root', 'dependency-root', 'world-root', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    a = p.parse_args(); generate(a.source_root, a.dependency_root, a.world_root, a.output)

if __name__ == '__main__': main()
