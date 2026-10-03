#!/usr/bin/env python3
"""Emit the current native logical world as ordinary, resumable ACL2 source.

A matching certificate is an input optimization, never the verdict for source
admission. Changed books keep their local proof scope. The early history
attachment deliberately precedes introduction of the generic history stobj.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import certs
import proof_repl
from proof_repl import encapsulated, forms, head_and_name

EARLY = ('books/codec-attach', 'books/records-attach-concrete',
         'books/payload-arena-attach', 'books/history-paged')
ATTACH = 'books/history-paged-attach'


def generate(source: Path, caches: list[Path], output: Path, limit=25.0):
    source = source.resolve()
    caches = [p.resolve() for p in caches]
    proof_repl.ROOT = source
    graph = certs.include_graph(source, ['books/image-world', *EARLY, ATTACH])
    fingerprints = {name: certs.book_facts(source / (name + '.lisp'))[0]
                    for name in graph}
    match_memo = {}
    def matches(cache, name):
        key = (str(cache), name)
        if key not in match_memo:
            path = cache / (name + '.lisp')
            match_memo[key] = False
            if path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == fingerprints[name]:
                match_memo[key] = all(matches(cache, child) for child in graph[name])
        return match_memo[key]

    loaded = set()
    events = ['(in-package "ACL2")', '(set-cbd ' + json.dumps(str(source / 'books') + '/') + ')']
    coordinate = []
    inputs = {}
    def remember(path):
        inputs[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    def visit(name):
        if name in loaded:
            return
        if name == ATTACH:
            # Ordinary source order is include P3, attach, then generic.
            path = source / (name + '.lisp')
            actual = forms(path.read_text())
            expected = ['(in-package "ACL2")', '(include-book "history-paged")',
                        '(attach-stobj fn-hist fn-hist-paged)', '(include-book "history-columns")']
            if actual != expected:
                raise ValueError('history attachment order changed; inspect actual source before emitting')
            remember(path)
            visit('books/history-paged')
            events.append(actual[2])
            visit('books/history-columns')
            loaded.add(name)
            coordinate.append({'book': name, 'kind': 'ordered-attachment'})
            return
        selected = next((cache for cache in caches
                         if (cache / (name + '.cert')).is_file()
                         and (cache / (name + '.port')).is_file()
                         and matches(cache, name)), None)
        if selected is not None:
            # ACL2 still checks the certificate; matching source does not waive
            # compatibility or toolchain checks during the actual include.
            events.append('(include-book ' + json.dumps(str(selected / name)) + ')')
            closure = certs.closure(source, name)
            loaded.update(closure)
            for child in closure:
                remember(selected / (child + '.lisp'))
                for suffix in ('.cert', '.port', '.fasl'):
                    path = selected / (child + suffix)
                    if path.is_file(): remember(path)
            coordinate.append({'book': name, 'kind': 'certificate-input', 'root': str(selected)})
            return
        for child in graph[name]:
            visit(child)
        path = source / (name + '.lisp')
        remember(path)
        hoisted, body = encapsulated(path.read_text(), path.parent, set(graph), limit or None)
        # All local fn include events were resolved above. Only system books
        # or package declarations may remain hoisted.
        events.extend(hoisted)
        events.append('(value-triple (cw "FN_SOURCE_BOOK ' + name + '~%"))')
        if body: events.append(body)
        loaded.add(name)
        coordinate.append({'book': name, 'kind': 'source-admission'})

    # The build umbrella has replay before its attachment block. Explicit
    # early attachment prevents any incidental generic introduction there.
    for name in EARLY[:3]: visit(name)
    visit(ATTACH)
    visit('books/image-world')
    events.append('(value-triple (cw "FN_SOURCE_LOGICAL_WORLD_READY~%"))')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('\n\n'.join(events) + '\n')
    manifest = output.with_suffix('.json')
    manifest.write_text(json.dumps({'kind': 'current logical source admission, not certification',
        'source': str(source), 'cache_roots': [str(p) for p in caches],
        'inputs_sha256': inputs, 'output_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
        'books': coordinate, 'per_event_prover_seconds': limit}, indent=2) + '\n')
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root', type=Path, required=True)
    p.add_argument('--cache-root', type=Path, action='append', default=[])
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--limit', type=float, default=25.0)
    a = p.parse_args()
    print(generate(a.source_root, a.cache_root, a.output, a.limit))

if __name__ == '__main__': main()
