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
import subprocess
from pathlib import Path
import certs
import proof_repl
from proof_repl import encapsulated, forms, head_and_name

EARLY = ('books/codec-attach', 'books/records-attach-concrete',
         'books/payload-arena-attach', 'books/history-paged')
ATTACH = 'books/history-paged-attach'


def selected_defthms(text, deferred, removed):
    result = []
    for form in forms(text):
        head, name = head_and_name(form)
        if head == 'defthm' and name in deferred:
            if any(part in name for part in ('{', 'guard-thm', 'correspondence')):
                raise ValueError('required guard/abstract obligation cannot be deferred: ' + name)
            removed.add(name)
            continue
        if head in {'local', 'encapsulate', 'progn'}:
            inner = form.strip()[1:-1]
            spans = proof_repl.spans(inner)
            start = 2 if head == 'encapsulate' else 1
            changes = []
            for begin, end in spans[start:]:
                replacement = selected_defthms(inner[begin:end], deferred, removed)
                if replacement != inner[begin:end]: changes.append((begin, end, replacement))
            for begin, end, replacement in reversed(changes):
                inner = inner[:begin] + replacement + inner[end:]
            if head == 'local' and len(spans) == 2 and not forms(inner[spans[1][0]:]):
                continue
            form = '(' + inner + ')'
        result.append(form)
    return '\n'.join(result)


def bounded_body(body, steps):
    if not body or not steps: return body
    inner = body.strip()[1:-1]
    spans = proof_repl.spans(inner)
    prefix = inner[:spans[1][1]]
    events = [inner[begin:end] for begin, end in spans[2:]]
    # Ordinary with-prover-step-limit is an embedded event; the ! form is not.
    return '(' + prefix + '\n' + '\n'.join(
        '(with-prover-step-limit ' + str(steps) + ' ' + event + ')' 
        for event in events) + '\n)'


def generate(source: Path, caches: list[Path], output: Path, limit=25.0,
             revision=None, deferred=None, steps=200000):
    source = source.resolve()
    deferred = deferred or {}
    removed = {}
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
        if str(path) not in inputs:
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
                         and not any(deferred.get(child) for child in certs.closure(source, name))
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
        original = path.read_text()
        omitted = set()
        body_text = selected_defthms(original, deferred.get(name, set()), omitted) if deferred.get(name) else original
        if omitted != deferred.get(name, set()):
            raise ValueError('named DEFTHM not found: ' + name)
        if omitted: removed[name] = sorted(omitted)
        hoisted, body = encapsulated(body_text, path.parent, set(graph), limit or None)
        body = bounded_body(body, steps)
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
    output.parent.mkdir(parents=True, exist_ok=True)
    early = output.with_name(output.stem + '.early.lisp')
    early.write_text('\n\n'.join(events) + '\n')
    visit('books/image-world')
    events.append('(value-triple (cw "FN_SOURCE_LOGICAL_WORLD_READY~%"))')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('\n\n'.join(events) + '\n')
    manifest = output.with_suffix('.json')
    manifest.write_text(json.dumps({'kind': 'current logical source admission, not certification',
        'source': str(source),
        'source_revision': revision or subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() if revision or (source / '.git').exists() else None,
        'source_sha256': fingerprints,
        'repository_sha256': {name + '.lisp': fingerprints[name] for name in sorted(loaded)},
        'repository_books': sorted(name + '.lisp' for name in loaded),
        'logical_prefix': str(output.resolve()), 'cache_roots': [str(p) for p in caches],
        'inputs_sha256': inputs, 'output_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
        'books': coordinate, 'deferred_defthms': removed,
        'per_event_prover_steps': steps, 'per_event_prover_seconds': limit}, indent=2) + '\n')
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root', type=Path, required=True)
    p.add_argument('--cache-root', type=Path, action='append', default=[])
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--limit', type=float, default=25.0)
    p.add_argument('--source-revision', help='immutable archive source identity')
    p.add_argument('--step-limit', type=int, default=200000)
    p.add_argument('--defer-defthm', action='append', default=[], metavar='BOOK:NAME',
                   help='explicitly omit an unrelated theorem, never a definition or guard/correspondence obligation')
    a = p.parse_args()
    deferred = {}
    for selection in a.defer_defthm:
        book, name = selection.rsplit(':', 1)
        deferred.setdefault(book.removesuffix('.lisp'), set()).add(name.lower())
    print(generate(a.source_root, a.cache_root, a.output, a.limit, a.source_revision,
                   deferred, a.step_limit))

if __name__ == '__main__': main()
