#!/usr/bin/env python3
"""Author-only resource overlay; preserve the frozen encapsulate and LOCAL scope.

Public ACL2 three-argument WITH-PROVER-STEP-LIMIT passes T as no-change-flg
(history-management.lisp:3346); unlike the ordinary two-argument wrapper it
never debits the enclosing event. A quoted one-element time list establishes
an independent deadline (axioms.lisp:25888). No ACL2 is launched here.

Author CLI requires --expected-sha and exactly one selector: --form-index
(one-based) or --contains-generator (a unique top-level encapsulate containing
one reviewed pool emitter). The historical SHA is only the Python API default;
future author sources supply their reviewed SHA explicitly. The grammar and
emitter allowlist remain deliberately pool-specific; this is not a macro evaluator.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import lisp_rewrite as lr

FROZEN_SHA = '2bf0be9f8059897d6f7809a52fdbd3d74f2767d44ff8b0e876b0ed6a17c5c86c'
GENERATORS = frozenset('''fn2-pool-frame-row-events fn2-pool-frame-scalar-events
fn2-pool-frame-retired-events fn2-pool-key-frame-events fn2-pool-except-frame-events
fn2-pool-free-slots-frame-events fn2-pool-retired-frame-events fn2-pool-chain-frame-events
fn2-pool-accounts-frame-events fn2-pool-op-conservation-events'''.split())
CONTAINERS = {'encapsulate': 2, 'progn': 1, 'local': 1}
ATOMIC_EVENTS = frozenset(('defconst', 'deftheory', 'defun', 'defmacro', 'make-event',
                           'defthm', 'in-theory', 'assert-event', 'verify-guards',
                           'fn2-pool-op-conservation'))
FACTORIES = frozenset(('fn2-pool-frame-events', 'fn2-pool-frame-retired-events',
                       'fn2-pool-key-frame-events', 'fn2-pool-except-frame-events',
                       'fn2-pool-free-slots-frame-events', 'fn2-pool-retired-frame-events',
                       'fn2-pool-chain-frame-events', 'fn2-pool-accounts-frame-events'))

class OverlayError(ValueError):
    pass

def head(node):
    return node.items[0].low if isinstance(node, lr.Lst) and node.items and isinstance(node.items[0], lr.Atom) else ''

def walk(node):
    yield node
    if isinstance(node, lr.Pre):
        yield from walk(node.node)
    elif isinstance(node, lr.Lst):
        for child in node.items:
            yield from walk(child)

def unwrap(node):
    if head(node) != 'with-prover-step-limit' or len(node.items) != 4:
        return None
    _, steps, unchanged, timed = node.items
    if not isinstance(unchanged, lr.Atom) or unchanged.low != 't':
        raise OverlayError('step wrapper must use the non-debit T argument')
    if head(timed) != 'with-prover-time-limit' or len(timed.items) != 3:
        raise OverlayError('missing per-event time wrapper')
    return timed.items[2]

def strip_overlay(text):
    parsed = lr.parse(text)
    edits = []
    def visit(node):
        inner = unwrap(node)
        if inner is not None:
            edits.extend([(node.start, inner.start, ''), (inner.end, node.end, '')])
            visit(inner)
        elif isinstance(node, lr.Pre):
            visit(node.node)
        elif isinstance(node, lr.Lst):
            for child in node.items:
                visit(child)
    for form in parsed.forms:
        visit(form)
    return lr.write(text, edits)

def theorem_bodies(text):
    return [text[n.start:n.end] for f in lr.parse(text).forms for n in walk(f) if head(n) == 'defthm']

def declarations(text):
    return [text[n.start:n.end] for f in lr.parse(text).forms for n in walk(f) if head(n) == 'declare']

def make_overlay(text, *, form_index=None, generator=None, steps=2_000_000, seconds=60, expected_sha=FROZEN_SHA):
    digest = hashlib.sha256(text.encode()).hexdigest()
    if expected_sha is not None and digest != expected_sha:
        raise OverlayError(f'frozen source mismatch: {digest}')
    if steps != 2_000_000 or type(seconds) is not int or not 1 <= seconds <= 60:
        raise OverlayError('author overlay requires 2000000 steps and 1..60 seconds per event')
    forms = lr.parse(text).forms
    if form_index is not None and generator is not None:
        raise OverlayError('choose a form index or generator selector, not both')
    if generator is not None:
        generator = generator.lower()
        if generator not in GENERATORS:
            raise OverlayError(f'unreviewed generator selector: {generator}')
        selected = [i for i, form in enumerate(forms, 1)
                    if head(form) == 'encapsulate' and any(
                        head(n) == 'defun' and len(n.items) > 1 and n.items[1].low == generator
                        for n in walk(form))]
        if len(selected) != 1:
            raise OverlayError(f'generator selector must identify exactly one encapsulate; found {len(selected)}')
        form_index = selected[0]
    if form_index is None:
        form_index = 98  # Python API compatibility with the historical pilot.
    if not 1 <= form_index <= len(forms) or head(forms[form_index-1]) != 'encapsulate':
        raise OverlayError('selected top-level form is not the original encapsulate')
    original = text[forms[form_index-1].start:forms[form_index-1].end]
    root = lr.parse(original).forms[0]
    edits = []
    counts = {'direct': 0, 'templates': {}}
    wrapped = set()
    def protect(node, origin):
        if node.start in wrapped:
            raise OverlayError('duplicate resource wrapper')
        wrapped.add(node.start)
        # Insert only. Every original theorem/guard/hint byte is retained.
        edits.append((node.start, node.start,
                      f"(with-prover-step-limit {steps} t\n (with-prover-time-limit '({seconds})\n "))
        edits.append((node.end, node.end, '))'))
        if origin == 'direct':
            counts['direct'] += 1
        else:
            counts['templates'][origin] = counts['templates'].get(origin, 0) + 1
    def templates(node, generator):
        if head(node) == 'defthm':
            protect(node, generator)
            return  # Never modify a theorem statement or its hint subtree.
        if isinstance(node, lr.Pre):
            templates(node.node, generator)
        elif isinstance(node, lr.Lst):
            for child in node.items:
                templates(child, generator)
    def event(node):
        kind = head(node)
        if kind in CONTAINERS:
            for child in node.items[CONTAINERS[kind]:]:
                event(child)
            return
        if not isinstance(node, lr.Lst) or not kind:
            raise OverlayError('unexpected inner event structure')
        if kind in ('with-prover-step-limit', 'with-prover-step-limit!', 'with-prover-time-limit'):
            raise OverlayError('input already has resource wrappers')
        if kind not in ATOMIC_EVENTS:
            raise OverlayError(f'unreviewed inner event macro: {kind}')
        if kind == 'defmacro' and node.items[1].low != 'fn2-pool-op-conservation':
            raise OverlayError('only the reviewed pool conservation event macro is supported')
        if kind == 'make-event':
            calls = {head(n) for n in walk(node) if isinstance(n, lr.Lst) and head(n)}
            if not calls.intersection(FACTORIES) or calls.difference(FACTORIES | {'make-event', 'cons', 'append'}):
                raise OverlayError('unreviewed make-event factory expression')
        if kind == 'defun':
            name = node.items[1].low
            literals = [n for child in node.items[3:] for n in walk(child) if head(n) == 'defthm']
            if literals and name not in GENERATORS:
                raise OverlayError(f'unreviewed generated theorem emitter: {name}')
            if name in GENERATORS:
                for child in node.items[3:]:
                    templates(child, name)
        protect(node, 'direct')
    event(root)
    overlay = lr.write(original, edits)
    if strip_overlay(overlay) != original:
        raise OverlayError('resource stripping did not recover the original exact bytes')
    if theorem_bodies(overlay) != theorem_bodies(original):
        raise OverlayError('a theorem statement/hint body changed')
    if declarations(overlay) != declarations(original):
        raise OverlayError('a guard/declaration body changed')
    if 'fn2-pool-op-conservation-events' in counts['templates'] and counts['templates']['fn2-pool-op-conservation-events'] != 2:
        raise OverlayError('conservation emitter must retain its exact local/global theorem pair')
    manifest = dict(source_sha256=digest, overlay_sha256=hashlib.sha256(overlay.encode()).hexdigest(),
                    form_index=form_index, steps=steps, seconds=seconds, non_debit=True,
                    exact_scope_roundtrip=True, theorem_bodies_unchanged=True, declarations_unchanged=True, **counts)
    return overlay, manifest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--seconds', type=int, default=60,
                        help='per-event deadline, 1..60 seconds; match the authorized run budget')
    parser.add_argument('--expected-sha', required=True,
                        help='reviewed SHA256 of the complete source file (mandatory; no CLI bypass)')
    selector = parser.add_mutually_exclusive_group(required=True)
    selector.add_argument('--form-index', type=int, help='one-based top-level encapsulate index')
    selector.add_argument('--contains-generator', choices=sorted(GENERATORS),
                          help='select the unique encapsulate defining this reviewed pool emitter')
    args = parser.parse_args()
    overlay, manifest = make_overlay(args.source.read_text(), form_index=args.form_index,
                                     generator=args.contains_generator, expected_sha=args.expected_sha.lower(),
                                     seconds=args.seconds)
    args.output.write_text(overlay)
    if args.manifest:
        args.manifest.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, sort_keys=True))

if __name__ == '__main__':
    main()
