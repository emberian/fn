#!/usr/bin/env python3
"""Author-only resource overlay; preserve the frozen encapsulate and LOCAL scope.

Public ACL2 three-argument WITH-PROVER-STEP-LIMIT passes T as no-change-flg
(history-management.lisp:3346); unlike the ordinary two-argument wrapper it
never debits the enclosing event. A quoted one-element time list establishes
an independent deadline (axioms.lisp:25888). No ACL2 is launched here.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys
import lisp_rewrite as lr

FROZEN_SHA = '2bf0be9f8059897d6f7809a52fdbd3d74f2767d44ff8b0e876b0ed6a17c5c86c'
GENERATORS = frozenset('''fn2-pool-frame-row-events fn2-pool-frame-scalar-events
fn2-pool-frame-retired-events fn2-pool-key-frame-events fn2-pool-except-frame-events
fn2-pool-free-slots-frame-events fn2-pool-retired-frame-events fn2-pool-chain-frame-events
fn2-pool-accounts-frame-events fn2-pool-op-conservation-events'''.split())
CONTAINERS = {'encapsulate': 2, 'progn': 1, 'local': 1}

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

def make_overlay(text, *, form_index=98, steps=2_000_000, seconds=60, expected_sha=FROZEN_SHA):
    digest = hashlib.sha256(text.encode()).hexdigest()
    if expected_sha is not None and digest != expected_sha:
        raise OverlayError(f'frozen source mismatch: {digest}')
    if steps != 2_000_000 or seconds != 60:
        raise OverlayError('this author retry is authorized only at 2000000 steps / 60 seconds per event')
    forms = lr.parse(text).forms
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
    parser.add_argument('--form-index', type=int, default=98)
    args = parser.parse_args()
    overlay, manifest = make_overlay(args.source.read_text(), form_index=args.form_index)
    args.output.write_text(overlay)
    if args.manifest:
        args.manifest.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, sort_keys=True))

if __name__ == '__main__':
    main()
