#!/usr/bin/env python3
"""Emit additive decoded execution events; preserve the already-live pool layout.

This is source admission input, not certification. Existing dependency books
must have matching installed artifacts. No stobj redefinition policy is added.
"""
from pathlib import Path
import argparse
import hashlib
import json
from proof_repl import forms, form_head

ROOT = Path(__file__).resolve().parents[1]


def selected(path, names=None):
    for form in forms(path.read_text()):
        head = form_head(form)
        if head in {'in-package', 'include-book'}:
            continue
        if names is None:
            yield form
        else:
            # Trusted repository source inventory only; no evaluation.
            fields = form.lstrip('(').split(None, 2)
            if len(fields) > 1 and fields[1].lower().rstrip(')') in names:
                yield form


def emit(root, dependencies, output, declarations=True):
    inputs = []
    result = ['(in-package "ACL2")']
    for book in ('decoded-worker-controller', 'decoded-window-lease', 'decoded-window-read', 'cold-read-layout'):
        result.append('(include-book ' + json.dumps(str(dependencies / 'books' / book)) + ')')
    selections = [
        ('books/decoded-worker-assignment.lisp', None),
        ('books/decoded-worker-job.lisp', None),
        ('books/decoded-worker-backing.lisp', None),
        ('books/page-read-counter-transaction.lisp', {'fn-prb-fixed-widthp'}),
        ('books/cold-read-window.lisp', {'fn-crw-nth', 'fn-crw-naturals', 'fn-crw-supportedp'}),
        ('host/page-window-executor-host.lisp', {'fn-owner-page-window-legacy-writablep', 'fn-owner-page-window-work-permittedp'}),
        ('host/page-decoded-window-host.lisp', {
            'fn-owner-page-decoded-job-assign', 'fn-owner-page-decoded-job-outcome',
            'fn-owner-page-decoded-job-byte-at', 'fn-owner-page-decoded-window-price-status',
            'fn-owner-page-decoded-window-acquire-projected', 'fn-owner-page-window-discovery-kind'}),
    ]
    if declarations:
        selections.append(('host/interfaces.lisp', {
            'create-fn-decoded-job', 'fn-dwj-begin', 'fn-dwj-one', 'fn-dwj-read-observation',
            'fn-owner-page-decoded-job-assign', 'fn-owner-page-decoded-job-outcome',
            'fn-owner-page-decoded-job-byte-at', 'fn-pwz-cold-descriptor', 'fn-pwz-nth',
            'fn-owner-page-decoded-window-price-status', 'fn-oct-nth',
            'fn-owner-page-decoded-window-acquire-projected', 'fn-owner-page-window-discovery-kind'}))
    for relative, names in selections:
        path = root / relative
        result.extend(selected(path, names))
        inputs.append({'file': relative, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    output.write_text('\n\n'.join(result) + '\n')
    output.with_suffix('.json').write_text(json.dumps({
        'scope': 'additive normal source admission; no old stobj layout override or certification',
        'dependency_root': str(dependencies), 'inputs': inputs,
        'events_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
    }, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=ROOT)
    parser.add_argument('--dependency-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--without-declarations', action='store_true')
    args = parser.parse_args()
    emit(args.source_root.resolve(), args.dependency_root, args.output, not args.without_declarations)
