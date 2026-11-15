#!/usr/bin/env python3
"""Source-only controls for the single lifecycle event generator.

The checkpoint digest freezes the actual pre-factor generated event trees;
this checks expression preservation, not ACL2 admission or submit execution.
"""
import hashlib
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]

def value(node):
    if isinstance(node, lr.Pre):
        return [node.prefix, value(node.node)]
    if isinstance(node, lr.Lst):
        return [value(x) for x in node.items]
    return node.text.lower()

def forms(path):
    return [value(x) for x in lr.parse(ROOT / path).forms]

def named(fs, head, name):
    return next(f for f in fs if isinstance(f, list) and f[:2] == [head, name])

def adapter(fs, name):
    entries = named(fs, 'defun', name)[-1][1]
    return {entry[0]: entry[2] for entry in entries}

def replace(form, bindings):
    if isinstance(form, str):
        return bindings.get(form, form)
    return [replace(x, bindings) for x in form]

def flatten_events(form):
    assert form[0] == 'progn'
    result = ['progn']
    for event in form[1:]:
        if isinstance(event, list) and event and event[0] == 'progn':
            result.extend(flatten_events(event)[1:])
        else:
            result.append(event)
    return result

def expansions(bindings):
    fs = forms('books/retirement-coordinator.lisp')
    return [flatten_events(replace(named(fs, 'defmacro', name)[-1][1][1], bindings))
            for name in ['fn2-retirement-coordinator-events', 'fn2-retirement-install-events']]

def digest(expansion):
    return hashlib.sha256(json.dumps(expansion, separators=(',', ':')).encode()).hexdigest()

class RetirementAdapter(unittest.TestCase):
    def test_checkpoint_exact_prior_generated_events(self):
        bindings = adapter(forms('books/checkpoint-lifecycle-coordinator.lisp'),
                           'fn2-checkpoint-retirement-adapter')
        self.assertEqual(digest(expansions(bindings)), '60b09fe5b1950928c7f71891a64b395e3416ba0dcdbf67741e2acddc57152b55')

    def test_ordinary_has_real_operations_and_closed_checkpoint_dispatch(self):
        fs = forms('books/retirement-coordinator.lisp')
        bindings = adapter(fs, 'fn2-retirement-ordinary-adapter')
        generated = expansions(bindings)
        names = [f[1] for g in generated for f in g[1:]
                 if isinstance(f, list) and f and f[0] == 'defun']
        self.assertEqual(names, ['fn2-retirement-admit', 'fn2-retirement-submit',
                                'fn2-retirement-poll', 'fn2-commit-lifecycle-step'])
        self.assertEqual(bindings['fn2-retirement-adapter-record-match'], 'nil')
        self.assertEqual(bindings['fn2-retirement-adapter-release'][0], 'fn2-core-release')
        for key in ['fn2-retirement-adapter-allocation', 'fn2-retirement-adapter-installation']:
            self.assertEqual(bindings[key], ['mv', ':invalid', 'fn2-core'])
        self.assertNotIn('fn2-checkpoint-', json.dumps(generated))

if __name__ == '__main__':
    unittest.main()
