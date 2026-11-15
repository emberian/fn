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
# Historical receipt, unchanged. STOP_LET is derived from this same historical
# tree by the narrow normalization below; it is not a new runtime baseline.
PRE_FACTOR_EVENT_SHA256 = '60b09fe5b1950928c7f71891a64b395e3416ba0dcdbf67741e2acddc57152b55'
STOP_LET_NORMAL_FORM_SHA256 = 'eff8a6b456d3d3cd7582b66dd31074ac20aa626317062825073918a4ada7cae9'

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

def normalize_stobj_stop_let(form):
    # Only undo the explicit translation repair: no scalar expression may
    # refer to the rebound core. The historical fingerprint stays unchanged.
    if not isinstance(form, list):
        return form
    form = [normalize_stobj_stop_let(x) for x in form]
    if (len(form) == 3 and form[0] == 'let' and len(form[1]) == 1
            and len(form[1][0]) == 2 and form[1][0][0] == 'fn2-core'
            and isinstance(form[1][0][1], list)
            and (form[1][0][1][0] == 'fn2-core-stop'
                 or form[1][0][1] == ['if', ['eq', 'cancelled', ':ok'], 'fn2-core',
                     ['fn2-core-stop', '*fn2-stop-reason-commit-settle*', 'fn2-core']])
            and isinstance(form[2], list) and len(form[2]) == 5
            and form[2][0] == 'mv'
            and form[2][-1] == 'fn2-core'
            and 'fn2-core' not in json.dumps(form[2][2:4])):
        return form[2][:-1] + [form[1][0][1]]
    return form

def digest(expansion):
    return hashlib.sha256(json.dumps(normalize_stobj_stop_let(expansion), separators=(',', ':')).encode()).hexdigest()

class RetirementAdapter(unittest.TestCase):
    def test_checkpoint_exact_prior_generated_events(self):
        bindings = adapter(forms('books/checkpoint-lifecycle-coordinator.lisp'),
                           'fn2-checkpoint-retirement-adapter')
        self.assertEqual(digest(expansions(bindings)), STOP_LET_NORMAL_FORM_SHA256)

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
