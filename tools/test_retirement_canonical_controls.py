#!/usr/bin/env python3
"""Source identity controls; does not load ACL2 or execute Lisp fixtures."""
import hashlib
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]

def shape(node):
    if isinstance(node, lr.Pre):
        return [node.prefix, shape(node.node)]
    if isinstance(node, lr.Lst):
        return [shape(x) for x in node.items]
    return node.text.lower()

def parsed(path):
    return lr.parse(ROOT / path)

def forms_digest(forms):
    return hashlib.sha256(json.dumps([shape(x) for x in forms], separators=(',', ':')).encode()).hexdigest()

class CanonicalControls(unittest.TestCase):
    def test_exact_shared_event_identity(self):
        receipt = json.loads((ROOT / 'tests/retirement-canonical-controls-receipt.json').read_text())
        assertions = 0
        for name, row in receipt['groups'].items():
            tree = parsed(row['shared_source'])
            macro = lr.match('(defmacro ' + name + ' ?*body)', tree.forms, deep=False)
            self.assertEqual(len(macro), 1)
            quoted = macro[0].node.items[-1]
            self.assertIsInstance(quoted, lr.Pre)
            self.assertEqual(quoted.prefix, "'")
            events = quoted.node.items[1:]
            self.assertEqual(forms_digest(events), row['sha256'], name)
            self.assertEqual(len(events), row['forms'])
            actual = sum(isinstance(x, lr.Lst) and x.items[0].text.lower() == 'assert-event' for x in events)
            self.assertEqual(actual, row['assertions'])
            if 'dispatcher_assertions' in row:
                dispatch = len(lr.match('(assert-event (fn2-riud-run ?case))', events, deep=False))
                self.assertEqual(dispatch, row['dispatcher_assertions'])
                self.assertEqual(actual - dispatch, row['cursor_assertions'])
            assertions += actual
        publication = receipt['publish_entry']
        self.assertEqual(hashlib.sha256((ROOT / publication['source']).read_bytes()).hexdigest(), publication['byte_sha256'])
        self.assertEqual(assertions + publication['assertions'], 32)

    def test_canonical_selects_one_served_world_and_all_shared_controls(self):
        tree = parsed('tests/retirement-canonical-core-unit.lisp')
        self.assertEqual(len(lr.match('(include-book "retirement-publish-core-unit")', tree.forms, deep=False)), 1)
        self.assertFalse(lr.match('(include-book "retirement-core-instance")', tree.forms, deep=False))
        for name in ['fn2-retirement-intent-core-controls-events', 'fn2-retirement-generic-controls-events',
                     'fn2-retirement-dispatch-controls-events']:
            self.assertEqual(len(lr.match('(' + name + ')', tree.forms, deep=False)), 1)
        self.assertFalse(lr.match('(defun ?*body)', tree.forms, deep=False))

    def test_historical_partial_entries_select_same_events(self):
        for source, name in [('tests/retirement-intent-core-unit.lisp', 'fn2-retirement-generic-controls-events'),
                             ('tests/retirement-dispatch-core-unit.lisp', 'fn2-retirement-dispatch-controls-events')]:
            tree = parsed(source)
            self.assertEqual(len(lr.match('(' + name + ')', tree.forms, deep=False)), 1)
            self.assertFalse(lr.match('(defun ?*body)', tree.forms, deep=False))

if __name__ == '__main__':
    unittest.main()
