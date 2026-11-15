#!/usr/bin/env python3
"""Preserve original stage grammar around the explicit pool preflight."""
import hashlib
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]
class StagePreflight(unittest.TestCase):
    def test_stage_changes_only_by_explicit_preflight(self):
        receipt = json.loads((ROOT/'tools/fixtures/c-stage-preflight-extraction.json').read_text())
        old = receipt['original_stage_form']
        self.assertEqual(hashlib.sha256(old.encode()).hexdigest(), receipt['original_stage_form_sha256'])
        source = lr.parse(ROOT/'books/machines-c-stage.lisp')
        hit = lr.match('_', source.forms, deep=False, head='defun', name='fn2-succ-stage')
        self.assertEqual(len(hit), 1)
        current = source.text[hit[0].start:hit[0].end]
        inserted = '      '+receipt['inserted_bindings']+'\n'
        self.assertEqual(current.count(inserted), 1)
        current = current.replace(inserted, '', 1)
        current = current.replace('fn2-succ-room fn2-idc-stage-pool-preflight fn2-idc-scratch',
                                  'fn2-succ-room fn2-idc-scratch', 1)
        self.assertEqual(lr.emit(lr.parse(current).forms[0], drop_comments=True),
                         lr.emit(lr.parse(old).forms[0], drop_comments=True))

    def test_shared_pool_rule_is_the_actual_reserve_rule(self):
        pool = lr.parse(ROOT/'books/pool.lisp')
        hit = lr.match('_', pool.forms, deep=False, head='defun', name='fn2-pool-reserve')
        self.assertEqual(len(hit), 1)
        self.assertIn('(fn2-pool-reservable-count class fn2-pool)',
                      pool.text[hit[0].start:hit[0].end])
        source = (ROOT/'books/machines-c-stage.lisp').read_text()
        self.assertIn('(<= (+ scratch missing) (fn2-pool-reservable-count scratch-class fn2-pool))', source)
        self.assertNotIn('fn2-pool-credit-protectedi', source)

if __name__ == '__main__':
    unittest.main()
