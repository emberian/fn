#!/usr/bin/env python3
"""The shared geometry contains the exact moved production forms, once."""
import hashlib
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
def original_form(name, form):
    receipt = json.loads((ROOT/'tools/fixtures/checkpoint-geometry-totalization.json').read_text())
    row = receipt['forms'].get(name)
    if row:
        for old, new in reversed(row['substitutions']):
            if form.count(new) != 1:
                raise AssertionError('missing exact totalization: '+name)
            form = form.replace(new, old)
        if hashlib.sha256(form.encode()).hexdigest() != row['original_raw_sha256']:
            raise AssertionError('changed original scan: '+name)
    return form



class GeometryExtraction(unittest.TestCase):
    def test_moved_forms_keep_original_fingerprint(self):
        receipt = json.loads((ROOT / 'tools/fixtures/checkpoint-working-geometry-extraction.json').read_text())
        source = lr.parse(ROOT / 'books/checkpoint-working-geometry.lisp')
        old = lr.parse(ROOT / receipt['original_book'])
        for name, digest in receipt['raw_form_sha256'].items():
            with self.subTest(name=name):
                found = lr.match('_', source.forms, deep=False, name=name)
                self.assertEqual(len(found), 1)
                form = source.text[found[0].start:found[0].end]
                self.assertEqual(hashlib.sha256(original_form(name, form).encode()).hexdigest(), digest)
                self.assertEqual(lr.match('_', old.forms, deep=False, name=name), [])

    def test_totalized_scans_preserve_each_original_body(self):
        receipt = json.loads((ROOT/'tools/fixtures/checkpoint-geometry-totalization.json').read_text())
        self.assertEqual(len(receipt['forms']), 4)
        for name, row in receipt['forms'].items():
            source = lr.parse(ROOT/row['book'])
            hit = lr.match('_', source.forms, deep=False, name=name)
            self.assertEqual(len(hit), 1)
            original_form(name, source.text[hit[0].start:hit[0].end])

    def test_consumers_share_geometry_without_c_worker(self):
        for name in ('checkpoint-working-reserve', 'checkpoint-working-credit'):
            text = (ROOT / f'books/{name}.lisp').read_text()
            self.assertIn('(include-book "checkpoint-working-geometry")', text)
        geometry = (ROOT / 'books/checkpoint-working-geometry.lisp').read_text()
        self.assertNotIn('(include-book "checkpoint-working-reserve")', geometry)
        self.assertIn('(include-book "checkpoint-future-working")', geometry)
        future = (ROOT / 'books/checkpoint-future-working.lisp').read_text()
        self.assertNotIn('checkpoint-working-geometry', future)
        for name in ('*fn2-checkpoint-future-window-count*',
                     'fn2-checkpoint-future-window-length', 'fn2-checkpoint-future-class-demand'):
            self.assertEqual(len(lr.match('_', lr.parse(future).forms, deep=False, name=name)), 1)


if __name__ == '__main__':
    unittest.main()
