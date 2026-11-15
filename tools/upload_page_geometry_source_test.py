#!/usr/bin/env python3
"""Source identity for the production upload geometry extraction."""
import hashlib
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]

class UploadGeometry(unittest.TestCase):
    def test_original_forms_moved_once(self):
        receipt = json.loads((ROOT/'tools/fixtures/upload-page-geometry-extraction.json').read_text())
        dest = lr.parse(ROOT/'books/upload-page-geometry.lisp')
        bodies = [dest.text[f.start:f.end] for f in dest.forms]
        for oldbook, forms in receipt['forms'].items():
            old = lr.parse(ROOT/oldbook)
            oldbodies = [old.text[f.start:f.end] for f in old.forms]
            for form in forms:
                with self.subTest(book=oldbook, digest=form['sha256']):
                    self.assertEqual(hashlib.sha256(form['form'].encode()).hexdigest(), form['sha256'])
                    self.assertEqual(bodies.count(form['form']), 1)
                    self.assertNotIn(form['form'], oldbodies)

    def test_actual_consumers_share_sizing(self):
        upload = (ROOT/'books/upload.lisp').read_text()
        kind = (ROOT/'books/upload-kind.lisp').read_text()
        self.assertIn('(fn2-upload-input-bound max cap0 cap1)', upload)
        self.assertIn('(article-max (fn2-upload-profile-article-max profile))', kind)
        geometry = (ROOT/'books/upload-page-geometry.lisp').read_text()
        self.assertNotIn('(include-book "upload-kind")', geometry)
        self.assertNotIn('(include-book "ordered")', geometry)
        self.assertIn('(fn2-book-layer :b)', geometry)
        self.assertIn('(include-book "upload-page-geometry")', kind)
        self.assertIn('(include-book "upload-page-geometry")', (ROOT/'books/ordered.lisp').read_text())

if __name__ == '__main__':
    unittest.main()
