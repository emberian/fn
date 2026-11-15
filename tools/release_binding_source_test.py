"""Shared release field source/geometry controls; no ACL2 result implied."""
from pathlib import Path
import hashlib
import json
import unittest
import lisp_rewrite as lr


def sexp(node):
    if isinstance(node, lr.Lst):
        return [sexp(n) for n in node.items]
    if isinstance(node, lr.Pre):
        return sexp(node.node)
    return node.text


def sum_terms(value):
    if value == 'f':
        return sum_terms(['+', 'base', '*fn2-format-release-allocation-field-release-evidence-storage-domain*'])
    if value == 'body':
        return ['base'], 0
    if isinstance(value, list):
        assert value[0] == '+'
        parts = [sum_terms(v) for v in value[1:]]
        return sorted(t for ts, _ in parts for t in ts), sum(n for _, n in parts)
    try:
        return [], int(value)
    except ValueError:
        return [value], 0


class ReleaseBinding(unittest.TestCase):
    def test_all_numeric_writes_share_exact_source_map(self):
        receipt = json.loads(Path('tools/fixtures/release-member-binding-extraction.json').read_text())
        original = receipt['original_numeric_store_region']
        self.assertEqual(hashlib.sha256(original.encode()).hexdigest(), receipt['original_numeric_store_sha256'])
        writes = []
        for node in lr.parse(original).forms:
            form = sexp(node)
            if form[0] == 'fn2-fields':
                setter = form[1]
                self.assertEqual(setter[0], 'fn2-fields-set-value')
                writes.append((sum_terms(setter[1]), setter[2]))
        text = Path('books/release-member-binding.lisp').read_text()
        form = next(sexp(n) for n in lr.parse(text).forms
                    if sexp(n)[0:2] == ['defconst', '*fn2-release-numeric-bindings*'])
        expected = [(sum_terms(['+', 'base', offset]), [getter, '0', 'fn2-allocation-release'])
                    for offset, getter in form[2]]
        self.assertEqual(len(writes), 13)
        self.assertEqual(writes, expected)
        producer = Path('books/release-allocation.lisp').read_text()
        self.assertIn('(fn2-release-store-numeric-fields body fn2-allocation-release fn2-fields)', producer)
        self.assertNotIn('(fn2-fields-set-value (+ body ', producer)
        self.assertIn('(fn2-release-numeric-match-forms *fn2-release-numeric-bindings*)', text)

    def test_existing_hash_helper_moved_once_unchanged(self):
        r = json.loads(Path('tools/fixtures/release-member-binding-extraction.json').read_text())
        s = Path('books/release-member-binding.lisp').read_text()
        form = next(s[n.start:n.end] for n in lr.parse(s).forms
                    if s[n.start:n.end].startswith('(defun fn2-release-member-hash-p '))
        self.assertEqual(hashlib.sha256(form.encode()).hexdigest(), r['hash_helper_sha256'])
        recovery = Path('books/recovery-release.lisp').read_text()
        self.assertIn('(include-book "release-member-binding")', recovery)
        self.assertNotIn('(defun fn2-release-member-hash-p ', recovery)

    def test_actual_capacity_and_single_derived_group(self):
        r = json.loads(Path('tools/fixtures/allocation-release-capacity-extraction.json').read_text())
        s = Path('books/allocation-release-geometry.lisp').read_text()
        form = next(s[n.start:n.end] for n in lr.parse(s).forms
                    if s[n.start:n.end].startswith('(defun fn2-allocation-release-member-capacity '))
        self.assertEqual(hashlib.sha256(form.encode()).hexdigest(), r['original_sha256'])
        self.assertIn('(fn2-pool-class-for (fn2-allocation-release-member-capacity) fn2-pool)', s)
        configuration = Path('books/checkpoint-working-credit.lisp').read_text()
        self.assertIn('(fn2-allocation-release-credit-vector 0 fn2-pool)', configuration)
        self.assertIn('(equal commit-io-rows (* *fn2-commit-write-resources* commitrows))', configuration)
        self.assertEqual(configuration.count('(fn2-pool-credit-configure groups fn2-pool)'), 1)

if __name__ == '__main__':
    unittest.main()
