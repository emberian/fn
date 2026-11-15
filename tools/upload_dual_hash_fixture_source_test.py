"""Actual primitive-call and missing-selector controls; not ACL2 execution."""
from pathlib import Path
import unittest
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]


class UploadDualFixture(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / 'tests/upload-dual-hash-unit.lisp').read_text()
        self.forms = lr.parse(self.text).forms

    def test_real_primitive_call_chain(self):
        for name in ('fn2-core-reserve', 'fn2-upload-hash-begin', 'fn2-upload-hash-step',
                     'fn2-upload-stored-hash', 'fn2-upload-block-hash', 'fn2-upload-block-cv',
                     'fn2-block-hash-into', 'fn2-upload-hash-end', 'fn2-upload-digest-store'):
            self.assertTrue(lr.match('(' + name + ' ?*args)', self.forms), name)
        self.assertEqual(len(lr.match('(fn2-upload-block-hash ?*args)', self.forms)), 2)
        self.assertEqual(len(lr.match('(fn2-upload-block-cv ?*args)', self.forms)), 2)
        self.assertIn('(equal short-got retained)', self.text)

    def test_actual_geometry_and_whole_guard(self):
        for name in ('fn2-b-upload-source-hash-row', 'fn2-b-upload-stored-hash-row',
                     'fn2-b-sealer-hash-row', 'fn2-b-ctl-runtime-row', 'fn2-b-block-read-row', 'fn2-core-wfp',
                     'fn2-pool-semanticp', 'fn2-pool-workspace-code'):
            self.assertTrue(lr.match('(' + name + ' ?*args)', self.forms), name)
        self.assertIn('(equal before (fn2-udh-snapshot scratch fn2-core))', self.text)
        for name in ('fn2-upload-put-core', 'fn2-commit-put-core', 'fn2-b3-put', 'fn2-extents-set-state'):
            self.assertFalse(lr.match('(' + name + ' ?*args)', self.forms), name)
        self.assertNotIn('*fn2-upload-page-source*', self.text)
        self.assertFalse(lr.match('(fn2-upload-save-source ?*args)', self.forms))

    def test_actual_specification_outputs_and_missing_hypotheses(self):
        self.assertTrue(lr.match('(fn-blake3 ?*args)', self.forms))
        self.assertTrue(lr.match('(fn-b3-node *fn2-b3-iv* block 4 0)', self.forms))
        for mode in ('nil', ':shared-stream', ':block-alias'):
            self.assertTrue(lr.match('(assert-event (fn2-udh-test ' + mode + '))', self.forms))
        self.assertIn('(equal selected (not alias))', self.text)
        self.assertIn('(equal original-ok (not alias))', self.text)
        self.assertIn('(equal stored-ok (not (eq alias :shared-stream)))', self.text)


if __name__ == '__main__':
    unittest.main()
