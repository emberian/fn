"""Actual payload-use producer source controls; no ACL2 execution."""
import sys
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
import rewrite_checkpoint_payload_proof as rw
from lisp_source import forms, read_sexp


def source(stem):
    return (ROOT / 'books' / (stem + '.lisp')).read_text()


class PayloadProofSource(unittest.TestCase):
    def test_structural_threading_and_idempotence(self):
        fixture = '''(defun fn2-checkpoint-payload-step (budget p)
 (declare (xargs :stobjs (p) :guard t)) (mv :ok p))
(defmacro fn2-checkpoint-payload-step-mv (code) `(mv ,code p))'''
        result, count = rw.rewrite(fixture, 'checkpoint-payload')
        self.assertEqual(count, 3)
        self.assertEqual(rw.rewrite(result, 'checkpoint-payload'), (result, 0))
        unrelated = '(defun unrelated (budget p) (mv :ok p))'
        self.assertEqual(rw.rewrite(unrelated, 'checkpoint-payload'), (unrelated, 0))
        for stem in ('checkpoint-payload-state', 'checkpoint-payload', 'checkpoint-metadata-driver'):
            self.assertEqual(rw.rewrite(source(stem), stem), (source(stem), 0))

    def test_guard_class_preserves_readonly_type(self):
        fixture = '(defun x (a b) (declare (xargs :stobjs (a b) :guard (and (a-wfp a) (b-wfp b)))) a)'
        out, n = rw.typed_guards(fixture)
        self.assertEqual(n, 2)
        self.assertIn('(ap a) (a-wfp a)', out)
        self.assertIn('(bp b) (b-wfp b)', out)
        self.assertEqual(rw.typed_guards(out), (out, 0))

    def test_actual_complete_is_delayed_until_bounded_use_retention(self):
        live = source('checkpoint-payload')
        self.assertNotIn('fn2-checkpoint-retained-entry-set-phase', live)
        self.assertIn('(if (eq code :complete) :more code)', live)
        self.assertEqual(live.count('(fn2-checkpoint-payload-proof-step '), 1)
        proof = source('checkpoint-payload-proof')
        self.assertIn('*fn2-checkpoint-payload-phase-complete*', proof)
        self.assertIn('(= (fn2-checkpoint-payload-position 0 fn2-checkpoint-payload) (fn2-checkpoint-payload-total', proof)
        self.assertIn('(proof-count (- count 1))', proof)
        self.assertIn('fn2-checkpoint-payload-proof-copy-hash 0 e got', proof)
        self.assertNotIn('fn2-alloc-retire', proof)
        self.assertNotIn('fn2-alloc-release', proof)

    def test_queue_derives_original_and_decoded_child_without_caller_handle(self):
        state = source('checkpoint-payload-state')
        table = source('checkpoint-payload-proof-state')
        self.assertIn('(child (equal phase *fn2-checkpoint-payload-phase-claim*))', state)
        self.assertIn('*fn2-format-source-manifest-entry-field-block-physical-unit*', state)
        self.assertIn('(fn2-checkpoint-payload-source-unit 0', state)
        self.assertIn('(pending-owner (fn2-extents-owner-id e fn2-extents))', state)
        self.assertNotIn('(posp (fn2-extents-owner-id', table)
        self.assertIn('(= (fn2-checkpoint-payload-proofs-allocation-owner e', table)
        self.assertIn('(proof-count 0)', state)

    def test_carrier_and_contract_class(self):
        carrier=source('checkpoint-payload-carrier')
        self.assertIn('(equal (fn2-checkpoint-payload-proof-count 0', carrier)
        resources=source('checkpoint-metadata-resources')
        self.assertEqual(resources.count('(defcorechild fn2-core-checkpoint-payload-proofs '),1)
        for stem in ('checkpoint-payload-state','checkpoint-payload','checkpoint-payload-proof'):
            text=source(stem)
            self.assertIn('(fn2-checkpoint-payload-proofsp fn2-checkpoint-payload-proofs)',text)
            self.assertIn('fn2-checkpoint-payload-proofs-hashes-length',text)
            lr.parse(text)


if __name__ == '__main__':
    unittest.main()
