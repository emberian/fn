"""Canonical holder coverage and structural carrier threading; source only."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import rewrite_checkpoint_dispose_holders as rw

class Holders(unittest.TestCase):
    def test_carrier_threading_class(self):
        text='(defun fn2-cdh-body (mode a) (declare (xargs :stobjs (a))) (mv :ok fn2-retirement-control))'
        out,n=rw.rewrite(text)
        self.assertEqual(n,3)
        self.assertEqual(rw.rewrite(out),(out,0))
        for file in ('books/checkpoint-dispose-holders.lisp','tests/checkpoint-dispose-holders-unit.lisp'):
            actual=(ROOT/file).read_text()
            self.assertEqual(rw.rewrite(actual),(actual,0))
    def test_real_archive_and_release_evidence_are_independent_vetoes(self):
        source=(ROOT/'books/checkpoint-dispose-holders.lisp').read_text()
        self.assertIn('(include-book "release-allocation-state")',source)
        self.assertNotIn('(include-book "release-allocation")',source)
        self.assertIn('(fn2-event-archive-candidate-held-p c checkpoint fn2-event-archive)',source)
        self.assertIn('(not (eq (fn2-release-evidence-candidate-state',source)
        self.assertIn('fn2-release-evidence-candidates) :clear))',source)
        machine=(ROOT/'books/machines-c.lisp').read_text()
        self.assertEqual(machine.count('(fn2-idc-child fn2-core-event-archive '),1)
        self.assertNotIn('event-archive-producer',machine)
    def test_refusal_controls_cover_nonserving_holders(self):
        fixture=(ROOT/'tests/checkpoint-dispose-holders-unit.lisp').read_text()
        for mode in ('archive-active','archive-pending','archive-uncertain','release-ledger','release-ledger-identity'):
            self.assertIn('(assert-event (fn2-cdh-test :'+mode+'))',fixture)

if __name__=='__main__':unittest.main()
