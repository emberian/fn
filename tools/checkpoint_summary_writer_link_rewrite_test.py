"""Actual writer request relation and late-type materialization controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_summary_writer_link_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
class Link(unittest.TestCase):
    def test_actual_class_reproduces_from_fixed_original(self):
        before=(ROOT/'tools/fixtures/checkpoint-summary-live-writer-before.lisp').read_text()
        actual=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text()
        self.assertEqual(actual,rw.rewrite(before))
    def test_hash_helper_has_no_unbound_stobj_guards(self):
        forms=lr.parse(ROOT/'books/checkpoint-summary-authority-live.lisp').forms
        fn=lr.match('(defun fn2-checkpoint-summary-live-published-hash-p ?*body)',forms)[0].node
        for carrier in ['fn2-checkpoint-writer','fn2-machines','fn2-checkpoint-lifecycle']:
            self.assertFalse(lr.match(f'({carrier}-wfp {carrier})',[fn]))
    def test_actual_request_not_wrong_direct_owner(self):
        forms=lr.parse(ROOT/'books/checkpoint-summary-authority-live.lisp').forms
        fn=lr.match('(defun fn2-checkpoint-summary-authority-live-source-p ?*body)',forms)[0].node
        self.assertTrue(lr.match('(fn2-event-producer-writer-request-p ?*args)',[fn]))
        for field in ['owner-kind','owner-slot','owner-gen']:
            self.assertFalse(lr.match(f'(= (fn2-checkpoint-publication-{field} 0 fn2-checkpoint-publication) (fn2-checkpoint-source-{field} 0 fn2-checkpoint-source))',[fn]))
    def test_materializes_after_actual_writer_and_request_helper(self):
        forms=lr.parse(ROOT/'books/assembly-callbacks-c.lisp').forms
        names=[x.items[0].low for x in forms if hasattr(x,'items') and x.items and hasattr(x.items[0],'low')]
        order=['fn2-checkpoint-writer-events','fn2-event-producer-rearm-events','fn2-checkpoint-summary-authority-live-events','fn2-checkpoint-master-events']
        self.assertEqual([x for x in names if x in order],order)
    def test_old_wrong_owner_guard_is_real_counterexample(self):
        # Actual producer relation forces physical writer TARGET distinct from
        # requester SLOT and publication.owner-slot=TARGET. The old equality
        # instead forced publication.owner-slot=requester, contradicting it.
        helper=lr.match('(defun fn2-event-producer-writer-request-p ?*body)',lr.parse(ROOT/'books/event-rearm.lisp').forms)[0].node
        self.assertTrue(lr.match('(not (equal target slot))',[helper]))
        self.assertTrue(lr.match('(equal (fn2-checkpoint-publication-owner-slot 0 fn2-checkpoint-publication) target)',[helper]))
        source=(ROOT/'tools/fixtures/checkpoint-summary-live-writer-before.lisp').read_text()
        self.assertIn('(= (fn2-checkpoint-publication-owner-slot 0 fn2-checkpoint-publication) (fn2-checkpoint-source-owner-slot 0 fn2-checkpoint-source))',source)
        with self.assertRaises(ValueError):rw.rewrite(rw.rewrite(source))
if __name__=='__main__':unittest.main()
