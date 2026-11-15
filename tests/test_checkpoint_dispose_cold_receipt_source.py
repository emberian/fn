"""Carried cold receipt scope controls, no ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def function(source,name):
    return next(t for s in forms(source) if isinstance((t:=read_sexp(s)),list) and t[:2]==['defun',name])
def nodes(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from nodes(y)
def receipt_ok(source):
    f=function(source,'fn2-checkpoint-dispose-cold-receipt-p')
    names={n[0] for n in nodes(f) if n and isinstance(n[0],str)}
    return set(('fn2-checkpoint-bank-protection-sources-p','fn2-checkpoint-bank-protection-cursor',
                'fn2-checkpoint-bank-protection-total','fn2-checkpoint-bank-protection-bound-mask',
                'fn2-checkpoint-bank-protection-edge-total','fn2-checkpoint-bank-protection-ops-rows',
                'fn2-checkpoint-bank-protection-candidate-rows','fn2-alloc-freeze-phase')).issubset(names)
class ColdReceipt(unittest.TestCase):
    def test_exact_carried_context_has_no_phase4_current_dependency(self):
        s=(ROOT/'books/checkpoint-dispose-cold-receipt.lisp').read_text()
        self.assertTrue(receipt_ok(s))
        for name in ('fn2-checkpoint-bank-protection-sources-p','fn2-checkpoint-bank-protection-edge-total',
                     'fn2-checkpoint-bank-protection-cursor','fn2-alloc-freeze-phase'):
            self.assertFalse(receipt_ok(s.replace(name,'removed-'+name)))
        self.assertNotIn('fn2-checkpoint-bank-protection-complete-p',s)
        self.assertNotIn('fn2-checkpoint-bank-protection-current-p',s)
    def test_ack_and_capture_identity_are_both_required(self):
        s=(ROOT/'books/checkpoint-dispose-cold-receipt.lisp').read_text()
        row=str(function(s,'fn2-checkpoint-dispose-cold-row-p'))
        for name in ('fn2-checkpoint-bank-obligation-state','fn2-checkpoint-dispose-cold-subject-p',
                     'fn2-checkpoint-bank-closure-row-p','fn2-alloc-handle-code'):
            self.assertIn(name,row)
        self.assertIn('(fn2-checkpoint-bank-cold-word slot',s)
        self.assertIn('(fn2-checkpoint-dispose-cold-words-p 0 slot c',s)
        self.assertNotIn('(defcost',s)
        self.assertNotIn('(fn2-alloc-edge-drop',s)
if __name__=='__main__':unittest.main()
