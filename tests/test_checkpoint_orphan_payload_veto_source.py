"""Actual metadata scan/submit class must veto authenticated payload use."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import rewrite_checkpoint_orphan_payload_veto as rw
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def definition(text,name):
    return next(n for f in forms(text) for n in walk(read_sexp(f)) if n[:2]==['defun',name])
def veto(text):
    eligible=definition(text,'fn2-checkpoint-owned-retirement-eligible-p')
    return ['not',['fn2-checkpoint-known-payload-use-p','e',*rw.TABLES,'fn2-extents']] in list(walk(eligible))
class PayloadVeto(unittest.TestCase):
    def test_actual_scan_and_submit_share_positive_use_veto(self):
        text=(ROOT/'books/checkpoint-owned-retirement.lisp').read_text()
        self.assertTrue(veto(text))
        self.assertFalse(veto(text.replace('(not (fn2-checkpoint-known-payload-use-p e '+ ' '.join(rw.TABLES)+' fn2-extents))','t',1)))
        for name in ('fn2-checkpoint-owned-retirement-scan','fn2-checkpoint-owned-retirement-submit-op'):
            self.assertIn('fn2-checkpoint-owned-retirement-eligible-p',str(definition(text,name)))
        cost=next(read_sexp(s) for s in forms(text) if read_sexp(s)[:2]==['defcost','fn2-checkpoint-owned-retirement-submit-op'])
        tables=cost[cost.index(':tables')+1]
        for table in rw.TABLES:self.assertIn('fn2-core-'+table[4:],tables)
    def test_structural_actual_abi_threading_and_idempotence(self):
        text='(defun fn2-checkpoint-owned-retirement-scan (kind cursor a) (declare (xargs :stobjs (a))) (fn2-checkpoint-owned-retirement-eligible-p kind cursor a))'
        out,n=rw.rewrite(text);self.assertEqual(n,3)
        self.assertEqual(rw.rewrite(out),(out,0))
        actual=(ROOT/'books/checkpoint-owned-retirement.lisp').read_text()
        self.assertEqual(rw.rewrite(actual),(actual,0))
    def test_cold_fact_checks_exact_handle_roles_and_current_authentication(self):
        text=(ROOT/'books/checkpoint-payload-use.lisp').read_text()
        cold=str(definition(text,'fn2-checkpoint-cold-payload-use-p'))
        for name in ('fn2-checkpoint-bank-closure-row-p','fn2-checkpoint-bank-closures-epoch',
                     'fn2-checkpoint-bank-closures-allocation','fn2-checkpoint-bank-closures-role-bits'):
            self.assertIn(name,cold)
        self.assertIn('fn2-checkpoint-payload-proof-p',text)
        self.assertIn('(< slot *fn2-checkpoint-anchor-slots*)',text)
        self.assertNotIn('(< slot 4)',text)
        self.assertNotIn('(fn2-alloc-edge-add',text);self.assertNotIn('(fn2-alloc-retire',text)
if __name__=='__main__':unittest.main()
