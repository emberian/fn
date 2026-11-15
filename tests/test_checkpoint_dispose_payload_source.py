"""Exact CP withdrawal gate controls; source only, not ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def definition(text,name):
    return next(t for x in forms(text) if isinstance((t:=read_sexp(x)),list) and t[:2]==['defun',name])
def nodes(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from nodes(y)

def gate(text):
    f=definition(text,'fn2-checkpoint-dispose-payload-source-code')
    calls=list(nodes(f))
    return all(any(n and n[0]==name for n in calls) for name in (
        'fn2-checkpoint-teardown-retained-ownerp', 'fn2-checkpoint-teardown-retained-bank-excludedp',
        'fn2-checkpoint-dispose-held-p','fn2-checkpoint-payload-proof-p','fn2-alloc-edge-matchesp',
        'fn2-checkpoint-teardown-debt-generation','fn2-extents-obligation','fn2-alloc-freeze-phase')) and all(term in str(f) for term in (
        'fn2-checkpoint-state-disposing','fn2-checkpoint-dispose-phase-sources'))

class ExactWithdrawal(unittest.TestCase):
    def test_whole_gate_and_removed_generation_obligation_controls(self):
        source=(ROOT/'books/checkpoint-dispose-payload.lisp').read_text()
        self.assertTrue(gate(source))
        for name in ('fn2-checkpoint-teardown-debt-generation','fn2-extents-obligation',
                     'fn2-checkpoint-payload-proof-p','fn2-checkpoint-dispose-held-p'):
            self.assertFalse(gate(source.replace(name,'removed-'+name)))
    def test_only_mutation_is_exact_shared_edge_drop(self):
        source=(ROOT/'books/checkpoint-dispose-payload.lisp').read_text()
        f=definition(source,'fn2-checkpoint-dispose-payload-source-withdraw')
        drops=[n for n in nodes(f) if n and n[0]=='fn2-alloc-edge-drop']
        self.assertEqual(len(drops),1)
        self.assertEqual(drops[0][-3:],[':selectable-checkpoint','fn2-extents','fn2-alloc-edges'])
        self.assertEqual(drops[0][1][0],'fn2-checkpoint-source-edge')
        self.assertNotIn('fn2-alloc-retire',str(f));self.assertNotIn('fn2-alloc-release',str(f))
        self.assertNotIn('(defcost',source)
    def test_actual_begin_closes_admissions_before_withdrawal(self):
        source=(ROOT/'books/checkpoint-dispose-owner.lisp').read_text()
        begin=definition(source,'fn2-checkpoint-dispose-begin')
        self.assertIn('fn2-checkpoint-teardown-retained-ownerp',str(begin))
        self.assertIn('fn2-checkpoint-dispose-environment-code',str(begin))
        self.assertIn('*fn2-checkpoint-state-disposing*',str(begin))
        self.assertNotIn('fn2-alloc-edge-drop',str(begin))
        current=definition(source,'fn2-checkpoint-dispose-current-p')
        self.assertIn('fn2-checkpoint-teardown-debt-generation',str(current))
        self.assertIn('fn2-checkpoint-teardown-retained-hash-p',str(current))
        self.assertIn('*fn2-checkpoint-dispose-phase-bytes*',str(current))
        fixture=(ROOT/'tests/checkpoint-dispose-payload-unit.lisp').read_text()
        self.assertIn('(fn2-checkpoint-dispose-begin 1 41 0 3 2',fixture)
        self.assertNotIn('(state *fn2-checkpoint-state-disposing*)',fixture)

    def test_fixture_has_full_schema_frames_and_all_required_modes(self):
        fixture=(ROOT/'tests/checkpoint-dispose-payload-unit.lisp').read_text()
        for mode in ('live','deleted','foreign-query','event-zero','own-query','stale-generation',
                     'stale-handle','unbound-evidence','uncertain'):
            self.assertIn('(assert-event (fn2-cdp-test :'+mode+'))',fixture)
        self.assertIn('readonly-frame',fixture)
        self.assertIn('(equal actual primitive)',fixture)
        self.assertIn('(eq (caddr unguarded) :ok)',fixture)
        self.assertIn('(= (fn2-extents-selectable-checkpoint re fn2-extents) 6)',fixture)

if __name__=='__main__':unittest.main()
