"""Bounded actual source cursor/classifier controls; no ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def f(text,name):
    return next(t for s in forms(text) if isinstance((t:=read_sexp(s)),list) and t[:2]==['defun',name])
def nodes(x):
    if isinstance(x,list):
        yield x
        for y in x:yield from nodes(y)
class SourceCursor(unittest.TestCase):
    def test_real_current_generation_and_holders_before_exact_drop(self):
        s=(ROOT/'books/checkpoint-dispose-source.lisp').read_text()
        step=f(s,'fn2-checkpoint-dispose-source-step')
        names=[n[0] for n in nodes(step) if n and isinstance(n[0],str)]
        for name in ('fn2-checkpoint-dispose-current-p','fn2-checkpoint-dispose-environment-code',
                     'fn2-extents-obligation','fn2-alloc-edge-matchesp','fn2-extents-selectable-checkpoint'):
            self.assertIn(name,names)
        self.assertEqual(names.count('fn2-alloc-edge-drop'),1)
        self.assertLess(s.index('(fn2-checkpoint-dispose-environment-code'),s.index('(fn2-alloc-edge-drop'))
        self.assertNotIn('fn2-alloc-release',s);self.assertNotIn('fn2-alloc-retire',s)
    def test_only_actual_typed_source_classes_and_one_row_progress(self):
        s=(ROOT/'books/checkpoint-dispose-source.lisp').read_text()
        for name in ('fn2-checkpoint-owned-provenance-p','fn2-checkpoint-dispose-journal-source-p',
                     'fn2-checkpoint-payload-proof-p','fn2-checkpoint-dispose-cold-payload-p'):
            self.assertIn('('+name,s)
        self.assertIn('(dispose-phase *fn2-checkpoint-dispose-phase-cold*)',s)
        self.assertIn('(when (= e n))',s)
        self.assertIn('(+ e 1)',s)
        step=f(s,'fn2-checkpoint-dispose-source-step')
        self.assertEqual(sum(n and n[0]=='fn2-checkpoint-dispose-source-step' for n in nodes(step)),0)
    def test_journal_has_actual_installed_edge_not_owner_id_authority(self):
        s=(ROOT/'books/checkpoint-dispose-source.lisp').read_text()
        journal=f(s,'fn2-checkpoint-dispose-journal-source-p')
        self.assertIn(['+', '7', ['*','2','e']],list(nodes(journal)))
        self.assertIn('fn2-alloc-edge-matchesp',str(journal))
        self.assertIn(':installed-root',str(journal))
        self.assertIn('fn2-extents-installed-root',str(journal))
        self.assertNotIn('(posp commit-kind)',s)
    def test_phase_numbers_and_full_readonly_typed_domain(self):
        state=(ROOT/'books/checkpoint-teardown-state.lisp').read_text()
        self.assertIn('(:idle :sources :roots :refs :bytes :finish :cold)',state)
        s=(ROOT/'books/checkpoint-dispose-source.lisp').read_text()
        step=f(s,'fn2-checkpoint-dispose-source-step')
        tables=next(n[i+1] for n in nodes(step) if n and n[0]=='xargs'
                    for i,a in enumerate(n) if a==':stobjs')
        for table in tables:
            self.assertIn([table+'p',table],list(nodes(step)))
            self.assertIn([table+'-wfp',table],list(nodes(step)))
if __name__=='__main__':unittest.main()
