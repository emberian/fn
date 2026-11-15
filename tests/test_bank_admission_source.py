"""Prepublication provider source controls, not a served admission witness."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
TEXT=(ROOT/'books/checkpoint-bank-admission.lisp').read_text()
def body(name):
    ns=lr.match('(defun '+name+' ?*body)',lr.parse(TEXT).forms,deep=False)
    if len(ns)!=1:raise ValueError(name)
    n=ns[0].node;return TEXT[n.start:n.end]
class BankAdmission(unittest.TestCase):
    def test_exact_held_owner_and_catalog_binding(self):
        p=body('fn2-checkpoint-bank-admission-current-p')
        for s in ('fn2-csnapshot-ownerp token kind owner generation',
                  '*fn2-csnapshot-phase-held*','fn2-run-installed-bank-geometry-p',
                  'fn2-checkpoint-bank-admission-cut-commit',
                  'fn2-checkpoint-bank-admission-cut-event',
                  'fn2-checkpoint-bank-admission-active-phase',
                  'fn2-checkpoint-bank-admission-active-tag',
                  'fn2-checkpoint-bank-admission-active-bank',
                  'fn2-checkpoint-bank-admission-resident-limit',
                  'fn2-checkpoint-bank-admission-bank-capacity'):
            self.assertIn(s,p)
        n=lr.parse(p).forms[0].items[-1]
        self.assertNotIn('-wfp',p[n.start:n.end])

    def test_one_cell_scan_and_terminal_count(self):
        p=body('fn2-checkpoint-bank-admission-step')
        self.assertEqual(p.count('(fn2-run-installed-state r '),1)
        self.assertEqual(p.count('(fn2-run-installed-physical r '),1)
        self.assertIn('(= i capacity)',p)
        self.assertIn('0 (+ 1 i) fn2-checkpoint-bank-admission',p)
        self.assertIn('(mv :resources fn2-checkpoint-bank-admission)',p)
        self.assertNotIn('(fn2-checkpoint-bank-admission-step ',p[p.index(' (b* '):])

    def test_no_hidden_pool_or_durable_work(self):
        for name in ('begin','step'):
            p=body('fn2-checkpoint-bank-admission-'+name)
            for forbidden in ('fn2-pool-','fn2-storage-reserve','fn2-run-install',
                              'fn2-block-write','fn2-commit-publish',
                              '(phase *fn2-checkpoint-summary-phase-applied*)'):
                # Readonly run-installed accessors are expected, installers are not.
                if forbidden=='fn2-run-install':forbidden='(fn2-run-install '
                self.assertNotIn(forbidden,p)
            for m in lr.match('(mv ?*args)',lr.parse(p).forms,deep=True):
                self.assertEqual(getattr(m.node.items[-1],'low',''),'fn2-checkpoint-bank-admission')
                self.assertEqual(len(m.node.items),3)

    def test_same_token_does_not_restart_changed_catalog(self):
        p=body('fn2-checkpoint-bank-admission-begin')
        self.assertIn('(not (equal token (fn2-checkpoint-bank-admission-token',p)
        self.assertLess(p.index('(mv :state '),p.index('(fn2-checkpoint-bank-admission-put'))

if __name__=='__main__':unittest.main()
