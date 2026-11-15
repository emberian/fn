"""Source/composition controls only; ACL2 execution is a separate gate."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def definition(source,name):
    matches=lr.match('(defun ?name ?*body)',lr.parse(source).forms,name=name)
    if len(matches)!=1: raise ValueError(name)
    return matches[0].node
def require(node,pattern):
    if not lr.match(pattern,[node]): raise ValueError(pattern)
def consume_contract(source):
    node=definition(source,'fn2-directory-rebase-consume')
    for p in [
      '(fn2-checkpoint-summary-authority-row-complete-p 1 ?*args)',
      '(= (fn2-directory-rebase-phase 0 fn2-directory-rebase) *fn2-directory-rebase-phase-source-scanned*)',
      '(= (fn2-alloc-freeze-phase fn2-extents) 2)',
      '(fn2-directory-rebase-seal-p 0 fn2-directory-rebase fn2-checkpoint-summary-authority)',
      '(= installation (fn2-commit-root-proposed 0 fn2-commit-root))',
      '(= (fn2-directory-rebase-suffix-scanned 0 fn2-directory-rebase) (- installation target))',
      '(fn2-commit-root-put 0 (base-batch target) ?*rest)',
      '(fn2-directory-rebase-transfer-bytes 0 fn2-checkpoint-summary-authority)',
      '(fn2-checkpoint-summary-authority-put 1 (phase *fn2-checkpoint-summary-authority-phase-idle*) ?*rest)',
    ]: require(node,p)
    # These carriers are read-only formals, absent from the return tuple, and no
    # source/lease/canonical-record reclamation operation is admitted here.
    for name in ['fn2-alloc-edge-drop','fn2-alloc-release','fn2-checkpoint-summary-retire']:
        if lr.match('('+name+' ?*args)',[node]): raise ValueError(name)
class Source(unittest.TestCase):
    def test_complete_subject_and_suffix(self):
        consume_contract((ROOT/'books/checkpoint-directory-consume.lisp').read_text())
    def test_incomplete_subject_refused(self):
        s=(ROOT/'books/checkpoint-directory-consume.lisp').read_text().replace('fn2-checkpoint-summary-authority-row-complete-p 1','fn2-checkpoint-summary-authority-row-current-p 1')
        with self.assertRaises(ValueError): consume_contract(s)
    def test_moving_installation_refused(self):
        s=(ROOT/'books/checkpoint-directory-consume.lisp').read_text().replace('(= installation (fn2-commit-root-proposed 0 fn2-commit-root))','t')
        with self.assertRaises(ValueError): consume_contract(s)
    def test_suffix_may_exceed_one(self):
        n=definition((ROOT/'books/checkpoint-directory-rebase.lisp').read_text(),'fn2-directory-rebase-step')
        require(n,'(<= batch (fn2-directory-rebase-installation 0 fn2-directory-rebase))')
        require(n,'(fn2-checkpoint-source-claimedp c ?*args)')
        require(n,'(if at-cut (fn2-directory-rebase-copy-seal ?*args) fn2-directory-rebase)')
        fixture=(ROOT/'tests/checkpoint-directory-consume-unit.lisp').read_text()
        self.assertIn('(installation-commit 3)',fixture)
        for mode in ['nil',':incomplete',':owner',':interleave',':hold',':seal']:
            self.assertIn('(assert-event (fn2-dcu-run '+mode+'))',fixture)
    def test_cold_constructor_remains_distinct(self):
        source=(ROOT/'books/checkpoint-directory-cold.lisp').read_text()
        n=definition(source,'fn2-directory-cold-source-p')
        require(n,'(fn2-checkpoint-summary-authority-cold-source-p ?*args)')
        require(n,'(fn2-checkpoint-summary-authority-row-complete-p 0 ?*args)')
        require(n,'(= (fn2-alloc-freeze-phase fn2-extents) 4)')
        install=definition(source,'fn2-directory-cold-install')
        require(install,'(fn2-directory-cold-source-p ?*args)')
        require(install,'(fn2-directory-cold-copy 0 seal ?*args)')
        require(install,'(fn2-commit-root-put 0 (base-batch cut) ?*args)')
        getter=definition(source,'fn2-directory-cold-base')
        require(getter,'(fn2-directory-cold-source-p ?*args)')
        require(getter,'(mv :selected ?*args (fn2-alloc-current-epoch fn2-extents))')
        require(getter,'(= (fn2-alloc-freeze-phase fn2-extents) 0)')
    def test_runtime_stays_inactive_until_composition(self):
        s=(ROOT/'books/checkpoint-master-state.lisp').read_text()
        self.assertIn('(defconst *fn2-checkpoint-activation-qualified* nil)',s)
if __name__=='__main__': unittest.main()
