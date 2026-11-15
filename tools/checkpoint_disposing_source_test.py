"""Structural refusal controls over the actual candidate constructor class."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]
def function(src, name):
    return lr.match('(defun '+name+' ?*body)', lr.parse(src).forms)[0].node
def require(node, pattern):
    if not lr.match(pattern, [node]): raise ValueError(pattern)
def check_claim(src):
    require(function(src,'fn2-checkpoint-builder-claimp'),
      '(not (member-equal (fn2-checkpoints-state c fn2-checkpoints) (list *fn2-checkpoint-state-free* *fn2-checkpoint-state-disposing*)))')
def check_admission(src):
    f=function(src,'fn2-checkpoint-teardown-admission-ownerp')
    require(f,'(fn2-checkpoint-teardown-retained-ownerp ?*args)')
    require(f,'(not (= (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-disposing*))')
    require(f,'(= (fn2-checkpoint-teardown-debt-dispose-phase c fn2-checkpoint-teardown-debt) *fn2-checkpoint-dispose-phase-idle*)')
class Disposing(unittest.TestCase):
    def read(self,name): return (ROOT/'books'/name).read_text()
    def test_actual_claim_and_fresh_admission(self):
        check_claim(self.read('checkpoint.lisp'));check_admission(self.read('checkpoint-teardown-owner.lisp'))
        for filename, names in [('checkpoint-teardown.lisp',['fn2-checkpoint-teardown-inspect-children','fn2-checkpoint-teardown-submit']),('checkpoint-teardown-sweep.lisp',['fn2-checkpoint-teardown-select'])]:
            for name in names:
                f=function(self.read(filename),name)
                require(f,'(fn2-checkpoint-teardown-admission-ownerp ?*args)')
                self.assertFalse(lr.match('(fn2-checkpoint-teardown-retained-ownerp ?*args)',[f]))
    def test_generic_claim_reopening_refused(self):
        s=self.read('checkpoint.lisp').replace('*fn2-checkpoint-state-free* *fn2-checkpoint-state-disposing*','*fn2-checkpoint-state-free*')
        with self.assertRaises(ValueError): check_claim(s)
    def test_identity_cannot_authorize_disposal_admission(self):
        for clause in ['(not (= (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-disposing*))','(= (fn2-checkpoint-teardown-debt-dispose-phase c fn2-checkpoint-teardown-debt) *fn2-checkpoint-dispose-phase-idle*)']:
            s=self.read('checkpoint-teardown-owner.lisp').replace(clause,'t')
            with self.assertRaises(ValueError):check_admission(s)
    def test_existing_constructor_state_boundaries(self):
        # These are the actual shared admissions, rather than caller flags.
        cases=[('checkpoint.lisp','fn2-checkpoint-builder-ownerp','(equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-building*)'),
          ('checkpoint-source-retention.lisp','fn2-checkpoint-source-claim','(equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-building*)'),
          ('checkpoint-restore-provenance.lisp','fn2-checkpoint-restore-map-current-p','(equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-checked*)')]
        for filename,name,pattern in cases:require(function(self.read(filename),name),pattern)
        # Live authority and directory-rebase use explicit installed-state
        # policies; DISPOSING is not added to their accepted state lists.
        for filename in ['checkpoint-summary-authority-live.lisp','checkpoint-directory-rebase.lisp']:
            text=self.read(filename)
            self.assertIn('*fn2-checkpoint-state-installed*',text)
            self.assertNotIn('*fn2-checkpoint-state-disposing*',text)
if __name__=='__main__':unittest.main()
