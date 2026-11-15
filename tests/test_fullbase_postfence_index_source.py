"""The full-base helper is an unwired source seam until the outer boot join uses it."""
from pathlib import Path
import sys, unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
NAME='fn2-boot-finalize-fullbase-index'
def body(source):
    parsed=lr.parse(source)
    hits=lr.match('_',parsed.forms,deep=True,head='defun',name=NAME)
    if len(hits)!=1:raise AssertionError(NAME)
    return source[hits[0].start:hits[0].end]
class FullbaseFence(unittest.TestCase):
    def setUp(self):self.src=(ROOT/'books/checkpoint-bank-boot.lisp').read_text()
    def check(self,source):
        text=body(source)
        for required in [
          '(= (fn2-machine-phase id fn2-core) *fn2-boot-state-epoch-result*)',
          '(= (fn2-machine-stage id fn2-core) 3)',
          '(= (fn2-machine-pending id fn2-core) 0)',
          '(= (fn2-machine-root-gen id fn2-core) 0)',
          '(= (fn2-machine-event-ready id fn2-core) 1)',
          '(= (fn2-machine-outcome id fn2-core) *fn2-outcome-done*)',
          '(= (fn2-machine-phase rid fn2-core) *fn2-recovery-machine-state-done*)',
          '(= (fn2-machine-stopped rid fn2-core) 1)',
          '(= (fn2-machine-pending rid fn2-core) 0)',
          '(= (fn2-machine-rc-base rid fn2-core) 0)',
          '(= (fn2-machine-rc-base-tag rid fn2-core) 0)',
          '(= (fn2-machine-rc-found rid fn2-core) (fn2-machine-rc-high rid fn2-core))',
          '(= (fn2-machine-rc-commit rid fn2-core) (fn2-machine-rc-chain rid fn2-core))',
          '(> epoch (fn2-machine-rc-epoch rid fn2-core))',
          '(> epoch (fn2-alloc-current-epoch fn2-extents))',
          '(= (fn2-alloc-epoch-begun fn2-extents) 0)',
          '(fn2-alloc-identity-owner-p *fn2-recovery-machine-kind* rid rgen rgen fn2-extents)',
          '(= (fn2-alloc-identity-phase fn2-extents) *fn2-alloc-identity-phase-idle*)',
          '(= (fn2-alloc-identity-op fn2-extents) *fn2-alloc-identity-op-none*)']:
            self.assertIn(required,text)
        self.assertLess(text.index('(fn2-alloc-identity-owner-p'),text.index('(fn2-alloc-identity-end'))
        self.assertLess(text.index('(fn2-alloc-identity-end'),text.index('(fn2-alloc-begin-epoch'))
        self.assertIn('((when (= active 0)) (fn2-boot-adopt-epoch epoch fn2-core))',text)
    def test_exact_actual_join_and_original_transition(self):self.check(self.src)
    def test_missing_fence_owner_terminal_and_epoch_refuse_source_gate(self):
        for old in ['(= (fn2-machine-outcome id fn2-core) *fn2-outcome-done*)',
                    '(fn2-alloc-identity-owner-p *fn2-recovery-machine-kind* rid rgen rgen fn2-extents)',
                    '(= (fn2-machine-rc-found rid fn2-core) (fn2-machine-rc-high rid fn2-core))',
                    '(> epoch (fn2-machine-rc-epoch rid fn2-core))']:
            with self.subTest(old=old),self.assertRaises(AssertionError):
                self.check(self.src.replace(old,'t',1))
if __name__=='__main__':unittest.main()
