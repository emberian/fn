"""Actual full-base consumer joins. No ACL2 execution or persisted boot claim."""
from pathlib import Path
import sys, unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import lisp_rewrite as lr

def form(book, name):
    src=lr.parse(ROOT/'books'/book)
    hits=lr.match('_',src.forms,deep=True,head='defun',name=name)
    if len(hits)!=1: raise AssertionError(name)
    return src.text[hits[0].start:hits[0].end]

class Fullbase(unittest.TestCase):
    def test_actual_spawn_and_bounded_shared_index(self):
        init=form('recovery-machine.lisp','fn2-recovery-fullbase-index')
        for p in ['(= ogen (fn2-machine-generation id fn2-core))',
                  '(= (fn2-machine-rc-base id fn2-core) 0)',
                  '(= (fn2-machine-rc-base-tag id fn2-core) 0)',
                  '(fn2-alloc-identity-begin *fn2-recovery-machine-kind* id ogen ogen fn2-extents)',
                  '(fn2-alloc-identity-clear-step *fn2-recovery-machine-kind* id ogen ogen fn2-extents)']:
            self.assertIn(p, init)
        adopt=form('recovery-machine.lisp','fn2-recovery-adopt')
        self.assertIn('(fn2-alloc-identity-adopt-progress *fn2-recovery-machine-kind* id ogen ogen',adopt)
        self.assertIn('p *fn2-alloc-none* epoch allocation fn2-extents)',adopt)
        self.assertIn('(epoch (if known epoch 0)) (allocation (if known allocation p))',adopt)
        for forbidden in ['(fn2-alloc-adopt ', '(fn2-alloc-commit-allocation ', '(fn2-alloc-edge-add ',
                          '(fn2-alloc-identity-step ', '(fn2-alloc-identity-prepare-adopt ']:
            self.assertNotIn(forbidden,adopt)
        self.assertLess(adopt.index('(fn2-alloc-edges-state edge'),adopt.index('fn2-alloc-identity-adopt-progress'))
        self.assertLess(adopt.index('fn2-alloc-identity-adopt-progress'),adopt.index('fn2-alloc-commit-allocation-transition'))

    def test_more_does_not_advance_or_replay(self):
        src=lr.parse(ROOT/'books/recovery-machine.lisp')
        for arm in ['install-adopt','install-finish']:
            hits=lr.match('_',src.forms,deep=True,head=arm)
            self.assertEqual(len(hits),1)
            text=src.text[hits[0].start:hits[0].end]
            self.assertIn('((:more :active) (:charge :steps *fn2-work-advance* :runnable t))',text)
        finish=form('recovery-frontier.lisp','fn2-recovery-install-finish')
        self.assertIn('(fn2-recovery-fullbase-index id ogen fn2-core)',finish)
        self.assertIn('(fn2-alloc-identity-owner-p *fn2-recovery-machine-kind* id ogen ogen fn2-extents)',finish)
        self.assertIn('(= (fn2-alloc-identity-op fn2-extents) *fn2-alloc-identity-op-none*)',finish)
        self.assertNotIn('fn2-alloc-identity-end',finish)
        self.assertNotIn('fn2-recovery-finish ',finish)
        legacy=form('recovery-machine.lisp','fn2-recovery-finish')
        self.assertLess(legacy.index('(= (fn2-alloc-identity-active fn2-extents) 0)'),legacy.index('fn2-commit-root-set-installed'))

    def test_real_entry_controls_and_explicit_epoch_zero_collision(self):
        src=(ROOT/'tests/recovery-fullbase-index-unit.lisp').read_text()
        for mode in [':success',':duplicate',':zero-collision',':generation',':edge',':empty']:
            self.assertIn('(assert-event (fn2-rfiu-run '+mode+'))',src)
        self.assertIn('(fn2-recovery-install-adopt id gen fn2-core)',src)
        self.assertIn('(fn2-recovery-install-finish id fn2-core)',src)
        self.assertIn('(fn2-recovery-prepare id 0 0 fn2-core)',src)
        self.assertIn('(fn2-alloc-edge-add 8 23 0 7 9 :promised-read',src)
        self.assertIn('(fn2-alloc-identity-refines-p fn2-extents)',src)
        self.assertNotIn('(update-fn2-alloc-identity-active',src)

if __name__=='__main__': unittest.main()
