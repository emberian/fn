"""Cold final-authority source joins, without Lisp evaluation/certification."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def check(text):
    forms=lr.parse(text).forms
    source=lr.match('(defun fn2-checkpoint-summary-adoption-source-p ?*body)', forms)[0].node
    final=lr.match('(defun fn2-checkpoint-summary-authority-cold-source-p ?*body)', forms)[0].node
    if not lr.match('(fn2-checkpoint-summary-adoption-source-p ?*args)',[final]) or not lr.match('(= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)',[final]):
        raise ValueError('final authority requires actual adopted C base')
    for pattern in ['(fn2-checkpoint-selected-source-current-p ?*args)',
                    '(= (fn2-checkpoint-selected-source-phase 0 fn2-checkpoint-selected-source) *fn2-checkpoint-selected-source-phase-projected*)',
                    '(fn2-checkpoint-summary-current-p ?*args)',
                    '(fn2-checkpoint-cbase-held-p fn2-checkpoint-summary fn2-checkpoint-cbase-holds)',
                    '(fn2-checkpoint-restore-events-complete-p ?*args)']:
        if not lr.match(pattern,[source]): raise ValueError('missing final authority join '+pattern)
    step=lr.match('(defun fn2-checkpoint-summary-authority-cold-step ?*body)',forms)[0].node
    for pattern in ['(fn2-checkpoint-summary-authority-cold-source-p ?*args)',
                    '(fn2-checkpoint-summary-authority-current-p ?*args)',
                    '(fn2-checkpoint-restore-events-frontier-word (floor i 8) (mod i 8) ?*args)',
                    '(fn2-checkpoint-restore-events-cut-seal-word (- i 480) ?*args)',
                    '(if (= i 487) *fn2-checkpoint-summary-authority-phase-complete* *fn2-checkpoint-summary-authority-phase-copy*)']:
        if not lr.match(pattern,[step]): raise ValueError('missing actual bounded copy '+pattern)
def check_live(text):
    forms=lr.parse(text).forms
    source=lr.match('(defun fn2-checkpoint-summary-authority-live-source-p ?*body)',forms)[0].node
    for pattern in ['(fn2-checkpoint-source-ownerp ?*args)',
                    '(= (fn2-checkpoint-source-phase 0 fn2-checkpoint-source) *fn2-checkpoint-source-phase-done*)',
                    '(= (fn2-checkpoint-source-rank 0 fn2-checkpoint-source) (fn2-checkpoint-metadata-manifest-entries 0 fn2-checkpoint-metadata-manifest))',
                    '(fn2-event-producer-donep ?*args)',
                    '(= (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication) *fn2-checkpoint-publication-phase-complete*)',
                    '(fn2-checkpoint-summary-live-published-hash-p ?*args)',
                    '(= (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-installed*)',
                    '(fn2-checkpoint-lifecycle-ownerp ?*args)',
                    '(= (fn2-checkpoint-lifecycle-phase 0 fn2-checkpoint-lifecycle) *fn2-checkpoint-lifecycle-phase-publication*)']:
        if not lr.match(pattern,[source]): raise ValueError('missing actual live source '+pattern)
    step=lr.match('(defun fn2-checkpoint-summary-authority-live-step ?*body)',forms)[0].node
    for pattern in ['(fn2-checkpoint-summary-authority-live-source-p ?*args)',
                    '(fn2-commit-directory-seal-slot (fn2-checkpoint-summary-authority-cut-commit 1 fn2-checkpoint-summary-authority) (fn2-fc-rows fn2-fc) fn2-commit-root)',
                    '(logbitp (floor i 8) (fn2-mk-size row fn2-mk))']:
        if not lr.match(pattern,[step]): raise ValueError('missing live continuation source '+pattern)
class Source(unittest.TestCase):
    def test_actual_adoption_preflight(self):
        source=lr.parse((ROOT/'books/checkpoint-summary-adoption.lisp').read_text()).forms
        fn=lr.match('(defun fn2-checkpoint-summary-apply-preflight ?*body)',source)[0].node
        for pattern in ['(fn2-checkpoint-summary-adoption-source-p ?*args)',
                        '(= (fn2-alloc-freeze-phase fn2-extents) 4)',
                        '(= (fn2-alloc-freeze-token fn2-extents) (fn2-checkpoint-selected-source-tag 0 fn2-checkpoint-selected-source))',
                        '(= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*)',
                        '(mv :occupied fn2-checkpoint-summary)',
                        '(fn2-checkpoint-summary-put 0 (application-stage 2) (cursor 0))']:
            self.assertTrue(lr.match(pattern,[fn]),pattern)
        for pattern in ['(fn2-run-installed-put ?*args)','(fn2-overlays-put ?*args)','(fn2-pool-release ?*args)']:
            self.assertFalse(lr.match(pattern,[fn]),pattern)
    def test_copy_requires_completed_preflight(self):
        forms=lr.parse((ROOT/'books/checkpoint-summary-apply.lisp').read_text()).forms
        fn=lr.match('(defun fn2-checkpoint-summary-apply-step ?*body)',forms)[0].node
        self.assertTrue(lr.match('(= (fn2-checkpoint-summary-application-stage 0 fn2-checkpoint-summary) 2)',[fn]))
    def test_actual_live_source(self): check_live((ROOT/'books/checkpoint-summary-authority-live.lisp').read_text())
    def test_live_requires_persisted_publication(self):
        source=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text().replace('*fn2-checkpoint-publication-phase-complete*','*fn2-checkpoint-publication-phase-fence*')
        with self.assertRaises(ValueError): check_live(source)
    def test_live_requires_mapped_seal(self):
        source=(ROOT/'books/checkpoint-summary-authority-live.lisp').read_text().replace('fn2-commit-directory-seal-slot','fn2-digest-slot')
        with self.assertRaises(ValueError): check_live(source)
    def test_master_retains_sources_through_pending_authority(self):
        decl=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse((ROOT/'books/checkpoint-master-state.lisp').read_text()).forms)[0].node
        props={decl.items[i].low:decl.items[i+1] for i in range(2,len(decl.items),2)}
        states=[x.low for x in props[':states'].items]
        self.assertEqual(states,[x.items[0].low for x in props[':arms'].items])
        holds={x.items[0].low:[y.low for y in x.items[1:]] for x in props[':holds'].items}
        for name in [':summary-authority-begin',':summary-authority-copy',':rebase-begin',':rebase-source',':rebase-consume',':rebase-archive']:
            self.assertEqual(holds[name],[':storage-window',':storage-window'])
        actual=lr.match('(defmachine-arms fn2-checkpoint-master ?*body)',lr.parse((ROOT/'books/checkpoint-master-arms.lisp').read_text()).forms)[0].node
        arms=next(actual.items[i+1] for i,x in enumerate(actual.items) if getattr(x,'low',None)==':arms')
        self.assertEqual(states,[x.items[0].low for x in arms.items])
        wait=next(x for x in arms.items if x.items[0].low==':publish-wait')
        self.assertTrue(lr.match('(:next :summary-authority-begin)',[wait]))
        copy=next(x for x in arms.items if x.items[0].low==':summary-authority-copy')
        self.assertTrue(lr.match('((:complete) (:next :rebase-begin) ?*rest)',[copy]))
        consume=next(x for x in arms.items if x.items[0].low==':rebase-consume')
        self.assertTrue(lr.match('(:do (code) (fn2-checkpoint-directory-rebase-consume-op ?*args) :accept (:committed))',[consume]))
        self.assertTrue(lr.match('(:next :release)',[consume]))
    def test_actual_join(self): check((ROOT/'books/checkpoint-summary-authority-cold.lisp').read_text())
    def test_no_preprojection_authority(self):
        s=(ROOT/'books/checkpoint-summary-authority-cold.lisp').read_text().replace('*fn2-checkpoint-selected-source-phase-projected*','*fn2-checkpoint-selected-source-phase-validated*')
        with self.assertRaises(ValueError): check(s)
    def test_no_unheld_authority(self):
        s=(ROOT/'books/checkpoint-summary-authority-cold.lisp').read_text().replace('(fn2-checkpoint-cbase-held-p fn2-checkpoint-summary fn2-checkpoint-cbase-holds)','t')
        with self.assertRaises(ValueError): check(s)
    def test_no_descriptor_as_physical_seal(self):
        s=(ROOT/'books/checkpoint-summary-authority-cold.lisp').read_text().replace('fn2-checkpoint-restore-events-cut-seal-word','fn2-checkpoint-summary-authority-descriptor-p')
        with self.assertRaises(ValueError): check(s)
if __name__=='__main__': unittest.main()
