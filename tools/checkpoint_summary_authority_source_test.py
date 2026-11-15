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
