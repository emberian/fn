"""Cold final-authority source joins, without Lisp evaluation/certification."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def check(text):
    forms=lr.parse(text).forms
    source=lr.match('(defun fn2-checkpoint-summary-authority-cold-source-p ?*body)', forms)[0].node
    for pattern in ['(fn2-checkpoint-selected-source-current-p ?*args)',
                    '(= (fn2-checkpoint-selected-source-phase 0 fn2-checkpoint-selected-source) *fn2-checkpoint-selected-source-phase-projected*)',
                    '(fn2-checkpoint-summary-current-p ?*args)',
                    '(= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)',
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
