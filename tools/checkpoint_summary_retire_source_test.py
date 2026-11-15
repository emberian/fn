"""Structural controls for physical retirement; no Lisp evaluation or proof claim."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]
def check_fence(text):
    fn = lr.match('(defun fn2-seal-release ?*body)', lr.parse(text).forms)[0].node
    checks = lr.match('((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) (mv :cache fn2-seals fn2-run-installed fn2-run-cache fn2-pool))', [fn])
    drops = lr.match('(fn2-run-cache-drop ?*args)', [fn])
    if len(checks) != 1 or not drops or checks[0].start >= drops[0].start:
        raise ValueError('physical fence must precede every resident cache drop')
def check_retire(text):
    forms=lr.parse(text).forms
    wrapper=lr.match('(defun fn2-checkpoint-summary-retire-row ?*body)',forms)[0].node
    if not lr.match('(fn2-checkpoint-summary-row-retire-row 0 r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-cbase-holds fn2-run-installed)',[wrapper]):raise ValueError('active retirement must call same row primitive')
    fn = lr.match('(defun fn2-checkpoint-summary-row-retire-row ?*body)', forms)[0].node
    for form in ['(fn2-checkpoint-cbase-row-promised-p s fn2-checkpoint-summary fn2-checkpoint-cbase-holds)',
                 '(fn2-checkpoint-summary-row-run-source-p s r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)',
                 '(= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*)',
                 '(member-equal (fn2-checkpoint-summary-phase s fn2-checkpoint-summary) (list *fn2-checkpoint-summary-phase-applied* *fn2-checkpoint-summary-phase-retiring*))']:
        if not lr.match(form, [fn]):
            raise ValueError('missing exact retirement gate: '+form)
    if lr.match('(fn2-run-cache-drop ?*args)', [fn]) or lr.match('(fn2-pool-release ?*args)', [fn]):
        raise ValueError('physical source is not resident cache ownership')
class Source(unittest.TestCase):
    def test_actual_sealer_fence(self):
        check_fence((ROOT/'books/sealer.lisp').read_text())
    def test_removed_fence_refused(self):
        source=(ROOT/'books/sealer.lisp').read_text().replace('(= (fn2-run-installed-physical r fn2-run-installed) 1)', 'nil')
        with self.assertRaises(ValueError): check_fence(source)
    def test_actual_retirement(self):
        check_retire((ROOT/'books/checkpoint-summary-retire.lisp').read_text())
    def test_missing_promise_gate_refused(self):
        source=(ROOT/'books/checkpoint-summary-retire.lisp').read_text().replace('(fn2-checkpoint-cbase-row-promised-p s fn2-checkpoint-summary fn2-checkpoint-cbase-holds)', 't')
        with self.assertRaises(ValueError): check_retire(source)
if __name__ == '__main__': unittest.main()
