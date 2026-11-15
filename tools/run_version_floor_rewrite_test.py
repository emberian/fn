"""Shared version-floor source identity and actual operation fixture controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import run_version_floor_rewrite as rw
R=Path(__file__).resolve().parents[1]
def canon(n):return n.low if hasattr(n,'low') else tuple(canon(x) for x in n.items)
class Floor(unittest.TestCase):
 def test_actual_class_from_fixed_original(self):
  expected=lr.parse(rw.rewrite((R/'tools/fixtures/run-version-floor-before.lisp').read_text())).forms
  actual=lr.parse(R/'books/runs.lisp').forms
  for f in expected:
   name=f.items[1].low;head=f.items[0].low
   n=lr.match(f'({head} {name} ?*body)',actual,deep=False)[0].node
   self.assertEqual(canon(f),canon(n))
 def test_all_actual_live_installers_above_floor(self):
  actual=lr.parse(R/'books/runs.lisp').forms
  for name in ['fn2-run-install','fn2-run-install-physical']:
   f=lr.match(f'(defun {name} ?*body)',actual)[0].node
   self.assertTrue(lr.match('(< (fn2-run-installed-version-floor fn2-run-installed) run)',[f]))
  live=[]
  for p in (R/'books').glob('*.lisp'):
   fs=lr.parse(p).forms
   if lr.match('(fn2-run-installed-put ?r (state *fn2-run-installed-state-live*) ?*args)',fs):live.append(p.name)
  self.assertEqual(live,['runs.lisp'])
 def test_floor_nonwrapping_before_mutation(self):
  forms=lr.parse(R/'books/runs.lisp').forms
  f=lr.match('(defun fn2-run-version-floor-advance ?*body)',forms)[0].node
  self.assertTrue(lr.match('(and (unsigned-byte-p 60 next) (< (fn2-run-installed-version-floor fn2-run-installed) next))',[f]))
  self.assertTrue(lr.match('(mv :bounds fn2-run-installed)',[f]))
 def test_actual_empty_run_and_refusal_fixture(self):
  forms=lr.parse(R/'tests/run-version-floor-unit.lisp').forms
  for pat in ['(fn2-run-install-physical 0 2 5 1 0 0 ?*args)','(fn2-run-version-floor-advance 6 fn2-run-installed)','(fn2-run-retire 0 fn2-run-installed)','(fn2-run-free-physical 0 fn2-run-installed)','(eq refused :bounds)','(= after 6)']:
   self.assertTrue(lr.match(pat,forms),pat)
if __name__=='__main__':unittest.main()
