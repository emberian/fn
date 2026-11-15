from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Terminal(unittest.TestCase):
 def test_exact_release_normalizes_after_last_refusal(self):
  s=(ROOT/'books/run-physical-release.lisp').read_text();s=s[:s.index('(fn2-run-load-frames fn2-run-load-release')]
  p=s.index('(kind 0) (owner 0) (generation 0)')
  self.assertLess(s.index('(fn2-checkpoint-summary-release c'),p)
  self.assertLess(s.rindex('((unless'),p)
  self.assertNotIn('((unless',s[p:])
 def test_only_accepted_unwind_normalizes(self):
  s=(ROOT/'books/run-physical-resources.lisp').read_text()
  self.assertIn("(if (member-eq release '(:ok :retired))\n                             (fn2-run-loads-put c (phase *fn2-run-load-phase-idle*) (windows 0) (tag 0)\n                              (kind 0) (owner 0) (generation 0)) fn2-run-loads)",s)
 def test_actual_consumer_requires_zero_owner_identity(self):
  s=(ROOT/'books/run-physical-readiness.lisp').read_text()
  for f in ['kind','owner','generation']:
   self.assertIn(f'(equal (fn2-run-loads-{f} c fn2-run-loads) 0)',s)
if __name__=='__main__':unittest.main()
