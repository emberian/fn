"""Actual early carrier and conservative candidate exclusion, source only."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class Holder(unittest.TestCase):
 def test_one_early_actual_child_without_producer_import(self):
  s=(ROOT/'books/machines-c.lisp').read_text();forms=lr.parse(s).forms
  self.assertEqual(len(lr.match('(fn2-idc-child fn2-core-event-archive fn2-event-archive (fn2-event-archive-init 2 fn2-event-archive) ?*rest)',forms,deep=False)),1)
  self.assertEqual(len(lr.match('(include-book "event-archive-state")',forms,deep=False)),1)
  self.assertNotIn('(include-book "event-archive-producer")',s)
  self.assertNotIn('(fn2-sealer-child fn2-core-event-archive',(ROOT/'books/event-archive-producer.lisp').read_text())
 def test_both_fixed_rows_without_readiness_or_cut_inference(self):
  s=(ROOT/'books/event-archive-state.lisp').read_text()
  f=lr.match('(defun fn2-event-archive-candidate-held-p ?*body)',lr.parse(s).forms,deep=False)[0].node
  body=s[f.start:f.end]
  for r in [0,1]:
   self.assertIn(f'(not (equal (fn2-event-archive-phase {r} fn2-event-archive) *fn2-event-archive-phase-idle*))',body)
   for field,v in [('candidate','c'),('checkpoint','checkpoint')]:self.assertIn(f'(equal (fn2-event-archive-{field} {r} fn2-event-archive) {v})',body)
  for x in ['source-tag','source-generation','cut-commit','cut-event','*fn2-event-archive-phase-complete*']:
   self.assertNotIn(x,body)
if __name__=='__main__':unittest.main()
