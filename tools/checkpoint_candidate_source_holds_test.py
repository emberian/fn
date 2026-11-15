from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def check(src):
 forms=lr.parse(src).forms
 fn=lr.match('(defun fn2-checkpoint-candidate-source-held-p ?*body)',forms)[0].node
 for head,stobj in [('fn2-checkpoint-catalog-source-held-p','fn2-checkpoint-summary'),('fn2-checkpoint-authority-source-held-p','fn2-checkpoint-summary-authority')]:
  for row in [0,1]:
   if not lr.match(f'({head} c {row} {stobj})',[fn]):raise ValueError('missing actual holder row')
 if not lr.match('(fn2-checkpoint-cbase-catalog-available-p c (fn2-checkpoint-cbase-holds-tag c fn2-checkpoint-cbase-holds) fn2-checkpoint-cbase-holds)',[fn]):raise ValueError('promise terminal must be derived')
class Holders(unittest.TestCase):
 def test_actual_all_holders(self):check((ROOT/'books/checkpoint-candidate-source-holds.lisp').read_text())
 def test_pending_omission_refused(self):
  s=(ROOT/'books/checkpoint-candidate-source-holds.lisp').read_text().replace('(fn2-checkpoint-catalog-source-held-p c 1 fn2-checkpoint-summary)','nil')
  with self.assertRaises(ValueError):check(s)
 def test_idle_and_retired_bytes_are_not_subjects(self):
  forms=lr.parse(ROOT/'books/checkpoint-candidate-source-holds.lisp').forms
  c=lr.match('(defun fn2-checkpoint-catalog-source-held-p ?*body)',forms)[0].node
  a=lr.match('(defun fn2-checkpoint-authority-source-held-p ?*body)',forms)[0].node
  self.assertTrue(lr.match('(list *fn2-checkpoint-summary-phase-idle* *fn2-checkpoint-summary-phase-retired*)',[c]))
  self.assertTrue(lr.match('(posp (fn2-checkpoint-summary-installed r fn2-checkpoint-summary))',[c]))
  self.assertTrue(lr.match('(posp (fn2-checkpoint-summary-lease-count r fn2-checkpoint-summary))',[c]))
  self.assertTrue(lr.match('*fn2-checkpoint-summary-authority-phase-idle*',[a]))
if __name__=='__main__':unittest.main()
