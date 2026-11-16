#!/usr/bin/env python3
"""Source connections for bounded refusal work, not execution evidence."""
from pathlib import Path
import hashlib,subprocess,unittest
import lisp_rewrite as lr
from txn_ready_charge_rewrite import transform
R=Path(__file__).resolve().parents[1]
def form(text,pattern):
 m=lr.match(pattern,lr.parse(text).forms)
 assert len(m)==1
 return text[m[0].start:m[0].end]
class Xref(unittest.TestCase):
 def test_preflight_precedes_all_output_and_uses_staged_number(self):
  s=(R/'books/txn.lisp').read_text()
  x=form(s,'(defun fn2-txn-xref ?*body)')
  self.assertLess(x.index('fn2-txn-xref-size'),x.index('fn2-gram-put-chain'))
  self.assertIn('(equal (- ov-end ov-off) expected)',x)
  p=form(s,'(defun fn2-txn-xref-size ?*body)')
  for word in ['fn2-successor-out','*fn2-overview-entry-field-number*','fn2-gram-read','fn2-gram-pow10 20 number 1']:
   self.assertIn(word,p)
  self.assertNotIn('fn2-gram-put',p)
 def test_same_bounded_number_renderer(self):
  s=(R/'books/grammar.lisp').read_text()
  n=form(s,'(defun fn2-gram-put-number ?*body)')
  self.assertIn('(fn2-gram-put-digits 20 n (fn2-gram-pow10 20 n 1)',n)
  d=form((R/'books/txn.lisp').read_text(),'(defun fn2-txn-xref-digits ?*body)')
  self.assertIn('(or (zp left) (zp power))',d)
  self.assertIn('(fn2-gram-next-power power)',d)
 def test_charge_rewrite_reverses_exact_historical_ready_arm(self):
  s=(R/'books/txn.lisp').read_text()
  original=subprocess.check_output(['git','show','c7dbd223b83e72aeca5805897c0aa24e338a7f88:books/txn.lisp'],cwd=R,text=True)
  pattern='(:ready :on-refusal ?*body)'
  self.assertEqual(form(transform(s,inverse=True),pattern),form(original,pattern))
  self.assertEqual(transform(transform(s,inverse=True)),s)
 def test_fill_is_reference_binding_not_pool_copy(self):
  s=form((R/'books/machines-c-stage.lisp').read_text(),'(defun fn2-succ-fill-octets ?*body)')
  self.assertIn('(ref-slot slot)',s);self.assertIn('(ref-len len)',s)
  self.assertNotIn('fn2-pool-',s)
if __name__=='__main__':unittest.main()
