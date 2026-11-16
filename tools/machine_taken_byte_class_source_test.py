#!/usr/bin/env python3
"""Inverse receipt for the two-hunk taken-range generator extension."""
from pathlib import Path
import hashlib
import subprocess
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
BASE='0506c97c9'
OLD={
 'fn2-machine-taken-ranges-p':'d375b1ec5077baa2584f588c6225c4456c9c37b3f681c75d2e8d2fb5f0ea4c1c',
 'fn2-machine-taken-reserves':'1a2be228827aed9f36ef5287cea03934c9518336c5dc002ec032882afcc9ab59',
}
def form(text,name):
 ms=lr.match('(defun '+name+' ?*body)',lr.parse(text).forms)
 if len(ms)!=1:raise AssertionError(name)
 return text[ms[0].start:ms[0].end]
class TakenBytes(unittest.TestCase):
 def test_inverse_preserves_original_full_forms(self):
  original=subprocess.check_output(['git','show',BASE+':books/machines.lisp'],cwd=ROOT,text=True)
  current=(ROOT/'books/machines.lisp').read_text()
  for name,sha in OLD.items():
   before=form(original,name);after=form(current,name)
   self.assertEqual(hashlib.sha256(before.encode()).hexdigest(),sha)
   if name.endswith('ranges-p'):
    restored=after.replace('(fn2-machine-class-specp (fn2-arm-get :class (cdar specs)))',
                           '(natp (fn2-arm-get :class (cdar specs)))')
   else:
    a=lr.match('(fn2-core-reserve ?*args)',lr.parse(after).forms)
    b=lr.match('(fn2-core-reserve ?*args)',lr.parse(before).forms)
    self.assertEqual(len(a),1);self.assertEqual(len(b),1)
    restored=lr.write(after,[(a[0].start,a[0].end,before[b[0].start:b[0].end])])
    self.assertIn('(if (natp c) c',after)
    self.assertIn('registry in child form',after)
   self.assertEqual(restored,before,name)
 def test_existing_child_resolver_unchanged(self):
  before=subprocess.check_output(['git','show',BASE+':books/machine-arms.lisp'],cwd=ROOT,text=True)
  after=(ROOT/'books/machine-arms.lisp').read_text()
  self.assertEqual(form(before,'fn2-arms-registry-reserves'),form(after,'fn2-arms-registry-reserves'))
 def test_prepared_controls_use_actual_generators(self):
  p=lr.parse(ROOT/'tests/machine-taken-byte-class-unit.lisp')
  for name in ['fn2-machine-taken-ranges-p','fn2-machine-taken-reserves','fn2-arms-registry-reserves']:
   self.assertTrue(lr.match('('+name+' ?*args)',p.forms),name)
if __name__=='__main__':unittest.main()
