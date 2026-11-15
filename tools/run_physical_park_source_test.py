"""Exact canonical park-precondition extraction, not runtime qualification."""
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class ParkSource(unittest.TestCase):
 def setUp(self):
  self.source=(ROOT/'books/run-physical-release.lisp').read_text()
  self.saved=json.loads((ROOT/'tools/fixtures/run-physical-park/precondition.json').read_text())
 def test_exact_precondition(self):
  fn=lr.match('(defun fn2-run-load-parkable-p ?*body)',lr.parse(self.source).forms)[0].node
  body=fn.items[-1]
  self.assertEqual(self.source[body.start:body.end],self.saved['condition'])
 def test_only_named_predicate_substitution(self):
  fn=lr.match('(defun fn2-run-load-park-source ?*body)',lr.parse(self.source).forms)[0]
  call=lr.match('(fn2-run-load-parkable-p ?*args)',[fn.node])
  self.assertEqual(len(call),1)
  text=self.source[fn.start:fn.end]
  restored=lr.write(text,[(call[0].start-fn.start,call[0].end-fn.start,self.saved['condition'])])
  self.assertEqual(restored,self.saved['original_function'])
 def test_preflight_has_no_effects(self):
  fn=lr.match('(defun fn2-run-load-parkable-p ?*body)',lr.parse(self.source).forms)[0]
  text=self.source[fn.start:fn.end]
  for forbidden in ('-put ','-set-','fn2-checkpoint-summary-release','fn2-pool-release'):
   self.assertNotIn(forbidden,text)
  for required in ('fn2-run-load-ownerp','fn2-run-loads-pending','fn2-pool-workspace-code'):
   self.assertIn(required,text)
 def test_park_retains_windows_and_releases_before_reset(self):
  fn=lr.match('(defun fn2-run-load-park-source ?*body)',lr.parse(self.source).forms)[0]
  text=self.source[fn.start:fn.end]
  self.assertLess(text.index('(fn2-checkpoint-summary-release'),text.index('(fn2-run-cursors-put'))
  self.assertIn('(source *fn2-none*) (tag 0)',text)
  self.assertNotIn('(windows ',text)
  self.assertNotIn('fn2-pool-release',text)
if __name__=='__main__':unittest.main()
