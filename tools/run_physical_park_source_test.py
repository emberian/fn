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
 def test_exact_summary_release_extraction(self):
  text=(ROOT/'books/checkpoint-summary-leases.lisp').read_text()
  parsed=lr.parse(text)
  helper=lr.match('(defun fn2-checkpoint-summary-releaseable-p ?*body)',parsed.forms)[0].node
  condition=helper.items[-1]
  self.assertEqual(text[condition.start:condition.end],self.saved['release_condition'])
  fn=lr.match('(defun fn2-checkpoint-summary-release ?*body)',parsed.forms)[0]
  call=lr.match('(fn2-checkpoint-summary-releaseable-p ?*args)',[fn.node])[0]
  actual=text[fn.start:fn.end]
  restored=lr.write(actual,[(call.start-fn.start,call.end-fn.start,self.saved['release_condition'])])
  self.assertEqual(restored,self.saved['release_original'])
 def test_region_preflight_precedes_first_mutation(self):
  text=(ROOT/'books/run-physical-park-region.lisp').read_text()
  parsed=lr.parse(text)
  check=lr.match('(defun fn2-run-load-region-park-check ?*body)',parsed.forms)[0]
  c=text[check.start:check.end]
  self.assertIn('fn2-run-load-parkable-p',c)
  self.assertIn('fn2-checkpoint-summary-releaseable-p',c)
  for mutation in ('-put ','-set-','(fn2-run-load-park-source '):self.assertNotIn(mutation,c)
  outer=lr.match('(defun fn2-run-load-region-park ?*body)',parsed.forms)[0]
  t=text[outer.start:outer.end]
  self.assertLess(t.index('(fn2-run-load-regionp'),t.index('(fn2-run-load-region-park-check'))
  self.assertLess(t.index('(<= count (fn2-checkpoint-summary-lease-count'),t.index('(fn2-run-load-region-park-apply'))
  self.assertIn('(mv :source fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)',t)
 def test_park_region_uses_single_canonical_operation(self):
  text=(ROOT/'books/run-physical-park-region.lisp').read_text()
  self.assertEqual(len(lr.match('(fn2-run-load-park-source ?*args)',lr.parse(text).forms)),1)
  self.assertNotIn('(fn2-checkpoint-summary-release ',text)
  self.assertNotIn('fn2-c-source-reader-release',text)
  self.assertNotIn('fn2-pool-release',text)
 def test_empty_jobs_invalidate_latent_physical_cursor(self):
  text=(ROOT/'books/run-physical-park-region.lisp').read_text()
  apply=lr.match('(defun fn2-run-load-region-park-apply ?*body)',lr.parse(text).forms)[0]
  t=text[apply.start:apply.end]
  self.assertIn('(fn2-run-cursors-put c (phase *fn2-run-cursor-phase-idle*) (physical 0))',t)
  self.assertLess(t.index('(< c (fn2-run-cursors-rows'),t.index('(fn2-run-cursors-put'))
if __name__=='__main__':unittest.main()
