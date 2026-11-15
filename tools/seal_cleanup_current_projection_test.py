"""Frozen ROOT099 exact source contract; independent of the current cold schema."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import seal_cleanup_current_projection as p
ROOT=Path(__file__).resolve().parents[1]
class Current(unittest.TestCase):
 def setUp(self):self.before,self.schema,self.after=p.load_case('root')
 def fixture(self):return p.fixture_source(self.schema,label='ROOT099')
 def test_exact_current_projection(self):
  # Original full-book byte equality is retained against immutable800fa output.
  self.assertEqual(p.composed_project(self.before,self.schema),self.after)
 def test_current_fixture_is_canonical_projection(self):
  self.assertEqual(self.fixture(),(ROOT/'tools/fixtures/seal-release-held-root-after.lisp').read_text())
 def test_query_reference_field_is_in_full_snapshot(self):
  text=self.fixture();self.assertIn('(fn2-pool-query-ref-count i fn2-pool)',text)
  self.assertNotIn('fn2-seals-copy-live',text);self.assertNotIn('fn2-run-installed-version-floor',text)
 def test_no_pool_or_core_or_adoption_import(self):
  self.assertEqual(set(p.project(self.before,self.schema)),set(self.before))
  self.assertNotIn('books/pool.lisp',self.before)
  fixture=self.fixture();includes=lr.match('(include-book ?*args)',lr.parse(fixture).forms,deep=False)
  self.assertEqual(len(includes),3);self.assertNotIn('checkpoint-live-adoption',fixture)
 def test_current_actor_held_retries_credit_refuses(self):
  source=self.after['books/machines-c-sealer-events.lisp']
  self.assertTrue(lr.match('((:more :retired :done :held) (:charge ?*args))',lr.parse(source).forms))
  self.assertTrue(lr.match('(:otherwise (:do () (fn2-sealer-refuse code)) ?*rest)',lr.parse(source).forms))
 def test_cleanup_has_no_install_or_input_retirement(self):
  s=self.after['books/sealer.lisp']
  for name in ('fn2-seal-overlay-return','fn2-seal-hash-return'):
   n=p.one(f'(defun {name} ?*rest)',s)
   self.assertFalse(lr.match('(fn2-seal-install-run ?*rest)',[n]))
   self.assertFalse(lr.match('(fn2-seal-retire-runs ?*rest)',[n]))
 def test_fixture_holds_then_actual_lastclose_and_retry(self):
  s=self.fixture()
  for name in ('fn2-pool-query-acquire','fn2-pool-query-release','fn2-seal-release-row','fn2-seal-overlay-return','fn2-seal-hash-return'):
   self.assertTrue(lr.match(f'({name} ?*args)',lr.parse(s).forms),name)
  self.assertIn('(eq again :state)',s)
if __name__=='__main__':unittest.main()
