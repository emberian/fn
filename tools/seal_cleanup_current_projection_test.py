"""Current072 donor source controls; no ACL2 or cache publication."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import seal_cleanup_current_projection as p
import seal_overlay_draining_rewrite as drain
ROOT=Path(__file__).resolve().parents[1]
class Current(unittest.TestCase):
 def test_exact_current_projection(self):
  for file,expected in p.project(p.BEFORE).items():self.assertEqual(drain.transform(file,expected),(ROOT/file).read_text(),file)
 def test_current_fixture_is_canonical_projection(self):
  self.assertEqual(p.fixture_source(),(ROOT/'tests/seal-release-row-held-unit.lisp').read_text())
 def test_query_reference_field_is_in_full_snapshot(self):
  text=p.fixture_source();self.assertIn('(fn2-pool-query-ref-count i fn2-pool)',text)
  self.assertNotIn('fn2-seals-copy-live',text);self.assertNotIn('fn2-run-installed-version-floor',text)
 def test_no_pool_or_core_or_adoption_import(self):
  self.assertEqual(set(p.project(p.BEFORE)),set(p.BEFORE))
  self.assertNotIn('books/pool.lisp',p.BEFORE)
  fixture=p.fixture_source();includes=lr.match('(include-book ?*args)',lr.parse(fixture).forms,deep=False)
  self.assertEqual(len(includes),3)
  self.assertNotIn('checkpoint-live-adoption',fixture)
 def test_current_actor_held_retries_credit_refuses(self):
  source=(ROOT/'books/machines-c-sealer-events.lisp').read_text()
  self.assertTrue(lr.match('((:more :retired :done :held) (:charge ?*args))',lr.parse(source).forms))
  self.assertTrue(lr.match('(:otherwise (:do () (fn2-sealer-refuse code)) ?*rest)',lr.parse(source).forms))
 def test_cleanup_has_no_install_or_input_retirement(self):
  s=(ROOT/'books/sealer.lisp').read_text()
  for name in ('fn2-seal-overlay-return','fn2-seal-hash-return'):
   n=p.one(f'(defun {name} ?*rest)',s)
   self.assertFalse(lr.match('(fn2-seal-install-run ?*rest)',[n]))
   self.assertFalse(lr.match('(fn2-seal-retire-runs ?*rest)',[n]))
 def test_fixture_holds_then_actual_lastclose_and_retry(self):
  s=p.fixture_source()
  for name in ('fn2-pool-query-acquire','fn2-pool-query-release','fn2-seal-release-row','fn2-seal-overlay-return','fn2-seal-hash-return'):
   self.assertTrue(lr.match(f'({name} ?*args)',lr.parse(s).forms),name)
  self.assertIn('(eq again :state)',s)
if __name__=='__main__':unittest.main()
