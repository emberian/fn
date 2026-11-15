"""Source/ABI controls for prepared nonempty DRAINING operation witnesses."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import seal_draining_fixture_emit as emit
ROOT=Path(__file__).resolve().parents[1]
def fn(source,name):return lr.match(f'(defun {name} ?*args)',lr.parse(source).forms,deep=False)[0].node
class Fixture(unittest.TestCase):
 def test_actual_carrier_emission_reproduces(self):
  self.assertEqual(emit.emit(),(ROOT/'tests/seal-draining-sources-unit.lisp').read_text())
 def test_nonempty_sources_are_real_build_and_insert(self):
  s=emit.emit();nodes=lr.parse(s).forms
  self.assertTrue(lr.match('(fn2-rga-call fn2-rga-build 3 *fn2-overview-entry* ?*args)',nodes))
  self.assertTrue(lr.match('(fn2-ov-insert o 0 128 ?*args)',nodes))
  self.assertTrue(lr.match('(= (fn2-overlays-count o fn2-overlays) 1)',nodes))
  self.assertTrue(lr.match('(fn2-dr8-call fn2-dr8-build-runs 4)',nodes))
  self.assertTrue(lr.match('(fn2-dr8-call fn2-dr8-overlays 4)',nodes))
 def test_source_limit_and_real_worker_not_fake_install(self):
  s=emit.emit();nodes=lr.parse(s).forms
  self.assertTrue(lr.match('(= (fn2-ranges-scount 0 fn2-ranges) 8)',nodes))
  self.assertTrue(lr.match('(= (fn2-ranges-scount 0 fn2-ranges) 4)',nodes))
  self.assertTrue(lr.match('(fn2-seal-step 4096 ?*args)',nodes))
  self.assertFalse(lr.match('(fn2-seals-put 0 (phase *fn2-seal-phase-install*) ?*args)',nodes))
  self.assertTrue(lr.match('(= (fn2-seals-k 0 fn2-seals) 4)',nodes))
  self.assertTrue(lr.match('(fn2-rd-refresh 0 ?*args)',nodes))
  self.assertTrue(lr.match('(fn2-dr8-call fn2-dr8-first 1000)',nodes))
 def test_actual_held_ref_cleanup_and_capacity_progress(self):
  nodes=lr.parse(emit.emit()).forms
  for name in ('fn2-pool-query-acquire','fn2-pool-query-release','fn2-seal-free-rows'):
   self.assertTrue(lr.match(f'({name} ?*args)',nodes))
  self.assertTrue(lr.match('(equal rest (fn2-dr8-entries 2 7))',nodes))
  self.assertTrue(lr.match('(eq held :held)',nodes))
  self.assertTrue(lr.match('(eq drained :idle)',nodes))
 def test_real_pinned_query_uses_existing_core_producer(self):
  s=(ROOT/'tests/seal-draining-pinned-read-unit.lisp').read_text();nodes=lr.parse(s).forms
  self.assertTrue(lr.match('(include-book "read-unit")',nodes,deep=False))
  for name in ('fn2-init-executor','fn2-cs-seed-all','fn2-read-range','fn2-read-next','fn2-read-value','fn2-read-octets','fn2-pool-query-acquire','fn2-pool-query-release','fn2-sealer-step'):
   self.assertTrue(lr.match(f'({name} ?*args)',nodes),name)
  self.assertFalse(lr.match('(fn2-seals-put ?*args)',nodes))
  self.assertFalse(lr.match('(fn2-overlays-set-phase ?*args)',nodes))
  self.assertTrue(lr.match('(eq value-code :stale)',nodes));self.assertTrue(lr.match('(eq octet-code :stale)',nodes))
  self.assertTrue(lr.match('(equal rest (cdr *fn2-rdu-three*))',nodes))
 def test_layout_disjointness_is_actual_declaration_derived(self):
  s=emit.emit();self.assertIn('*fn2-seal-field-rows*',s);self.assertIn('*fn2-run-reader-fields*',s)
  self.assertTrue(lr.match('(fn2-fields-init *fn2-dr8-fields* fn2-fields)',lr.parse(s).forms))
if __name__=='__main__':unittest.main()
