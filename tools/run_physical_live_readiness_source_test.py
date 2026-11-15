"""Persistent live capability vs cold startup/free-room source controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def body(source,name):
 found=lr.match('(defun '+name+' ?*body)',lr.parse(source).forms)
 assert len(found)==1,(name,len(found))
 m=found[0];return source[m.start:m.end]
class LiveReadiness(unittest.TestCase):
 def setUp(self):
  self.base=(ROOT/'books/run-physical-readiness.lisp').read_text()
  self.live=(ROOT/'books/run-physical-readiness-live.lisp').read_text()
  self.core=(ROOT/'books/run-physical-readiness-core.lisp').read_text()
 def test_live_constructor_derives_actual_writer_namespace(self):
  b=body(self.live,'fn2-run-load-readiness-live-begin')
  self.assertIn('fn2-c-source-writer-exclusive-p',b)
  for f in ('tag','generation','candidate','owner-kind','owner-slot','owner-gen','cut-commit','cut-event'):
   self.assertIn('(fn2-checkpoint-summary-'+f+' 1 fn2-checkpoint-summary)',b)
  self.assertLess(b.index('fn2-c-source-writer-exclusive-p'),b.index('fn2-run-load-readiness-begin-geometry'))
  self.assertNotIn('readiness-roomp',b)
  self.assertNotIn('fn2-pool-reserve',b)
  current=body(self.live,'fn2-run-load-readiness-live-current-p')
  self.assertIn('fn2-run-load-readiness-ownerp',current)
  self.assertIn('fn2-c-source-writer-exclusive-p',current)
  for cut in ('cut-commit','cut-event'):self.assertIn('fn2-run-load-readiness-'+cut,current)
 def test_cold_room_and_error_priority_preserved(self):
  b=body(self.base,'fn2-run-load-readiness-begin')
  self.assertLess(b.index('begin-geometry-p'),b.index('readiness-roomp'))
  self.assertLess(b.index('readiness-roomp'),b.index('(fn2-run-load-readiness-begin-geometry '))
  c=body(self.base,'fn2-run-load-readiness-complete-current-p')
  self.assertIn('*fn2-run-load-readiness-scope-cold*',c)
  self.assertIn('readiness-roomp',c)
  step=body(self.base,'fn2-run-load-readiness-step')
  self.assertIn('*fn2-run-load-readiness-scope-live*',step)
  self.assertIn('(mv :changed fn2-run-load-readiness)',step)
 def test_live_step_and_complete_do_not_wait_for_unused_bundle(self):
  step=body(self.base,'fn2-run-load-readiness-step-with-owner')
  self.assertIn('(and live (fn2-run-load-readiness-parked-row-p',step)
  self.assertIn('(if live (fn2-run-load-readiness-op-quiescent-p',step)
  self.assertIn('(and (not live) (not (fn2-run-load-readiness-roomp',step)
  complete=body(self.live,'fn2-run-load-readiness-live-complete-current-p')
  self.assertIn('fn2-run-load-readiness-live-current-p',complete)
  self.assertIn('fn2-run-load-readiness-complete-geometry-p',complete)
  self.assertNotIn('readiness-roomp',complete)
 def test_dead_routing_preserves_historical_receipt(self):
  q=body(self.base,'fn2-run-load-readiness-op-quiescent-p')
  self.assertIn('(equal (fn2-run-load-ops-live o fn2-run-load-ops) 0)',q)
  for f in ('generation','cursor'):self.assertNotIn('fn2-run-load-ops-'+f,q)
  cold=body(self.base,'fn2-run-load-readiness-op-row-p')
  for f in ('generation','cursor'):self.assertIn('fn2-run-load-ops-'+f,cold)
  h=(ROOT/'books/run-physical-harvest.lisp').read_text()
  self.assertIn('(fn2-run-load-ops-set-live opslot 0 fn2-run-load-ops)',h)
  self.assertNotIn('fn2-run-load-ops-set-generation',h)
  self.assertNotIn('fn2-run-load-ops-set-cursor',h)
  self.assertLess(h.index('(equal (fn2-run-load-ops-live'),h.index('(equal (fn2-run-load-ops-generation'))
 def test_actual_core_checks_writer_every_turn(self):
  s=body(self.core,'fn2-run-load-readiness-owned-step')
  self.assertLess(s.index('fn2-run-load-readiness-live-current-p'),s.index('fn2-run-load-readiness-step-with-owner'))
  self.assertIn('((unless current) (mv :changed fn2-core))',s)
  self.assertIn('fn2-core-c-source-control',s)
  self.assertIn('fn2-core-checkpoint-summary',s)
  self.assertNotIn('fn2-checkpoint-summary-set-phase',s)
if __name__=='__main__':unittest.main()
