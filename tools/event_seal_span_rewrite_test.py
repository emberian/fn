"""Replay actual dispatcher class; verify semantic span remains behind frame auth."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_seal_span_rewrite as rw
import event_archive_witness_rewrite as witness
ROOT=Path(__file__).resolve().parents[1]
def read(p): return (ROOT/p).read_text()
def matches(s,p): return lr.match(p,lr.parse(s).forms)
def node(s,p): return matches(s,p)[0].node
class SealSpan(unittest.TestCase):
 def test_dispatch_class_replay_idempotence_and_drift(self):
  for name,count in [('event-producer',2),('checkpoint-restore-events',1),('event-read-verified-unit',1)]:
   before=read('tools/fixtures/seal-span-before-'+name+'.lisp')
   after=rw.dispatch(before,count)
   after=witness.producer_gate(after) if name=='event-producer' else after
   path=('tests/' if name.endswith('-unit') else 'books/')+name+'.lisp'
   self.assertEqual(after,read(path));self.assertEqual(rw.dispatch(after,count),after)
   with self.assertRaises(ValueError):rw.dispatch(before,count+1)
 def test_state_class_replay_and_all_format_phases(self):
  after=witness.state(rw.state(read('tools/fixtures/seal-span-before-event-read-state.lisp')))
  self.assertEqual(after,read('books/event-read-state.lisp'));self.assertEqual(rw.state(after),after)
  f=node(after,'(defun fn2-event-read-format-phase-p ?*body)')
  for phase in ['frame-seal','seal-span','seal-tail','semantic-seal','frame-records']:
   self.assertIn('*fn2-event-read-phase-'+phase+'*',after[f.start:f.end])
 def test_shared_decoder_and_zero_tail_bound(self):
  s=read('books/event-read-verify.lisp');f=node(s,'(defun fn2-event-read-seal-span ?*body)')
  for p in ['(<= (+ off payload) *fn2-commit-unit-bytes*)',
            '(fn2-format-sealed-batch-decode base slot gen off (+ off payload) kind owner generation fn2-fields fn2-pool)',
            '(< off next)','(<= next (+ off payload))',
            '(<= (- next off) *fn2-format-sealed-batch-max-size*)',
            '(fn2-journal-zero-tail (- (+ off payload) next) next slot gen kind owner generation fn2-pool)']:
   self.assertTrue(lr.match(p,[f]),p)
  self.assertFalse(lr.match('(fn2-pool-write ?*args)',[f]))
 def test_actual_transition_preserves_source_subject(self):
  s=read('books/event-read-verify.lisp');f=node(s,'(defun fn2-event-read-format-core ?*body)')
  span=lr.match('(fn2-event-read-seal-span-step budget fn2-event-read fn2-fields fn2-pool)',[f])[0].node
  self.assertLess(span.start,lr.match('(fn2-format-run ?*args)',[f])[0].node.start)
  self.assertTrue(lr.match('(if semantic (fn2-event-read-body-len 0 fn2-event-read) 4096)',[f]))
  step=node(s,'(defun fn2-event-read-seal-span-step ?*body)')
  allowed={'phase','body-len','seal-span-started','seal-span-next','seal-span-length'}
  for put in lr.match('(fn2-event-read-put 0 ?*fields)',[step]):
   self.assertTrue({n.items[0].low for n in put.node.items[2:]} <= allowed)
  self.assertTrue(lr.match('(fn2-format-sealed-batch-start base fn2-fields)',[step]))
  self.assertTrue(lr.match('(fn2-format-sealed-batch-decode-step base slot gen off (+ off payload) kind owner generation budget fn2-fields fn2-pool)',[step]))
  self.assertTrue(lr.match('(count (min budget (- (+ off payload) next)))',[step]))
  self.assertTrue(lr.match('(fn2-journal-zero-tail count next slot gen kind owner generation fn2-pool)',[step]))
  self.assertTrue(lr.match('((when (zp budget)) (mv :more fn2-event-read fn2-fields))',[step]))
 def test_small_budget_fixture_progress_and_full_zero_snapshot(self):
  s=read('tests/event-read-seal-budget-unit.lisp')
  self.assertTrue(matches(s,'(fn2-event-read-format-core 0 ?*args)'))
  self.assertTrue(matches(s,'(equal before (fn2-esb-snapshot ?*args))'))
  self.assertTrue(matches(s,'(<= (- after-position position) budget)'))
  self.assertTrue(matches(s,'(fn2-esb-test 1)'));self.assertTrue(matches(s,'(fn2-esb-test 4096)'))
 def test_real_callers_yield_before_new_format_work(self):
  s=read('books/event-producer.lisp')
  gates=matches(s,'((and (not (posp budget)) (fn2-event-read-format-phase-p read-phase)) ?*body)')
  self.assertEqual(len(gates),1);self.assertTrue(lr.match('(mv :yield ?*args)',[gates[0].node]))
  self.assertLess(gates[0].node.start,node(s,'(fn2-event-read-format-step ?*args)').start)
  s=read('books/checkpoint-restore-events.lisp')
  f=node(s,'(defun fn2-checkpoint-restore-events-journal-step ?*body)')
  gate=lr.match('((when (zp budget)) ?*body)',[f])[0].node
  self.assertTrue(lr.match('(mv :yield ?*args)',[gate]))
  self.assertLess(gate.start,lr.match('(fn2-event-read-format-core ?*args)',[f])[0].node.start)
 def test_runnable_boundary_fixture_uses_actual_writer(self):
  s=read('tests/event-read-seal-span-unit.lisp')
  self.assertTrue(matches(s,'(fn2-commit-pack :seal ?*args)'))
  self.assertEqual(len(matches(s,'(fn2-event-read-seal-span ?*args)')),3)
  self.assertTrue(matches(s,'(eq malformed :format)'));self.assertTrue(matches(s,'(eq padding :padding)'))
  self.assertTrue(matches(s,'(fn2-pool-write slot gen end 1 7 0 1 fn2-pool)'))
if __name__=='__main__':unittest.main()
