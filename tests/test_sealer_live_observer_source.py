#!/usr/bin/env python3
"""Actual callback source boundaries; no execution/admission claim."""
import sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
def form(path,name):
 s=(ROOT/path).read_text();m=lr.match('(defun '+name+' ?*body)',lr.parse(s).forms,deep=True)
 if len(m)!=1:raise AssertionError(name)
 n=m[0].node;return s[n.start:n.end]
class SealerObserver(unittest.TestCase):
 def test_acquire_before_actual_lower_work(self):
  s=form('books/machines-c-sealer-events.lisp','fn2-sealer-step')
  self.assertLess(s.index('(fn2-sealer-source-acquire'),s.index('(fn2-sealer-work'))
  self.assertIn('(unless (eq code :ok))',s)
 def test_closing_blocks_only_new_receipt(self):
  s=form('books/machines-c-sealer-events.lisp','fn2-sealer-source-acquire')
  self.assertIn('(and (= receipt 0) (not (= (fn2-csnapshot-phase',s)
  self.assertIn('(fn2-c-source-reader-acquire endpoint receipt',s)
  self.assertIn('*fn2-csnapshot-phase-held*',s)
 def test_release_after_real_idle_and_exact_receipt(self):
  s=form('books/machines-c-sealer-events.lisp','fn2-sealer-source-release')
  self.assertLess(s.index('*fn2-seal-phase-idle*'),s.index('(fn2-c-source-reader-release'))
  self.assertIn('(= (fn2-seals-held 0 fn2-seals) 0)',s)
  self.assertIn('(fn2-c-source-reader-release endpoint receipt',s)
  self.assertIn('(if (eq code :ok) (fn2-seals-set-source-receipt 0 0',s)
 def test_real_retired_release_precedes_lower_idle(self):
  s=form('books/sealer.lisp','fn2-seal-release')
  self.assertIn('(fn2-seal-retired-row rows 0',s)
  self.assertIn('((unless (< r rows))',s)
  self.assertIn('(fn2-seal-release-row r',s)
 def test_final_poll_has_actual_quiescence_gate(self):
  s=(ROOT/'books/c-snapshot.lisp').read_text()
  self.assertIn('((not sealer-quiescent) (mv :more 0 0 fn2-csnapshot))',s)
  q=form('books/c-snapshot.lisp','fn2-csnapshot-sealer-quiescent-p')
  for x in ('*fn2-seal-phase-idle*','fn2-seals-held','fn2-seals-source-receipt','fn2-c-source-readers-live','fn2-sealer-snapshot-read-code'):self.assertIn(x,q)
 def test_closing_keeps_allocator_open(self):
  s=form('books/alloc.lisp','fn2-alloc-snapshot-prepare')
  self.assertNotIn('update-fn2-alloc-freeze-phase',s)
  self.assertIn('update-fn2-alloc-freeze-token',s)
  s=form('books/machines-c-sealer-events.lisp','fn2-sealer-work')
  self.assertNotIn('*fn2-csnapshot-phase-closing*',s)
 def test_actual_fixture_does_not_plant_observer_or_phase(self):
  s=(ROOT/'tests/sealer-source-quiescence-unit.lisp').read_text()
  for x in ('fn2-seals-set-phase','fn2-c-source-readers-put','fn2-c-source-control-put','fn2-csnapshot-put','fn2-machine-write-phase'):self.assertNotIn(x,s)
  for x in ('fn2-ov-write','fn2-ov-freeze','fn2-sealer-run','fn2-csnapshot-begin','fn2-csnapshot-poll','allocator-open'):self.assertIn(x,s)
 def test_wake_validates_actual_writer_generation(self):
  s=form('books/machines-c-sealer-events.lisp','fn2-sealer-source-wake-p')
  for x in ('fn2-machine-kind-read-code','fn2-machine-generation-read-code','*fn2-checkpoint-master-kind*','fn2-machine-generation target fn2-core) targetgen','fn2-c-source-control-writer-owner','fn2-c-source-control-writer-gen'):self.assertIn(x,s)
  self.assertIn('(fn2-sealer-source-wake-p target targetgen',form('books/machines-c-sealer-events.lisp','fn2-sealer-source-release'))
 def test_actual_wake_and_new_start_gate(self):
  s=(ROOT/'books/machines-c-sealer-events.lisp').read_text()
  self.assertIn('(:do (code target targetgen) (fn2-sealer-source-release)',s)
  self.assertIn('(:wake-row target)',s)
  self.assertIn('(fn2-sealer-source-startable-p fn2-core)',form('books/machines-c-sealer-events.lisp','fn2-sealer-ready'))
if __name__=='__main__':unittest.main()
