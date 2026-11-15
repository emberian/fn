#!/usr/bin/env python3
"""Trace codec admission and exact charges through actual scheduler geometry."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/'books'/p).read_text()
def node(p,head,name):return lr.match('('+head+' '+name+' ?*body)',lr.parse(read(p)).forms,deep=False)[0].node
def raw(p,n):return read(p)[n.start:n.end]
class ArchiveBudget(unittest.TestCase):
 def test_restart_interval_is_shared_and_envelope_is_page_derived(self):
  self.assertIn('(defconst *fn2-run-restart-interval* *fn2-format-run-restart-interval*)',read('runs-page.lisp'))
  self.assertIn('(defconst *fn2-format-run-restart-interval* 16)',read('format-base.lisp'))
  n=node('checkpoint-geometry.lisp','defconst','*fn2-checkpoint-semantic-visit-bytes*')
  self.assertIn('(* (+ *fn2-format-run-restart-interval* 2) *fn2-format-page-size*)',raw('checkpoint-geometry.lisp',n))
 def test_actual_schema_bounds_remain_asserted(self):
  s=read('checkpoint-restore-semantic-work.lisp')
  self.assertIn('(assert-event (<= *fn2-run-layout-max-entry-bytes* *fn2-format-page-size*))',s)
  self.assertIn('(assert-event (<= (+ (* 2 *fn2-run-entries-base*) *fn2-run-restart-bytes* 32)',s)
  self.assertIn('(assert-event (<= *fn2-checkpoint-restore-semantic-entry-bytes* *fn2-checkpoint-semantic-visit-bytes*))',s)
 def test_boot_declares_envelope_but_charges_exact_assembled_cost(self):
  self.assertIn(':budget (:bytes *fn2-checkpoint-semantic-visit-bytes* :steps 32 :descriptors 4)',read('boot-kind.lisp'))
  s=read('boot.lisp')
  self.assertIn(':charge :bytes *fn2-checkpoint-restore-semantic-entry-bytes*',s)
  self.assertNotIn(':charge :bytes *fn2-checkpoint-semantic-visit-bytes*',s)
 def test_actual_scheduler_grant_tracks_registered_machine_budgets(self):
  n=node('machines.lisp','defun','fn2-machine-work-ceiling')
  self.assertIn('(fn2-machine-property name :budget world)',raw('machines.lisp',n))
  n=node('executor-loop-events.lisp','defmacro','fn2-executor-loop-events')
  s=raw('executor-loop-events.lisp',n)
  self.assertIn('(fn2-machine-property (car names) :budget world)',s)
  self.assertIn('(fn2-exec-kinds-work-max (fn2-machine-names (w state)) (w state))',s)
  self.assertIn('(* (nfix k) *fn2-turn-transition-max*)',s)
  self.assertIn('(fn2-turn-work-room-p h k nvisits',s)
if __name__=='__main__':unittest.main()
