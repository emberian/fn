"""Replay the whole geometry class on immutable cold9f; preserve other forms."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_geometry_rewrite as rw
ROOT=Path(__file__).resolve().parents[1];F=ROOT/'tools/fixtures'
def named(s):
 return {n.items[1].low:rw.tree(n) for n in lr.parse(s).forms if hasattr(n,'items') and len(n.items)>1 and getattr(n.items[0],'low',None) in ['defun','defthm','defcolumns','defcorechild','defconst'] and hasattr(n.items[1],'low')}
class Geometry(unittest.TestCase):
 def test_old_current_source_replay_and_unchanged_remainder(self):
  before=(F/'event-archive-geometry-before-machines-b.lisp').read_text();after=rw.machines_b(before)
  old,new=named(before),named(after)
  for name,form in old.items():
   if name!='fn2-b-run-cursor-rows':self.assertEqual(new[name],form,name)
  provider=named((F/'event-archive-geometry-provider.lisp').read_text())
  for name,form in provider.items():self.assertEqual(new[name],form,name)
  self.assertEqual(rw.machines_b(after),after)
  # Current geometry composes the later canonical fixed-pair guard class.
  # Check exact composed declarations, rather than stripping their guards.
  guarded=(F/'event-archive-fixed-row-provider.lisp').read_text()
  composed=(F/'event-archive-geometry-provider.lisp').read_text()
  for n in lr.parse(guarded).forms:
   name=n.items[1].low
   if name=='fn2-b-fixed-cursor-rows-p':continue
   old=rw.one(composed,'(defun '+name+' ?*body)')
   composed=lr.write(composed,[(old.start,old.end,guarded[n.start:n.end])])
  current=(ROOT/'books/machines-b.lisp').read_text()
  self.assertEqual(rw.machines_b(current,provider=composed),current)
 def test_actual_providers_precede_every_call(self):
  before=(F/'event-archive-geometry-before-machines-b.lisp').read_text();after=rw.machines_b(before)
  for n in ['fn2-b-cursor-rows','fn2-b-cns-rows','fn2-b-auth-rows','fn2-b-read-rows']:
   definition=rw.one(after,'(defun '+n+' ?*body)')
   for m in lr.match('('+n+' ?*args)',lr.parse(after).forms):self.assertLess(definition.start,m.node.start,n)
 def test_runtime_readiness_replays_exactly(self):
  before=(F/'event-archive-geometry-before-run-physical-readiness.lisp').read_text();after=rw.readiness(before)
  self.assertEqual(after,(ROOT/'books/run-physical-readiness.lisp').read_text())
  self.assertEqual(rw.readiness(after),after)
 def test_formula_drift_refused(self):
  before=(F/'event-archive-geometry-before-machines-b.lisp').read_text()
  with self.assertRaises(ValueError):rw.machines_b(before.replace('*fn2-b-seal-source-cursors* 1))','*fn2-b-seal-source-cursors* 3))'))
if __name__=='__main__':unittest.main()
