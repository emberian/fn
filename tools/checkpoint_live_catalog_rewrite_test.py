"""Actual root1 EMIT capture and pending-source refusal controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_live_catalog_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def node(s,p):return lr.match(p,lr.parse(s).forms)[0].node
class Intake(unittest.TestCase):
 def setUp(self):
  self.driver=(ROOT/'books/checkpoint-metadata-driver.lisp').read_text()
  self.live=(ROOT/'books/checkpoint-summary-live-catalog.lisp').read_text()
 def test_fixed_actual_driver_transformation(self):
  before=(ROOT/'tools/fixtures/checkpoint-live-catalog-driver-before.lisp').read_text()
  self.assertEqual(self.driver,rw.rewrite(before))
  with self.assertRaises(ValueError):rw.rewrite(self.driver)
 def test_actual_family_projection_is_bounded(self):
  forms=lr.parse(self.driver).forms
  for name,carrier in [('begin','fn2-checkpoint-summary'),('work','fn2-checkpoint-summary-sources'),('step','fn2-checkpoint-summary-sources')]:
   rows=[m.node for m in lr.match(f'(fn2-checkpoint-root1-{name} ?*args)',forms) if len(m.node.items)>2 and getattr(m.node.items[1],'low','')=='fn2-checkpoint-root1']
   self.assertEqual(len(rows),1);self.assertIn(carrier,[x.low for x in rows[0].items]);self.assertLessEqual(len(rows[0].items)-1,31)
 def test_emit_success_is_immediate_capture_boundary(self):
  work=node(self.driver,'(fn2-checkpoint-root1-operation fn2-checkpoint-root1-work ?*body)')
  branch=lr.match('((when (eq code :ok)) ?*body)',[work])
  self.assertEqual(len(branch),1)
  self.assertTrue(lr.match('(fn2-checkpoint-summary-live-record ?*args)',[branch[0].node]))
  self.assertTrue(lr.match('(if (eq captured :captured) :more captured)',[branch[0].node]))
  self.assertTrue(lr.match('(fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-uncertain* fn2-checkpoint-root1)',[branch[0].node]))
 def test_same_typed_recorder_and_actual_owner(self):
  record=node(self.live,'(defun fn2-checkpoint-summary-live-record ?*body)')
  self.assertTrue(lr.match('(fn2-checkpoint-summary-record-fields 1 ?*args)',[record]))
  self.assertTrue(lr.match('(fn2-checkpoint-summary-live-current-p ?*args)',[record]))
  self.assertTrue(lr.match('(= (fn2-checkpoint-source-rank 0 fn2-checkpoint-source) (fn2-checkpoint-metadata-manifest-entries 0 fn2-checkpoint-metadata-manifest))',[record]))
  self.assertFalse(lr.match('(fn2-run-layout-decode ?*args)',[record]))
 def test_no_pending_overwrite_or_caller_tag(self):
  begin=node(self.live,'(defun fn2-checkpoint-summary-live-begin ?*body)')
  self.assertTrue(lr.match('(= (fn2-checkpoint-summary-phase 1 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-idle*)',[begin]))
  self.assertTrue(lr.match('(fn2-checkpoint-summary-fresh-tag fn2-checkpoint-summary)',[begin]))
  self.assertTrue(lr.match('(fn2-checkpoint-build-ownerp token kind owner generation fn2-checkpoint-build fn2-csnapshot)',[begin]))
  self.assertFalse(lr.match('(fn2-checkpoint-summary-put 0 ?*args)',[begin]))
 def test_emit_entry_survives_writer_scratch(self):
  # The actual writer decoder writes PREV inside its own fields workspace;
  # manifest BEGIN requires that whole workspace disjoint from entry-base.
  assembly=(ROOT/'books/runs-assemble.lisp').read_text()
  writer=node(assembly,'(defun fn2-run-add-write ?*body)')
  self.assertTrue(lr.match('(fn2-run-layout-decode sid lv prev ?*args)',[writer]))
  manifest=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  begin=node(manifest,'(defun fn2-checkpoint-metadata-manifest-begin ?*body)')
  self.assertTrue(lr.match('(or (<= (+ entry-base *fn2-run-entry-rows*) fields) (<= (+ fields *fn2-run-build-fields*) entry-base))',[begin]))
if __name__=='__main__':unittest.main()
