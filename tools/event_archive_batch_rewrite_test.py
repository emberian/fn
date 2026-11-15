"""Concrete selected-page/header decoder binding; no batch authority claim."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_batch_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def form(s,p):
 n=calls(s,p)[0].node;return s[n.start:n.end]
class Batch(unittest.TestCase):
 def test_exact_source_projection_retains_old_holders_and_leaf_consumer(self):
  for name,fun in [('event-archive-state',rw.state),('event-archive-cold-members',rw.members),('event-archive-cold-member-unit',rw.fixture)]:
   before=read('tools/fixtures/cold-batch-before-'+name+'.lisp');after=fun(before)
   self.assertEqual(after,read(('tests/' if name.endswith('unit') else 'books/')+name+'.lisp'));self.assertEqual(after,fun(after))
   if name.endswith('unit'):continue
   for pattern in (['(defun fn2-event-archive-candidate-held-p ?*body)'] if name.endswith('state') else
                   ['(defun fn2-event-archive-cold-member-page-p ?*body)', '(fn2-event-archive-operation fn2-event-archive-cold-member-step ?*body)']):
    self.assertEqual(form(before,pattern),form(after,pattern))
 def test_saved_page_ref_identity_class(self):
  s=read('books/event-archive-cold-members.lisp')
  begin=form(s,'(fn2-event-archive-operation fn2-event-archive-cold-batch-begin ?*body)')
  current=form(s,'(defun fn2-event-archive-cold-batch-header-current-p ?*body)')
  for name,value in rw.BIND:
   self.assertTrue(calls(begin,'('+name+' '+value+')'),name)
   self.assertTrue(calls(current,'(equal (fn2-event-archive-'+name+' 1 fn2-event-archive) '+value+')'),name)
  self.assertTrue(calls(current,'(fn2-event-archive-cold-member-page-p ?*args)'))
  self.assertTrue(calls(current,'(fn2-event-archive-cold-batch-fields-p ?*args)'))
  for short,long in rw.REFS:
   for part in ['off','length']:
    accessor='len' if part=='length' else part
    self.assertTrue(calls(current,'(equal (fn2-fields-ref-'+accessor+' '+short+' fn2-fields) (fn2-event-archive-batch-'+short+'-'+part+' 1 fn2-event-archive))'))
 def test_generated_budgeted_decoder_exact_end_and_no_header_authority(self):
  s=read('books/event-archive-cold-members.lisp')
  step=form(s,'(fn2-event-archive-operation (fn2-event-archive-cold-batch-header-step budget) ?*body)')
  for p in ['(fn2-format-frame-header-start base fn2-fields)',
            '(fn2-format-frame-header-decode-step base slot gen off end kind owner generation budget fn2-fields fn2-pool)',
            '(equal next end)', '(equal (fn2-fields-value (+ base *fn2-format-frame-header-field-payload-length*) fn2-fields) *fn2-commit-records-room*)',
            '((when (zp budget)) (mv :more fn2-event-archive fn2-fields))',
            '(valid *fn2-event-archive-batch-phase-seal-copy*)']:
   self.assertTrue(calls(step,p),p)
  self.assertFalse(calls(step,'(fn2-format-run ?*args)'))
  self.assertFalse(calls(step,'(fn2-alloc-edge-drop ?*args)'))
  self.assertFalse(calls(step,'(phase *fn2-event-archive-phase-complete*)'))
  self.assertFalse(calls(step,'(batch-phase *fn2-event-archive-batch-phase-complete*)'))
  self.assertIn('unreachable-in-composition',s)
  self.assertNotIn('3900',step);self.assertNotIn('942',step);self.assertNotIn('95',step)
 def test_exact_existing_private_stripe_geometry_no_page_clobber(self):
  s=read('books/event-archive-cold-members.lisp')
  geometry=form(s,'(defun fn2-event-archive-cold-batch-fields-p ?*body)')
  for p in ['(fn2-b-fixed-cursor-rows-p ?rows)', '(not (equal row checker))',
            '(equal (fn2-run-cursors-rb c fn2-run-cursors) (* 128 checker))',
            '(<= (* 128 (+ row 1)) (fn2-fields-rows fn2-fields))']:
   self.assertTrue(calls(geometry,p),p)
  decl=calls(s,'(fn2-event-archive-operation (fn2-event-archive-cold-batch-header-step budget) ?children ?outs ?*body)')[0]
  self.assertEqual(lr.flat(decl.captures['outs']),'(fn2-event-archive fn2-fields)')
 def test_actual_writer_header_one_byte_zero_and_partial_refusal_controls(self):
  s=read('tests/event-archive-cold-member-unit.lisp')
  for p in ['(fn2-commit-pack :frame 1 ?*args)', '(fn2-commit-pack :seal 2 ?*args)',
            '(fn2-event-archive-member-entry-encode ?*args)', '(fn2-event-archive-member-entry-decode ?*args)',
            '(fn2-event-archive-cold-batch-begin ?*args)',
            '(fn2-event-archive-cold-batch-header-step 0 ?*args)',
            '(fn2-event-archive-cold-batch-header-step 1 ?*args)',
            '(<= (- after cursor) budget)', '(equal before (list (fn2-event-archive-copy fn2-event-archive) (fn2-fields-copy fn2-fields)))',
            '(eq code :source)', '(fn2-eamcu-test :batch-header)', '(fn2-eamcu-test :batch-commit)', '(fn2-eamcu-test :batch-tail)',
            '(= (fn2-event-archive-batch-history 1 fn2-event-archive) 17)',
            '(= (fn2-event-archive-history 1 fn2-event-archive) 123)',
            '(= (fn2-mk-size row fn2-mk) 0)']:
   self.assertTrue(calls(s,p),p)
  self.assertIn("'(:decoder-next :header-off :seal-off)",s)
  self.assertTrue(calls(read('books/event-archive-cold-members.lisp'),
    '(equal (fn2-fields-decode-next work fn2-fields) (fn2-event-archive-batch-cursor 1 fn2-event-archive))'))
if __name__=='__main__':unittest.main()
