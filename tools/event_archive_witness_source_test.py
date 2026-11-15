"""Actual verifier capture, scratch ownership and archive emission join controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_witness_rewrite as rw
import event_record_digest_rewrite as fetch
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def form(s,p):
 n=calls(s,p)[0].node
 return s[n.start:n.end]
class Witness(unittest.TestCase):
 def test_generated_bounds_and_single_schema_registration(self):
  s=read('books/event-archive-schema.lisp')
  self.assertEqual(len(calls(s,'(defrunschema fn2-event-archive-member ?*body)')),1)
  self.assertIn('(original-records-header (:octets ,*fn2-format-frame-header-max-size*))',s)
  self.assertIn('(original-sealed-batch (:octets ,*fn2-format-sealed-batch-max-size*))',s)
  self.assertIn('(batch-first (:id event))',s);self.assertTrue(calls(s,'(make-event ?*body)'))
  g=read('books/event-read-witness-geometry.lisp')
  self.assertNotIn('942',g);self.assertNotIn('95',g)
  self.assertTrue(calls(g,'(assert-event (<= *fn2-event-witness-work-bytes* *fn2-commit-unit-bytes*))'))
 def test_reader_state_and_native_stage_gate_replay(self):
  before=read('tools/fixtures/archive-witness-before-reader-state.lisp');after=fetch.state(rw.state(before))
  self.assertEqual(after,read('books/event-read-state.lisp'));self.assertEqual(rw.state(after),after)
  before=read('tools/fixtures/archive-witness-before-event-producer.lisp');after=rw.producer_gate(before)
  self.assertEqual(after,read('books/event-producer.lisp'));self.assertEqual(rw.producer_gate(after),after)
 def test_exact_mutable_output_class_and_actual_begin_caller(self):
  current=read('books/event-archive-producer.lisp')
  for name,inp in [('fn2-event-archive-begin',True),('fn2-event-archive-stage',False)]:
   old=read('tools/fixtures/archive-witness-before-event-archive-producer.lisp');after=rw.operation(old,name,inp)
   a=calls(after,'(fn2-event-archive-operation '+name+' ?*body)')[0].node
   b=calls(current,'(fn2-event-archive-operation '+name+' ?*body)')[0].node
   self.assertEqual(lr.flat(a.items[2]),lr.flat(b.items[2]));self.assertEqual(lr.flat(a.items[3]),lr.flat(b.items[3]))
   self.assertEqual(rw.operation(after,name,inp),after)
  control=read('books/event-archive-control.lisp')
  decl=calls(current,'(fn2-event-archive-operation fn2-event-archive-begin ?children ?outs ?*body)')[0]
  call=calls(control,'(fn2-event-archive-begin ?*args)')[0].node
  self.assertEqual(len(call.items)-1,len(decl.captures['children'].items))
  bind=calls(control,'((mv ?*vars) (fn2-event-archive-begin ?*args))')[0].node
  self.assertEqual(len(bind.items[0].items)-1,len(decl.captures['outs'].items)+1)
 def test_actual_semantic_success_captures_complete_body_before_records_read(self):
  s=form(read('books/event-read-verify.lisp'),'(defun fn2-event-read-format-core ?*body)')
  gate=calls(s,'((when semantic) ?*body)')[0].node
  self.assertTrue(lr.match('(fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)',[gate]))
  self.assertFalse(lr.match('(fn2-rec-fetch ?*args)',[gate]))
  self.assertTrue(lr.match('(phase *fn2-event-read-phase-record-digest*)',[gate]))
  current=form(read('books/event-read-verify.lisp'),'(defun fn2-event-read-record-digest-current-p ?*body)')
  self.assertTrue(calls(current,'(fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)'))
  step=form(read('books/event-read-verify.lisp'),'(defun fn2-event-read-record-digest-step ?*body)')
  self.assertTrue(calls(step,'(fn2-rec-fetch-step budget ?*args)'))
  self.assertTrue(calls(step,'(capture (and complete (equal (fn2-event-read-witness-enabled 0 fn2-event-read) 1)))'))
  self.assertTrue(calls(step,'(complete (and (eq code :ok) (equal next 32) (equal acc 0)))'))
  self.assertTrue(calls(step,'(witness-seal-length (if capture (fn2-event-read-body-len 0 fn2-event-read) ?else))'))
  self.assertTrue(calls(step,'(witness-commit (if capture (fn2-event-read-commit 0 fn2-event-read) ?else))'))
  self.assertTrue(calls(step,'(phase (cond (complete (if capture *fn2-event-read-phase-witness-seal* *fn2-event-read-phase-read-records*)) ?*rest))'))
  self.assertTrue(calls(s,'(equal (fn2-event-read-witness-phase 0 fn2-event-read) *fn2-event-witness-phase-records*)'))
  self.assertTrue(calls(s,'(or sealframe (fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) hash fn2-digests))'))
 def test_every_copy_is_bounded_and_source_bound(self):
  s=read('books/event-read-witness.lisp')
  for p in ['(count (min budget (- length cursor)))','((when (zp budget)) (mv :more fn2-event-read fn2-pool))',
            '(equal (fn2-event-read-witness-token 0 fn2-event-read) (fn2-event-read-token 0 fn2-event-read))',
            '(equal (fn2-event-read-witness-commit 0 fn2-event-read) (fn2-event-read-commit 0 fn2-event-read))',
            '(fn2-pool-copy-range slot gen (+ offset cursor) dst dgen (+ to cursor) count kind owner generation fn2-pool)']:
   self.assertTrue(calls(s,p),p)
  self.assertFalse(calls(s,'(fn2-format-run ?*args)'));self.assertFalse(calls(s,'(fn2-mk-append ?*args)'))
  fixture=read('tests/event-read-witness-unit.lisp')
  self.assertTrue(calls(fixture,'(fn2-erwu-test 1 nil)'));self.assertTrue(calls(fixture,'(fn2-erwu-test 4096 nil)'))
  self.assertTrue(calls(fixture,'(equal before (fn2-erwu-snapshot ?*args))'))
 def test_scratch_lifetime_and_actual_writer_emission_owns_ack(self):
  s=read('books/event-archive-producer.lisp');stage=form(s,'(fn2-event-archive-operation fn2-event-archive-stage ?*body)')
  self.assertFalse(calls(stage,'(fn2-pool-reset ?*args)'))
  self.assertTrue(calls(stage,'(fn2-event-archive-witness-current-p scratch sgen fn2-event-read fn2-pool)'))
  self.assertTrue(calls(stage,'(first (equal event (fn2-event-read-witness-first 0 fn2-event-read)))'))
  add=calls(stage,'(fn2-run-build-add ?*args)')[0].node
  ack=calls(stage,'(fn2-event-read-put 0 (witness-phase *fn2-event-witness-phase-emitted*) (witness-staged-event event))')[0].node
  self.assertLess(add.start,ack.start)
  self.assertTrue(calls(stage,'(fn2-event-read (if (eq code :ok) ?new fn2-event-read))'))
  begin=form(s,'(fn2-event-archive-operation fn2-event-archive-begin ?*body)')
  self.assertTrue(calls(begin,'(fn2-event-archive-sourcep ?*args)'))
  self.assertTrue(calls(begin,'(fn2-checkpoint-root1-workspaces ?*args)'))
  self.assertTrue(calls(begin,'(fn2-run-zero *fn2-event-witness-work-bytes* scratch sgen 0 kind owner gen fn2-pool)'))
 def test_next_source_cannot_overwrite_unemitted_receipt(self):
  s=form(read('books/event-read-source.lisp'),'(defun fn2-event-read-open-core ?*body)')
  self.assertTrue(calls(s,'(member-equal (fn2-event-read-witness-phase 0 fn2-event-read) (list *fn2-event-witness-phase-bound* *fn2-event-witness-phase-emitted*))'))
  self.assertTrue(calls(s,'(equal (fn2-event-read-witness-slot 0 fn2-event-read) scratch)'))
  self.assertTrue(calls(s,'(equal (fn2-event-read-witness-gen 0 fn2-event-read) sgen)'))
  self.assertLess(calls(s,'(equal (fn2-event-read-witness-token 0 fn2-event-read) token)')[0].node.start,calls(s,'(fn2-event-proof-pack-entry ?*args)')[0].node.start)
if __name__=='__main__':unittest.main()
