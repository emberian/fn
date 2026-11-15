"""Replay source-binding class and actual reader progress/refusal controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_record_digest_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def form(s,p):
 n=calls(s,p)[0].node;return s[n.start:n.end]
class RecordDigest(unittest.TestCase):
 def test_declaration_capture_comparison_class_exact_replay(self):
  for name,fun in [('event-read-state',rw.state),('event-read-verify',rw.verify),('event-read-source',rw.source_begin),('event-read-verified-unit',rw.fixture)]:
   before=read('tools/fixtures/record-digest-before-'+name+'.lisp')
   after=fun(before)
   self.assertEqual(after,read(('tests/' if name.endswith('unit') else 'books/')+name+'.lisp'),name)
   self.assertEqual(after,fun(after))
  state=read('books/event-read-state.lisp');verify=read('books/event-read-verify.lisp')
  current=form(verify,'(defun fn2-event-read-record-digest-current-p ?*body)')
  core=form(verify,'(defun fn2-event-read-format-core ?*body)')
  semantic=form(core,'((when semantic) ?*body)')
  for name,typ in rw.SAVED:
   self.assertTrue(calls(state,'(fetch-'+name+' :'+typ+')'),name)
   self.assertTrue(calls(semantic,'(fetch-'+name+' (fn2-event-read-'+name+' 0 fn2-event-read))'),name)
   self.assertTrue(calls(current,'(equal (fn2-event-read-fetch-'+name+' 0 fn2-event-read) (fn2-event-read-'+name+' 0 fn2-event-read))'),name)
 def test_semantic_receipt_precedes_bounded_fetch_no_legacy_call(self):
  s=read('books/event-read-verify.lisp');core=form(s,'(defun fn2-event-read-format-core ?*body)')
  semantic=form(core,'((when semantic) ?*body)')
  self.assertFalse(calls(core,'(fn2-rec-fetch ?*args)'))
  self.assertTrue(calls(semantic,'(fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)'))
  self.assertTrue(calls(semantic,'(record-fetch-next 0)'));self.assertTrue(calls(semantic,'(phase *fn2-event-read-phase-record-digest*)'))
  fetch=form(s,'(defun fn2-event-read-record-digest-step ?*body)')
  self.assertEqual(len(calls(fetch,'(fn2-rec-fetch-step budget ?*args)')),1)
  self.assertTrue(calls(fetch,'(complete (and (eq code :ok) (equal next 32) (equal acc 0)))'))
  self.assertTrue(calls(fetch,'(capture (and complete (equal (fn2-event-read-witness-enabled 0 fn2-event-read) 1)))'))
  branch=calls(core,'((when (equal phase *fn2-event-read-phase-record-digest*)) ?*body)')[0].node
  self.assertLess(branch.start,calls(core,'(fn2-rec-context ?*args)')[0].node.start)
  self.assertLess(branch.start,calls(core,'(fn2-format-run ?*args)')[0].node.start)
  constants=read('books/digests.lisp')
  self.assertTrue(calls(constants,'(defconst *fn2-fc-result* 125)'));self.assertTrue(calls(constants,'(defconst *fn2-fc-hash* 126)'))
 def test_zero_gate_is_after_source_refusal_before_possible_digest_write(self):
  s=form(read('books/event-read-verify.lisp'),'(defun fn2-event-read-format-step ?*body)')
  zero=calls(s,'((when (equal budget 0)) ?*body)')[0].node
  self.assertGreater(zero.start,calls(s,'(fn2-event-read-source-held-p ?*args)')[0].node.start)
  self.assertLess(zero.start,calls(s,'(fn2-event-source-seal ?*args)')[0].node.start)
  current=form(read('books/event-read-verify.lisp'),'(defun fn2-event-read-record-digest-current-p ?*body)')
  for p in ['(equal (fn2-fields-ref-slot field fn2-fields) (fn2-event-read-slot 0 fn2-event-read))',
            '(equal (fn2-fields-ref-gen field fn2-fields) (fn2-event-read-gen 0 fn2-event-read))',
            '(equal (fn2-fields-ref-off field fn2-fields) off)',
            '(equal (fn2-fields-ref-len field fn2-fields) 32)',
            '(fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)',
            '(<= (+ off 32) (+ (fn2-event-read-body-off 0 fn2-event-read) (fn2-event-read-body-len 0 fn2-event-read)))']:
   self.assertTrue(calls(current,p),p)
 def test_actual_reader_not_seeded_receipt_budget_one_zero_and_interleavings(self):
  s=read('tests/event-read-verified-unit.lisp')
  for p in ['(fn2-epv-format 0 fn2-core)','(fn2-epv-format 1 fn2-core)',
            '(equal before (fn2-epv-fetch-snapshot fn2-core))',
            '(fn2-epv-fetch-refusals ?faults fn2-core)',
            '(= after (+ next 1))','(eq code (if (= after 32) :ok :more))',
            '(fn2-epv-fetch-word-frame 0 after ?before ?after)',
            '(fn2-epv-fetch-controls fn2-core)','(fn2-epv-fetch-one fn2-core)',
            '(fn2-commit-admit-keyed ?*args)','(fn2-retirement-live-drive ?*args)',
            '(fn2-epv-open ?*args)','(fn2-epv-test nil)',
            '(fn2-epv-test :seal)','(fn2-epv-test :records)', '(fn2-epv-test :loan)',
            '(fn2-pool-release ?*args)', '(eq code :stale)',
            '(equal digest (fn2-digests-copy fn2-digests))']:
   self.assertTrue(calls(s,p),p)
  self.assertIn("'(:token :slot :gen :commit :ref :result)",s)
  self.assertFalse(calls(s,'(fn2-event-read-put ?i (phase *fn2-event-read-phase-record-digest*) ?*rest)'))
  self.assertTrue(calls(s,'(fn2-sim-complete ?*args)'));self.assertTrue(calls(s,'(fn2-harvest-one fn2-core)'))
if __name__=='__main__':unittest.main()
