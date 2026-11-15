"""Actual crypto-provider call cone; no original-frame/terminal substitution."""
from pathlib import Path
import json
import unittest
import lisp_rewrite as lr
import event_archive_seal_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def form(s,p):
 n=calls(s,p)[0].node;return s[n.start:n.end]
class Seal(unittest.TestCase):
 def test_exact_source_projection_holders_old_leaf_and_active_row_unchanged(self):
  before=json.loads(read('tools/fixtures/event-archive-seal-before.json'))
  for path,fn in [('books/event-archive-state.lisp',rw.state),('books/event-archive-cold-members.lisp',rw.members),('books/event-archive-cold-cursor.lisp',rw.cursor)]:
   after=fn(before[path]);self.assertEqual(after,read(path));self.assertEqual(after,fn(after))
  for path,pattern in [('books/event-archive-state.lisp','(defun fn2-event-archive-candidate-held-p ?*body)'),
                       ('books/event-archive-cold-members.lisp','(fn2-event-archive-operation fn2-event-archive-cold-member-step ?*body)')]:
   self.assertEqual(form(before[path],pattern),form(read(path),pattern))
  s=form(read('books/event-archive-cold-members.lisp'),'(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget) ?*body)')
  self.assertFalse(calls(s,'(fn2-event-archive-put 0 ?*args)'))
 def test_real_generated_span_and_byte_fetch_then_same_semantic_core(self):
  s=form(read('books/event-archive-cold-members.lisp'),'(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget) ?*body)')
  for p in ['(fn2-event-read-seal-span-step budget fn2-event-read fn2-fields fn2-pool)',
            '(equal (fn2-event-read-body-len 0 fn2-event-read) length)',
            '(fn2-rec-fetch-step budget ?*args)',
            '(fn2-event-read-format-core budget expected previous fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)',
            '(complete (and (eq code :ok) (equal next *fn2-commit-digest-bytes*) (equal acc 0)))',
            '(equal (fn2-fields-ref-off field fn2-fields) off)']:
   self.assertTrue(calls(s,p),p)
  self.assertFalse(calls(s,'(fn2-rec-fetch ?*args)'))
  self.assertFalse(calls(s,'(fn2-format-sealed-batch-decode ?*args)'))
  self.assertFalse(calls(s,'(fn2-b3-byte ?*args)'))
 def test_positive_zero_precedes_any_private_reader_genesis_or_hash_mutation(self):
  s=form(read('books/event-archive-cold-members.lisp'),'(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget) ?*body)')
  zero=calls(s,'((when (zp budget)) ?*body)')[0].node
  for pattern in ['(fn2-digests-put ?*args)','(fn2-event-read-put ?*args)', '(fn2-rec-fetch-step ?*args)', '(fn2-event-read-format-core ?*args)']:
   self.assertLess(zero.start,calls(s,pattern)[0].node.start,pattern)
  start=calls(s,'((when (equal (fn2-event-archive-batch-reader-started 1 fn2-event-archive) 0)) ?*body)')[0].node
  for p in ['(equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-idle*)',
            '(equal (fn2-event-archive-batch-commit 1 fn2-event-archive) 1)',
            '(equal (fn2-event-archive-batch-first 1 fn2-event-archive) 1)',
            '(equal (fn2-event-read-witness-enabled 0 fn2-event-read) 0)']:
   self.assertTrue(lr.match(p,[start]),p)
 def test_source_reader_and_header_idle_scope_remain_exact(self):
  whole=read('books/event-archive-cold-members.lisp')
  first=form(whole,'(defun fn2-event-archive-cold-batch-first-page-p ?*body)')
  header=form(whole,'(defun fn2-event-archive-cold-batch-header-current-p ?*body)')
  self.assertFalse(calls(first,'(equal (fn2-fc-phase ?row fn2-fc) *fn2-fc-phase-idle*)'))
  self.assertTrue(calls(header,'(equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)'))
  reader=form(whole,'(defun fn2-event-archive-cold-seal-reader-p ?*body)')
  for r,a in [('token','source-generation'),('slot','batch-accumulator-slot'),('gen','batch-accumulator-gen'),
              ('journal-history','batch-history'),('journal-incarnation','batch-incarnation'),('commit','batch-commit')]:
   self.assertTrue(calls(reader,'(equal (fn2-event-read-'+r+' 0 fn2-event-read) (fn2-event-archive-'+a+' 1 fn2-event-archive))'))
 def test_actual_success_only_partial_receipt_preserves_jseal_before_leaf_temp_reuse(self):
  s=form(read('books/event-archive-cold-members.lisp'),'(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget) ?*body)')
  self.assertTrue(calls(s,'(verified (and (eq code :ok) (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-read-records*)))'))
  self.assertTrue(calls(s,'(fn2-digests (if verified (fn2-digest-copy saved-seal expected fn2-digests) fn2-digests))'))
  self.assertTrue(calls(s,'(if verified *fn2-event-archive-batch-phase-records-zero* *fn2-event-archive-batch-phase-uncertain*)'))
  self.assertNotIn('*fn2-event-archive-batch-phase-complete*',s)
  self.assertNotIn('*fn2-event-archive-phase-complete*',s)
  self.assertFalse(calls(s,'(fn2-alloc-edge-drop ?*args)'))
  self.assertFalse(calls(s,'(fn2-alloc-release ?*args)'))
 def test_real_provider_arity_and_mutable_result_counts(self):
  s=form(read('books/event-archive-cold-members.lisp'),'(fn2-event-archive-operation (fn2-event-archive-cold-batch-seal-step budget) ?*body)')
  for path,name,mvs in [('books/event-read-verify.lisp','fn2-event-read-seal-span-step',3),
                        ('books/pool-digest.lisp','fn2-rec-fetch-step',4),
                        ('books/event-read-verify.lisp','fn2-event-read-format-core',9)]:
   definition=calls(read(path),'(defun '+name+' ?args ?*body)')[0]
   for call in calls(s,'('+name+' ?*args)'):
    self.assertEqual(len(call.node.items)-1,len(definition.captures['args'].items),name)
   for call in calls(s,'((mv ?*vars) ('+name+' ?*args))'):
    self.assertEqual(len(call.captures['vars']),mvs,name)
if __name__=='__main__':unittest.main()
