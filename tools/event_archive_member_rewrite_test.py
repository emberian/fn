"""Actual frozen schema20 stream; no source flag can stand for prefix closure."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_accumulator_rewrite as acc
import event_archive_fixed_rows_rewrite as fixed
import event_archive_member_rewrite as rw
import event_archive_batch_rewrite as batch
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
def form(s,p):
 n=calls(s,p)[0].node
 return s[n.start:n.end]
class Member(unittest.TestCase):
 def test_cursor_replay_and_idempotence(self):
  after=batch.project_cursor(acc.project('cursor', fixed.rewrite(rw.cursor(read('tools/fixtures/archive-members-before-cursor.lisp')))))
  self.assertEqual(after,read('books/event-archive-cold-cursor.lisp'));self.assertEqual(batch.project_cursor(acc.project('cursor', fixed.rewrite(rw.cursor(after)))),after)
 def test_actual_bind_return_class_and_physical_query(self):
  after=rw.bind(read('tools/fixtures/archive-members-before-bind.lisp'))
  pattern='(fn2-event-archive-operation fn2-event-archive-cold-bind-member ?*body)'
  self.assertEqual(form(after,pattern),form(read('books/event-archive-cold-members.lisp'),pattern));self.assertEqual(rw.bind(after),after)
  for p in ['(fn2-fields-set-value q (fn2-event-archive-history 1 fn2-event-archive) fn2-fields)',
            '(fn2-fields-set-value (+ q 1) (fn2-event-archive-incarnation 1 fn2-event-archive) fn2-fields)',
            '(fn2-fields-set-value (+ q 2) (fn2-event-archive-next-event 1 fn2-event-archive) fn2-fields)']:
   self.assertTrue(calls(after,p),p)
 def test_real_member_admission_binds_current_source_and_claimed_page(self):
  s=form(read('books/event-archive-cold-members.lisp'),'(defun fn2-event-archive-cold-member-page-p ?*body)')
  for p in ['(fn2-event-archive-cold-reach-current-p ?*args)','(fn2-event-archive-cold-cursor-source-p ?*args)',
            '(fn2-event-archive-reached-page-p ?*args)','(equal (fn2-run-cursors-level c fn2-run-cursors) 0)',
            '(equal (fn2-event-archive-entry-pending 1 fn2-event-archive) 1)',
            '(equal (fn2-event-archive-read-armed 1 fn2-event-archive) 0)']:
   self.assertTrue(calls(s,p),p)
 def test_only_shared_copy_scanner_hash_with_preappend_comparison(self):
  s=form(read('books/event-archive-cold-members.lisp'),'(fn2-event-archive-operation fn2-event-archive-cold-member-step ?*body)')
  for p in ['(fn2-pool-copy-range page pgen off scratch sgen 0 length kind owner generation fn2-pool)',
            '(fn2-journal-members-begin event 1 0 length scratch sgen kind owner generation fn2-journal-members)',
            '(not (equal row (fn2-run-loads-checker c fn2-run-loads)))',
            '(fn2-rec-fetch 0 expected page pgen (fn2-fields-ref-off stored-leaf fn2-fields) kind owner generation fn2-pool fn2-digests)',
            '(fn2-digest-equal leaf expected fn2-digests)',
            '(fn2-event-members-step fields row leaf fn2-journal-members fn2-mk fn2-b3 fn2-fields fn2-pool fn2-digests)']:
   self.assertEqual(len(calls(s,p)),1,p)
  self.assertLess(calls(s,'(fn2-digest-equal ?*args)')[0].node.start,calls(s,'(fn2-event-members-step ?*args)')[0].node.start)
  for name in ['fn2-mk-append','fn2-b3-byte','fn2-run-layout-decode','fn2-pool-release']:
   self.assertFalse(calls(s,'('+name+' ?*args)'))
 def test_counts_only_after_actual_scanner_done_and_manifest_after_eof(self):
  s=read('books/event-archive-cold-members.lisp')
  done=calls(s,'((when (eq code :done)) ?*body)')[0].node
  self.assertTrue(lr.match('(member-seen (+ 1 (fn2-event-archive-member-seen 1 fn2-event-archive)))',[done]))
  self.assertTrue(lr.match('(equal (fn2-journal-members-off 0 fn2-journal-members) length)',[done]))
  n=form(s,'(fn2-event-archive-operation fn2-event-archive-cold-next-manifest ?*body)')
  for p in ['(equal (fn2-run-cursors-phase c fn2-run-cursors) *fn2-run-cursor-phase-end*)',
            '(equal (fn2-event-archive-member-seen 1 fn2-event-archive) (fn2-event-archive-member-entries 1 fn2-event-archive))',
            '(equal (fn2-mk-size row fn2-mk) end)',
            '(fn2-event-archive-cold-start-root c :manifest base fn2-event-archive fn2-run-cursors)',
            '(fn2-fields-set-value (+ q 1) (+ 1 end) fn2-fields)']:
   self.assertTrue(calls(n,p),p)
  self.assertNotIn('*fn2-event-archive-phase-complete*',s)
  self.assertNotIn('prefix-complete',s)
 def test_composed_check_dispatch_and_actual_call_mv_shapes(self):
  before=read('tools/fixtures/archive-members-before-boot.lisp')
  after=acc.project('boot', fixed.rewrite(rw.boot(before)));self.assertEqual(after,read('books/event-archive-cold-boot.lisp'));self.assertEqual(acc.project('boot', fixed.rewrite(rw.boot(after))),after)
  driver=read('books/event-archive-cold-step.lisp')
  for name in ['fn2-event-archive-cold-bind-member','fn2-event-archive-cold-member-step','fn2-event-archive-cold-next-manifest','fn2-event-archive-cold-step-reach']:
   self.assertEqual(len(calls(driver,'('+name+' ?*args)')),1,name)
  self.assertIn(':covered-await-witness',driver);self.assertNotIn('*fn2-event-archive-phase-complete*',driver)
  definitions={}
  for path in ['books/event-archive-cold-step.lisp','books/event-archive-cold-members.lisp','books/event-archive-cold-reach.lisp']:
   for m in calls(read(path),'(fn2-event-archive-operation ?name ?children ?outputs ?*body)'):
    decl=m.captures['name']
   name=decl.items[0].low if isinstance(decl,lr.Lst) else decl.low
   scalars=len(decl.items)-1 if isinstance(decl,lr.Lst) else 0
   definitions[name]=(scalars+len(m.captures['children'].items),1+len(m.captures['outputs'].items))
  for path in ['books/event-archive-cold-step.lisp','books/event-archive-cold-members.lisp','tests/event-archive-cold-member-unit.lisp']:
   text=read(path)
   for name,(arity,mvs) in definitions.items():
    for m in calls(text,'('+name+' ?*args)'):self.assertEqual(len(m.node.items)-1,arity,(path,name))
    for m in calls(text,'((mv ?*vars) ('+name+' ?*args))'):self.assertEqual(len(m.node.items[0].items)-1,mvs,(path,name,'B* results'))
    for m in calls(text,'(mv-let ?bindings ('+name+' ?*args) ?*body)'):self.assertEqual(len(m.captures['bindings'].items),mvs,(path,name,'MV-LET results'))
 def test_runnable_boundary_fixture_uses_actual_codecs_and_refusal_snapshots(self):
  s=read('tests/event-archive-cold-member-unit.lisp')
  for p in ['(fn2-commit-pack :record-header ?*args)','(fn2-commit-pack :record ?*args)',
            '(fn2-event-archive-member-entry-encode ?*args)','(fn2-event-archive-member-entry-decode ?*args)',
            '(fn2-event-archive-cold-member-page-p ?*args)','(fn2-event-archive-cold-member-step ?*args)',
            '(equal before (fn2-eamcu-snapshot ?*args))']:
   self.assertTrue(calls(s,p),p)
  self.assertCountEqual([lr.flat(m.captures['fault']) for m in calls(s,'(assert-event (fn2-eamcu-test ?fault))')], ['nil',':event',':generation',':owner',':leaf',':accumulator-alias',':accumulator-generation',':batch-header',':batch-commit',':batch-tail',':batch-copy'])
  for n in calls(s,'(fn2-commit-pack ?*args)'):
   decl=calls(read('books/commit-format.lisp'),'(defun fn2-commit-pack ?args ?*body)')[0]
   self.assertEqual(len(n.node.items)-1,len(decl.captures['args'].items))
if __name__=='__main__':unittest.main()
