"""Source-only replay/arity controls for the runnable semantic-seal unit."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_seal_fixture as rw
import event_archive_seal_rewrite as seal
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
class Fixture(unittest.TestCase):
 def test_replays_actual_writer_setup_and_real_local_carriers(self):
  s=read('tests/event-archive-cold-seal-unit.lisp')
  self.assertEqual(s,rw.generate(read('tests/event-archive-cold-member-unit.lisp')))
  args=calls(s,'(defun fn2-easc-body ?args ?*body)')[0].captures['args'].items
  expected=[a.low for a in args[1:]]
  actual=[m.captures['name'].low for m in calls(s,'(with-local-stobj ?name ?*body)')]
  self.assertEqual(expected,actual);self.assertEqual(len(expected),20)
  self.assertFalse(calls(s,'(with-local-stobj fn2-core ?*body)'))
 def test_original_records_frame_and_body_use_actual_shared_writer_hash(self):
  s=read('tests/event-archive-cold-seal-unit.lisp')
  for p in ['(fn2-commit-pack :record-header ?*args)', '(fn2-commit-pack :record ?*args)',
            '(fn2-commit-pack :frame 1 ?*args)', '(fn2-commit-pack :seal 2 ?*args)',
            '(fn2-format-run kind t ?*args)',
            '(fn2-digest-store *fn2-commit-digest-bytes* writer-result scratch sg *fn2-commit-scratch-records* 1 2 3 fn2-digests fn2-pool)',
            '(fn2-event-archive-member-entry-encode ?*args)', '(fn2-event-archive-member-entry-decode ?*args)',
            '(fn2-event-archive-cold-batch-seal-step 0 ?*args)', '(fn2-event-archive-cold-batch-seal-step 1 ?*args)',
            '(equal before (fn2-easc-snapshot ?*args))', '(equal (fn2-digest-list saved-seal fn2-digests) original-seal)',
            '(equal (fn2-digest-list hash fn2-digests) original-records)']:
   self.assertTrue(calls(s,p),p)
  self.assertFalse(calls(s,'(fn2-b3-byte ?*args)'))
  self.assertTrue(calls(s,'(whole (and premise ?*rest))'))
  self.assertCountEqual([lr.flat(m.captures['fault']) for m in calls(s,'(assert-event (fn2-easc-test ?fault))')],['nil',':hash',':namespace',':tail'])
 def test_actual_provider_argument_and_result_counts(self):
  s=read('tests/event-archive-cold-seal-unit.lisp')
  for path,name,mvs in [('books/format-check.lisp','fn2-format-run',6),
                        ('books/event-archive-cold-members.lisp','fn2-event-archive-cold-batch-seal-step',10)]:
   if name.endswith('seal-step'):
    decl=calls(read(path),'(fn2-event-archive-operation ('+name+' ?*scalars) ?children ?outs ?*body)')[0]
    arity=len(decl.captures['scalars'])+len(decl.captures['children'].items)
   else:arity=len(calls(read(path),'(defun '+name+' ?args ?*body)')[0].captures['args'].items)
   for m in calls(s,'('+name+' ?*args)'):self.assertEqual(len(m.node.items)-1,arity,name)
   for m in calls(s,'((mv ?*values) ('+name+' ?*args))'):self.assertEqual(len(m.captures['values']),mvs,name)
if __name__=='__main__':unittest.main()
