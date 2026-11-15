"""Cached root class and actual schema10 interval capture, source controls."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_root_rewrite as rw
import event_archive_frontier_begin_rewrite as frontier
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
class Root(unittest.TestCase):
 def test_manifest_constructor_replay_and_idempotence(self):
  old=read('tools/fixtures/event-archive-cold-cursor-before-root.lisp')
  after,helper=rw.transform(old)
  current=read('books/event-archive-cold-cursor.lisp');composed=frontier.cursor(after)
  for pattern in ['(defun fn2-event-archive-cold-start-root ?*body)','(fn2-event-archive-operation (fn2-event-archive-cold-cursor-begin ?*args) ?*body)']:
   a=calls(composed,pattern)[0].node;b=calls(current,pattern)[0].node
   self.assertEqual(composed[a.start:a.end],current[b.start:b.end])
  self.assertEqual(rw.transform(after),(after,None))
  self.assertEqual(len(calls(helper,'(fn2-run-cursor-start ?*args)')),1)
  self.assertEqual(len(calls(helper,'(fn2-run-cursors-put c ?*args)')),1)
 def test_actual_entry_interval_must_join_next_event(self):
  s=read('books/event-archive-cold-members.lisp')
  for p in ['(posp entries)','(<= entries end)','(<= end (fn2-event-archive-cut-event 1 fn2-event-archive))',
            '(equal (+ 1 (- end entries)) (fn2-event-archive-next-event 1 fn2-event-archive))',
            '(equal (fn2-fields-value (+ eb *fn2-manifest-entry-field-schema*) fn2-fields) *fn2-event-archive-schema*)']:
   self.assertTrue(calls(s,p),p)
  self.assertTrue(calls(s,'(fn2-event-archive-cold-reach-current-p ?*args)'))
  self.assertTrue(calls(s,'(fn2-event-archive-reached-page-p ?*args)'))
 def test_exact_decoded_hash_and_root_before_source_page_reuse(self):
  s=read('books/event-archive-cold-members.lisp')
  self.assertTrue(calls(s,'(equal (fn2-fields-ref-slot ref fn2-fields) page)'))
  self.assertTrue(calls(s,'(equal (fn2-fields-ref-gen ref fn2-fields) pgen)'))
  fetched=calls(s,'(fn2-rec-fetch ?*args)')[0].node
  captured=calls(s,'(fn2-event-archive-copy-digest 1 :member 0 hash fn2-digests fn2-event-archive)')[0].node
  start=calls(s,'(fn2-event-archive-cold-start-root c :member base fn2-event-archive fn2-run-cursors)')[0].node
  self.assertLess(fetched.start,captured.start);self.assertLess(captured.start,start.start)
  self.assertNotIn('*fn2-event-archive-phase-complete*',s)
  self.assertNotIn('fn2-pool-reset',s)
if __name__=='__main__':unittest.main()
