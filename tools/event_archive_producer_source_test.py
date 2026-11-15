#!/usr/bin/env python3
"""Source-boundary controls; no execution, persistence, or reclamation claim."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def source(name):return (ROOT/'books'/name).read_text()
def form(file,head,name):
 return lr.match('('+head+' '+name+' ?*body)',lr.parse(source(file)).forms,deep=False)[0].node
def calls(n,name):return lr.match('('+name+' ?*args)',[n])
def has(n,name):return bool(calls(n,name))
def text(file,n):return source(file)[n.start:n.end]
class ArchiveProducerSource(unittest.TestCase):
 def test_schema_is_internal_inline_and_uses_one_assembly(self):
  n=form('event-archive-schema.lisp','defrunschema','fn2-event-archive-member')
  s=text('event-archive-schema.lisp',n)
  self.assertIn(':id 20 :internal t',s)
  self.assertIn('(canonical (:octets 4096))',s)
  self.assertNotIn('physical-unit',s)
  self.assertEqual(source('runs-served.lisp').count('(include-book "event-archive-schema")'),1)
  self.assertNotIn('defrunschema',source('event-archive-producer.lisp'))
 def test_generic_live_and_replay_refuse_before_mutation(self):
  put=form('machines-c-successor.lisp','defun','fn2-succ-put')
  replay=form('machines-c-bind.lisp','defun','fn2-succ-replay-records')
  self.assertTrue(has(put,'fn2-run-layout-internal-p'))
  self.assertTrue(has(replay,'fn2-run-layout-internal-p'))
  self.assertLess(calls(put,'fn2-run-layout-internal-p')[0].node.start,calls(put,'fn2-succ-slots-put')[0].node.start)
  self.assertLess(calls(replay,'fn2-run-layout-internal-p')[0].node.start,calls(replay,'fn2-run-layout-decode')[0].node.start)
  specs=text('machines-c-bind.lisp',form('machines-c-bind.lisp','defun','fn2-succ-schema-specs'))
  self.assertIn('((fn2-decl-get :internal row) nil)',specs)
 def test_physical_archive_does_not_expand_semantic_record_kinds(self):
  self.assertIn('(defconst *fn2-commit-txn-schema-record-kind-last* *record-kind-authority-head*)',source('format-events.lisp'))
  self.assertNotIn('event-archive',source('journal-record-body.lisp'))
 def test_begin_derives_cut_owner_namespace_and_reuses_admitted_builder(self):
  n=form('event-archive-producer.lisp','fn2-event-archive-operation','fn2-event-archive-begin')
  for name in ['fn2-event-archive-sourcep','fn2-checkpoint-root1-workspaces','fn2-run-build-start']:
   self.assertTrue(has(n,name),name)
  start=calls(n,'fn2-run-build-start')[0].node
  args=source('event-archive-producer.lisp')[start.start:start.end]
  self.assertIn('*fn2-event-archive-schema*',args)
  self.assertIn('(fn2-checkpoint-build-history 0 fn2-checkpoint-build)',args)
  self.assertIn('(fn2-checkpoint-source-wbase)',args)
  self.assertFalse(has(n,'fn2-pool-reserve'))
 def test_stage_requires_actual_phase3_held_reader_and_shared_leaf(self):
  n=form('event-archive-producer.lisp','fn2-event-archive-operation','fn2-event-archive-stage')
  for name in ['fn2-event-archive-sourcep','fn2-event-read-source-held-p','fn2-event-read-ownerp',
               'fn2-mk-ready','fn2-b-event-leaf-digest','fn2-run-build-add','fn2-digest-store']:
   self.assertTrue(has(n,name),name)
  s=text('event-archive-producer.lisp',n)
  self.assertIn('(equal (fn2-journal-members-hash-phase 0 fn2-journal-members) 3)',s)
  self.assertIn('(equal (+ 1 (fn2-mk-size row fn2-mk)) event)',s)
  self.assertIn('(ref-off start) (ref-len (- end start))',s)
  self.assertIn('(fn2-digest-store 32 leaf scratch sgen 0',s)
  self.assertTrue(all(x.low.startswith('fn2-') for x in n.items[2].items))
  self.assertFalse(has(n,'fn2-journal-members-consumed'))
  self.assertFalse(has(n,'fn2-mk-append'))
 def test_no_overwrite_or_release_authority_is_added(self):
  s=source('event-archive-producer.lisp')
  for name in ['fn2-alloc-edge-drop','fn2-pool-release','fn2-alloc-free','fn2-checkpoint-root-produced']:
   self.assertNotIn('('+name,s)
  n=form('event-archive-producer.lisp','fn2-event-archive-operation','fn2-event-archive-stage')
  self.assertTrue(has(n,'fn2-run-builds-entries'))
  self.assertIn(':staged',text('event-archive-producer.lisp',n))
 def test_shared_page_recipes_derive_role_without_a_second_writer(self):
  n=form('checkpoint-metadata-state.lisp','defun','fn2-checkpoint-metadata-role')
  self.assertTrue(has(n,'fn2-run-layout-internal-p'))
  s=text('checkpoint-metadata-state.lisp',n)
  self.assertIn('(equal (fn2-checkpoint-metadata-source-kind 0 fn2-checkpoint-metadata) 2) 3)',s)
  self.assertTrue(s.rstrip().endswith('1)))'))
  for file,fn in [('checkpoint-metadata.lisp','fn2-checkpoint-metadata-page-for-build'),
                  ('checkpoint-metadata-page.lisp','fn2-checkpoint-metadata-page-bind'),
                  ('checkpoint-metadata-page.lisp','fn2-checkpoint-metadata-page-complete-p')]:
   self.assertEqual(len(calls(form(file,'defun',fn),'fn2-checkpoint-metadata-role')),1)
if __name__=='__main__':unittest.main()
