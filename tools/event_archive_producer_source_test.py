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
  n=lr.match('(defrunschema fn2-event-archive-member ?*body)',lr.parse(source('event-archive-schema.lisp')).forms)[0].node
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
  self.assertIn('(equal b (fn2-checkpoint-metadata-build 0 fn2-checkpoint-metadata))',s)
  self.assertIn('(list *fn2-event-archive-schema* 10)',s)
  self.assertIn('(and (not (fn2-run-layout-internal-p (fn2-run-builds-schema b fn2-run-builds))) 1)',s)
  for file,fn in [('checkpoint-metadata.lisp','fn2-checkpoint-metadata-page-for-build'),
                  ('checkpoint-metadata-page.lisp','fn2-checkpoint-metadata-page-bind'),
                  ('checkpoint-metadata-page.lisp','fn2-checkpoint-metadata-page-complete-p')]:
   self.assertEqual(len(calls(form(file,'defun',fn),'fn2-checkpoint-metadata-role')),1)
class ArchiveWorkSource(unittest.TestCase):
 def test_page_wait_precedes_build_progress(self):
  n=form('event-archive-work.lisp','fn2-event-archive-operation','fn2-event-archive-work')
  consume=calls(n,'fn2-checkpoint-metadata-page-consume')[0].node
  work=calls(n,'fn2-run-build-work')[0].node
  self.assertLess(consume.start,work.start)
  self.assertIn('(if (eq code :ok) :more code)',text('event-archive-work.lisp',n))
  self.assertTrue(has(n,'fn2-checkpoint-metadata-promote'))
  self.assertTrue(has(n,'fn2-checkpoint-metadata-page-complete-p'))
  self.assertNotIn('(fn2-run-build-promote',text('event-archive-work.lisp',n))
 def test_shared_physical_bind_is_the_only_page_path(self):
  n=form('event-archive-work.lisp','fn2-event-archive-operation','fn2-event-archive-page-bind')
  self.assertTrue(has(n,'fn2-event-archive-builderp'))
  self.assertEqual(len(calls(n,'fn2-checkpoint-metadata-page-bind')),1)
  self.assertNotIn('fn2-checkpoint-page-put',text('event-archive-work.lisp',n))
 def test_finish_derives_full_coverage_and_actual_reader_terminal(self):
  n=form('event-archive-work.lisp','fn2-event-archive-operation','fn2-event-archive-finish')
  s=text('event-archive-work.lisp',n)
  for name in ['fn2-event-read-ownerp','fn2-mk-size','fn2-run-builds-entries','fn2-csnapshot-cut-event','fn2-run-build-finish']:
   self.assertTrue(has(n,name),name)
  self.assertIn('*fn2-event-read-phase-complete*',s)
  self.assertTrue(all(x.low.startswith('fn2-') for x in n.items[2].items))
 def test_staging_refuses_a_frozen_page_writer(self):
  n=form('event-archive-producer.lisp','fn2-event-archive-operation','fn2-event-archive-stage')
  self.assertIn('(equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 0)',text('event-archive-producer.lisp',n))
class ArchiveControlSource(unittest.TestCase):
 def test_header_binds_cut_seal_namespace_and_manifest_ref(self):
  n=form('event-archive-format.lisp','deflayout','fn2-event-archive-header')
  s=text('event-archive-format.lisp',n)
  for field in ['(history (:id history))','(incarnation (:id incarnation))','(cut-commit (:id commit))',
                '(cut-event (:id event))','(cut-seal :digest)','(first-event (:id event))','(last-event (:id event))',
                '(member-runs :varint)','(manifest-entries :varint)']:
   self.assertIn(field,s)
  self.assertIn('(fn2-format-prefix "MANIFEST-" *fn2-format-ref*)',s)
 def test_fresh_constructor_derives_actual_base_and_retains_active0(self):
  n=form('event-archive-control.lisp','fn2-event-archive-operation','fn2-event-archive-fresh-start')
  self.assertTrue(has(n,'fn2-event-archive-begin'))
  s=text('event-archive-control.lisp',n)
  self.assertIn('(equal (fn2-commit-root-base-batch 0 fn2-commit-root) 0)',s)
  self.assertIn('(equal (fn2-commit-root-base-event 0 fn2-commit-root) 0)',s)
  self.assertIn('(equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-idle*)',s)
  puts=calls(n,'fn2-event-archive-put')
  self.assertEqual([x.node.items[1].low for x in puts],['1'])
 def test_member_capture_requires_real_completed_page_and_exact_C_seal(self):
  n=form('event-archive-control.lisp','fn2-event-archive-operation','fn2-event-archive-capture-member')
  for name in ['fn2-event-archive-ownerp','fn2-event-archive-builderp','fn2-event-read-ownerp',
               'fn2-checkpoint-metadata-page-complete-p','fn2-checkpoint-metadata-page-consume','fn2-event-source-seal']:
   self.assertTrue(has(n,name),name)
  self.assertLess(calls(n,'fn2-checkpoint-metadata-page-complete-p')[0].node.start,calls(n,'fn2-event-source-seal')[0].node.start)
  s=text('event-archive-control.lisp',n)
  self.assertIn('(member-unit (fn2-run-writers-unit writer fn2-run-writers))',s)
  self.assertIn('(member-allocation (fn2-run-writers-counter writer fn2-run-writers))',s)
  self.assertTrue(all(x.low.startswith('fn2-') for x in n.items[2].items))
  self.assertNotIn('root-source-complete',s)
 def test_pending_hashes_are_separate_and_no_root_hold_is_discharged(self):
  s=source('event-archive-state.lisp')
  self.assertIn('(48)',s);self.assertIn('(* r 24)',s)
  s=source('event-archive-control.lisp')
  self.assertNotIn('(fn2-event-archive-put 0',s)
  self.assertNotIn('(fn2-event-archive-copy-digest 0',s)
  for name in ['fn2-alloc-edge-drop','fn2-pool-release','fn2-alloc-free','fn2-checkpoint-refs-put']:
   self.assertNotIn('('+name,s)
class ArchiveManifestSource(unittest.TestCase):
 def test_begin_uses_only_captured_completed_member_and_same_build(self):
  n=form('event-archive-manifest.lisp','fn2-event-archive-operation','fn2-event-archive-manifest-begin')
  self.assertTrue(has(n,'fn2-event-archive-ownerp'))
  s=text('event-archive-manifest.lisp',n)
  self.assertIn('*fn2-event-archive-phase-member-complete*',s)
  self.assertIn('*fn2-run-build-phase-done*',s)
  start=calls(n,'fn2-run-build-start')[0].node
  self.assertEqual(start.items[1].low,'b');self.assertEqual(start.items[2].low,'10')
  self.assertFalse(has(n,'fn2-checkpoint-metadata-manifest-put'))
  self.assertFalse(has(n,'fn2-checkpoint-metadata-set-ordinal'))
 def test_emit_preserves_exact_coverage_and_shared_schema10_binder(self):
  n=form('event-archive-manifest.lisp','fn2-event-archive-operation','fn2-event-archive-manifest-emit')
  for name in ['fn2-event-archive-builderp','fn2-event-archive-load-digest','fn2-manifest-bind-unfiltered','fn2-run-build-add']:
   self.assertTrue(has(n,name),name)
  s=text('event-archive-manifest.lisp',n)
  self.assertIn('(equal (fn2-event-archive-first-event 1 fn2-event-archive) 1)',s)
  self.assertIn('(equal (fn2-event-archive-last-event 1 fn2-event-archive) (fn2-event-archive-member-entries 1 fn2-event-archive))',s)
  self.assertIn('(if (eq code :ok) (fn2-event-archive-set-manifest-entries 1 1',s)
 def test_finish_and_capture_require_actual_manifest_count_and_page(self):
  finish=form('event-archive-manifest.lisp','fn2-event-archive-operation','fn2-event-archive-manifest-finish')
  self.assertTrue(has(finish,'fn2-run-build-finish'))
  capture=form('event-archive-manifest.lisp','fn2-event-archive-operation','fn2-event-archive-capture-manifest')
  self.assertTrue(has(capture,'fn2-checkpoint-metadata-page-consume'))
  s=text('event-archive-manifest.lisp',capture)
  self.assertIn('(manifest-height (fn2-run-builds-height b fn2-run-builds))',s)
  self.assertIn('*fn2-event-archive-phase-header*',s)
  self.assertNotIn('root-source-complete',s)
 def test_schema10_height_is_level_count_at_both_captures(self):
  n=form('event-archive-control.lisp','fn2-event-archive-operation','fn2-event-archive-capture-member')
  self.assertIn('(member-height (fn2-run-builds-height b fn2-run-builds))',text('event-archive-control.lisp',n))
class ArchivePageKindSource(unittest.TestCase):
 def test_root3_class_is_exactly_manifest_and_internal_run_pages(self):
  n=form('checkpoint-page-header.lisp','defun','fn2-checkpoint-page-role-kind-p')
  cases=calls(n,'case')[0].node
  role3=next(x for x in cases.items[2:] if hasattr(x,'items') and x.items[0].low=='3')
  s=text('checkpoint-page-header.lisp',role3)
  for kind in ['*page-kind-manifest*','*page-kind-run-data*','*page-kind-run-index*']:
   self.assertIn(kind,s)
  self.assertEqual(s.count('(equal kind '),3)
  self.assertNotIn('checkpoint-descriptor',s)
 def test_actual_archive_worker_uses_schema_kind_and_verified_promotion(self):
  n=form('event-archive-work.lisp','fn2-event-archive-operation','fn2-event-archive-work')
  self.assertTrue(has(n,'fn2-checkpoint-metadata-page'))
  self.assertTrue(has(n,'fn2-checkpoint-metadata-page-consume'))
  self.assertTrue(has(n,'fn2-checkpoint-metadata-promote'))
  wrapper=form('checkpoint-metadata.lisp','defun','fn2-checkpoint-metadata-page')
  self.assertTrue(has(wrapper,'fn2-run-layout-page-kind'))
  bind=form('checkpoint-metadata-page.lisp','defun','fn2-checkpoint-metadata-page-bind')
  self.assertTrue(has(bind,'fn2-checkpoint-metadata-writerp'))
  self.assertTrue(has(bind,'fn2-checkpoint-metadata-role'))
class ArchiveHeaderSource(unittest.TestCase):
 def test_reservation_derives_actual_ledger_ordinal_and_page_counts(self):
  n=form('event-archive-header.lisp','fn2-event-archive-operation','fn2-event-archive-header-reserve')
  for name in ['fn2-event-archive-ownerp','fn2-checkpoint-root1-workspaces','fn2-checkpoint-construction-reserve']:
   self.assertTrue(has(n,name),name)
  s=text('event-archive-header.lisp',n)
  self.assertIn('(equal (+ ordinal 1) pages)',s)
  self.assertIn('(header-ordinal ordinal)',s)
  self.assertIn('(source-pages pages)',s)
  self.assertTrue(all(x.low.startswith('fn2-') for x in n.items[2].items))
 def test_bounded_zero_and_actual_generated_codec(self):
  zero=form('event-archive-header.lisp','fn2-event-archive-operation','fn2-event-archive-header-zero-step')
  self.assertIn('(min 4096 (- *fn2-format-page-size* at))',text('event-archive-header.lisp',zero))
  pack=form('event-archive-header.lisp','fn2-event-archive-operation','fn2-event-archive-header-pack')
  self.assertTrue(has(pack,'fn2-event-archive-header-bind'))
  self.assertTrue(has(pack,'fn2-event-archive-header-encode'))
  self.assertEqual(len(calls(pack,'fn2-event-archive-header-bind')[0].node.items)-1,27)
  self.assertIn(':cut-seal',text('event-archive-header.lisp',pack))
  self.assertIn(':manifest',text('event-archive-header.lisp',pack))
  self.assertIn('(if (eq code :ok) :format code)',text('event-archive-header.lisp',pack))
 def test_bind_and_completion_use_real_shared_worker(self):
  bind=form('event-archive-header.lisp','fn2-event-archive-operation','fn2-event-archive-header-bind-page')
  self.assertTrue(has(bind,'fn2-checkpoint-page-begin'))
  self.assertIn('*fn2-event-archive-phase-bound*',text('event-archive-header.lisp',bind))
  done=form('event-archive-header.lisp','fn2-event-archive-operation','fn2-event-archive-header-complete')
  self.assertTrue(has(done,'fn2-checkpoint-page-completed-extent-p'))
  writes=calls(done,'fn2-checkpoint-refs-put')
  self.assertEqual(len(writes),1)
  self.assertLess(calls(done,'fn2-checkpoint-page-completed-extent-p')[0].node.start,writes[0].node.start)
  s=text('event-archive-header.lisp',done)
  for field in ['epoch','allocation','page-kind','history','incarnation','encoded-length']:
   self.assertIn('(fn2-checkpoint-page-verified-'+field,s)
  self.assertIn('(equal (fn2-checkpoint-refs-root-source-complete r fn2-checkpoint-refs) 0)',s)
  self.assertIn('(equal pages (fn2-checkpoint-metadata-ordinal 0 fn2-checkpoint-metadata))',s)
  self.assertNotIn('fn2-alloc-edge-drop',s)
  self.assertNotIn('fn2-pool-release',s)
 def test_operation_names_do_not_collide_with_generated_state_accessors(self):
  state=form('event-archive-state.lisp','defcolumns','fn2-event-archive')
  getters={'fn2-event-archive-'+f.items[0].low for f in state.items[2].items}
  for n in __import__('lisp_rewrite').match('(fn2-event-archive-operation ?name ?*body)',__import__('lisp_rewrite').parse(source('event-archive-header.lisp')).forms,deep=False):
   self.assertNotIn(n.captures['name'].low,getters)
 def test_source_admission_preserves_the_actual_root1_manifest_builder(self):
  n=form('event-archive-producer.lisp','defun','fn2-event-archive-sourcep')
  self.assertIn('(equal (fn2-checkpoint-metadata-manifest-build 0 fn2-checkpoint-metadata-manifest) *fn2-checkpoint-manifest-build*)',text('event-archive-producer.lisp',n))
if __name__=='__main__':unittest.main()
