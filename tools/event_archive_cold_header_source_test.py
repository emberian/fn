"""Source controls for the actual root3 envelope/sole-layout reader slice."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def read(name):return (ROOT/'books'/name).read_text()
def calls(s,p):return lr.match(p,lr.parse(s).forms)
class ColdHeader(unittest.TestCase):
 def test_shared_authentication_precedes_sole_body_decoder(self):
  s=read('event-archive-cold-header.lisp')
  auth=calls(s,'(fn2-checkpoint-restore-reader-format-step ?*args)')
  decode=calls(s,'(fn2-event-archive-header-decode ?*args)')
  self.assertEqual(len(auth),1);self.assertEqual(len(decode),1)
  self.assertLess(auth[0].node.start,decode[0].node.start)
  self.assertEqual(auth[0].node.items[1].low,'*fn2-commit-unit-bytes*')
  for name in ['fn2-format-run','fn2-checkpoint-map-header-decode','fn2-block-read-children']:
   self.assertFalse(calls(s,'('+name+' ?*args)'))
 def test_exact_source_and_namespace_checks(self):
  s=read('event-archive-cold-header.lisp')
  self.assertTrue(calls(s,'(fn2-event-archive-cold-source-bytes-p 0 c fn2-checkpoint-bytes fn2-checkpoint-restore-reader)'))
  for field in ['checkpoint','history','incarnation','cut-commit','cut-event','manifest-run','manifest-height','manifest-entries','manifest-storage-domain','manifest-page-kind','manifest-encoded-length']:
   self.assertIn('*fn2-event-archive-header-field-'+field+'*',s)
  for field in ['physical-unit','writer-epoch','allocation']:
   self.assertTrue(calls(s,'(fn2-checkpoint-refs-'+field+' r fn2-checkpoint-refs)'))
  self.assertIn('(equal next (+ *fn2-event-archive-header-start* payload))',s)
 def test_only_discovery_never_complete_or_active(self):
  s=read('event-archive-cold-header.lisp')
  writes=calls(s,'(fn2-event-archive-put ?*args)')
  self.assertEqual(len(writes),1);self.assertEqual(writes[0].node.items[1].low,'1')
  self.assertIn('(phase *fn2-event-archive-phase-cold-header*)',s)
  self.assertNotIn('*fn2-event-archive-phase-complete*',s)
  self.assertIn('(source-tag 0) (source-generation 0)',s)
  self.assertIn('(equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-idle*)',s)
  self.assertEqual(len(calls(s,'(fn2-rec-fetch ?*args)')),2)
  self.assertTrue(calls(s,'(fn2-event-archive-cold-copy-descriptor 0 fn2-checkpoint-restore-reader fn2-event-archive)'))
 def test_member_header_id_and_manifest_key_are_terminal_event(self):
  producer=read('event-archive-producer.lisp');work=read('event-archive-work.lisp');manifest=read('event-archive-manifest.lisp')
  self.assertTrue(calls(producer,'(fn2-run-build-start b *fn2-event-archive-schema* (fn2-csnapshot-cut-event 0 fn2-csnapshot) ?*args)'))
  self.assertTrue(calls(producer,'(equal (fn2-run-builds-run b fn2-run-builds) (fn2-csnapshot-cut-event 0 fn2-csnapshot))'))
  self.assertTrue(calls(manifest,'(fn2-manifest-bind-unfiltered base *fn2-event-archive-schema* (fn2-event-archive-last-event 1 fn2-event-archive) ?*args)'))
  self.assertTrue(calls(manifest,'(fn2-run-build-start b 10 (fn2-event-archive-checkpoint 1 fn2-event-archive) ?*args)'))
  self.assertTrue(calls(work,'(if (equal (fn2-run-builds-schema *fn2-checkpoint-source-build* fn2-run-builds) *fn2-event-archive-schema*) (fn2-event-archive-cut-event 1 fn2-event-archive) (fn2-event-archive-checkpoint 1 fn2-event-archive))'))
 def test_private_source_rebinds_descriptor_and_exact_physical_subject(self):
  s=read('event-archive-cold-source.lisp')
  self.assertTrue(calls(s,'(fn2-event-archive-cold-descriptor-current-p 0 c fn2-checkpoint-bytes fn2-event-archive)'))
  for field in ['checkpoint','history','incarnation','cut-commit','cut-event']:
   self.assertTrue(calls(s,'(equal (fn2-checkpoints-'+field+' c fn2-checkpoints) (fn2-event-archive-'+field+' 1 fn2-event-archive))'))
  for field,archive in [('physical-unit','unit'),('writer-epoch','epoch'),('allocation','allocation')]:
   self.assertTrue(calls(s,'(equal (fn2-checkpoint-refs-'+field+' r fn2-checkpoint-refs) (fn2-event-archive-header-'+archive+' 1 fn2-event-archive))'))
  self.assertNotIn('source-generation',s);self.assertNotIn('source-tag',s)
  self.assertNotIn('*fn2-event-archive-phase-complete*',s)
 def test_header_workspace_is_captured_from_actual_reader(self):
  s=read('event-archive-cold-header.lisp')
  self.assertTrue(calls(s,'(slot (fn2-checkpoint-restore-reader-slot 0 fn2-checkpoint-restore-reader))'))
  self.assertTrue(calls(s,'(gen (fn2-checkpoint-restore-reader-gen 0 fn2-checkpoint-restore-reader))'))
  self.assertTrue(calls(s,'(header-slot slot)'));self.assertTrue(calls(s,'(header-gen gen)'))
if __name__=='__main__':unittest.main()
