"""Prepared source-reader physical fixture wiring; no execution/admission claim."""
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class PhysicalFixture(unittest.TestCase):
 def test_actual_codec_adoption_then_next_held_root1_reader(self):
  s=(ROOT/'tests/checkpoint-source-reader-physical-unit.lisp').read_text()
  calls=('fn2-rpl-rebuild token','fn2-rpl-cold-admission','fn2-rpl-apply 32','fn2-csnapshot-begin','fn2-rsr-reserve next-token','fn2-rsr-descriptor-begin next-token','fn2-rsr-begin next-token','fn2-rsr-drive 512')
  body=s.split('(defun fn2-rsr-body',1)[1]
  at=0
  for call in calls:
   at=body.index(call,at)+len(call)
  self.assertIn('SYNTHETIC',s)
  self.assertIn('UNEXECUTED',s)
  self.assertIn('(include-book "../books/executor")',s)
  for call in ('*fn2-checkpoint-master-kind*','fn2-machine-kind-base kind','fn2-checkpoint-master-row-generation owner','fn2-exec-genesis-row owner','fn2-csnapshot-begin kind owner gen'):
   self.assertIn(call,s)
 def test_no_seeded_ready_and_actual_op_completion(self):
  s=(ROOT/'tests/checkpoint-source-reader-physical-unit.lisp').read_text()
  self.assertNotIn('(phase *fn2-run-load-phase-ready*)',s)
  self.assertNotIn('fn2-run-cache-install',s)
  for call in ('fn2-rpl-complete-read op ogen','fn2-rsr-step 0','fn2-rsr-attached token 1','fn2-rsr-attached token 0','*fn2-storage-extent-units*','fn2-rpl-cache-emptyp'):
   self.assertIn(call,s)
 def test_terminal_uses_real_page_worker_and_requires_full_detach(self):
  s=(ROOT/'tests/checkpoint-source-reader-physical-unit.lisp').read_text()
  for call in ('fn2-checkpoint-page-worker-run target 4096','fn2-checkpoint-page-take fn2-core','fn2-checkpoint-page-accept-return kind owner gen','fn2-rsr-consume 4096','fn2-rsr-complete-write','fn2-harvest-one','fn2-checkpoint-source-reader-detachedp','*fn2-checkpoint-metadata-manifest-phase-complete*','*fn2-checkpoint-source-phase-done*','(equal writes (* 2 *fn2-storage-extent-units*))'):
   self.assertIn(call,s)
  for fake in ('(phase *fn2-checkpoint-root1-phase-complete*)','(phase *fn2-checkpoint-page-phase-complete*)','(handoff *fn2-checkpoint-page-handoff-to-source*)','(phase *fn2-run-load-phase-ready*)'):
   self.assertNotIn(fake,s)
 def test_wrapper_projects_actual_declared_mutations(self):
  s=(ROOT/'tests/checkpoint-source-reader-physical-unit.lisp').read_text()
  self.assertIn('(cdr (assoc-eq target *fn2-checkpoint-root1-outputs*))',s)
  self.assertIn(',*fn2-checkpoint-root1-children* ,outputs',s)
if __name__=='__main__':unittest.main()
