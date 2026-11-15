"""Reviewed proof projection and truthful cold member contract connection."""
from pathlib import Path
import json,hashlib,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'));import reader_foundation_batch as b
class FoundationBatch(unittest.TestCase):
 def test_exact_safe_six_and_four_providers(self):
  for name in b.SAFE+b.HELPERS:
   path='books/'+name+'.lisp';actual=(ROOT/path).read_text()
   self.assertEqual(actual,b.source(ROOT,b.ROOT_SOURCE,path),name)
   if name in b.SAFE:b.validate_safe(b.source(ROOT,b.BASE,path),actual)
 def test_receipt_and_idempotent_narrow_projection(self):
  receipt=json.loads((ROOT/'tools/fixtures/reader-foundation-batch.json').read_text())
  for name,digest in receipt['files'].items():self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest,name)
  for name,transform in [('checkpoint-tickets',b.tickets),('checkpoint-installation-coordinator',b.coordinator)]:
   path='books/'+name+'.lisp';before=b.source(ROOT,b.BASE,path);reference=b.source(ROOT,b.ROOT_SOURCE,path);now=(ROOT/path).read_text()
   self.assertEqual(transform(before,reference),now)
   self.assertEqual(transform(now,reference),now)
   for key,definition in b.definitions(before).items():self.assertEqual(b.norm(definition),b.norm(b.definitions(now)[key]),key)
 def test_native_ownership_and_resize_hook_preserved(self):
  for name in ['checkpoint-tickets','checkpoint-installation-coordinator']:
   text=(ROOT/'books'/f'{name}.lisp').read_text()
   self.assertIn('fn2-checkpoint-construction-native-p',text)
  self.assertIn('(fn2-columns-extra-resize-frames fn2-extents)',(ROOT/'books/commit-alloc.lisp').read_text())
  for name in ['alloc','arms','event-read-state','event-read-source','event-read-verify','pool-digest']:
   self.assertEqual((ROOT/'books'/f'{name}.lisp').read_text(),b.source(ROOT,b.BASE,'books/'+name+'.lisp'),name)
 def test_member_runtime_and_original_claim_retained(self):
  path='books/checkpoint-member.lisp';before=b.source(ROOT,b.BASE,path);now=(ROOT/path).read_text()
  self.assertEqual(now,b.member(b.source(ROOT,b.ROOT_SOURCE,path)))
  for name,old in b.definitions(before).items():self.assertEqual(b.norm(old),b.norm(b.definitions(now)[name]),name)
  self.assertNotIn('(fn2-pool-preserves fn2-checkpoint-installation-pack-member',now)
  self.assertIn('(defcolumns-guarded-contracts fn2-checkpoint-installation-pack-member',now)
  self.assertIn('(include-book "columns-carrier-contracts")',now)
  self.assertIn('(hyps (fn2-columns-carrier-hyps carriers))',now)
  self.assertIn('(old (car (fn2-columns-preservation-facts name (cons name args) (list (car specs)) hyps nil)))',now)
  self.assertIn('(defthm-owed ,(cadr old) ,args ,(caddr old)',now)
  self.assertIn('(fn2-columns-preserves (caar carriers) name args nil hyps (cdr specs)',now)
 def test_actual_step_uses_guarded_four_only(self):
  text=(ROOT/'books/checkpoint-installation-coordinator.lisp').read_text()
  proof=b.unique(text,'(fn2-core-preserves fn2-checkpoint-installation-step ?*body)');proof=text[proof.start:proof.end]
  for suffix in ['fields-type','fields-wfp','pool-type','pool-wfp']:
   self.assertIn('fn2-checkpoint-installation-pack-member-'+suffix+'-under-guard',proof)
  # The actual CORE contracts supply readonly TYPE/WFP; this is not a new
  # runtime validator. Existing child facts are the bridge to the stored guard.
  core=(ROOT/'books/core.lisp').read_text()
  self.assertIn('(implies (fn2-corep fn2-core) (,pred (,field fn2-core)))',core)
  self.assertIn('(implies (fn2-core-wfp fn2-core) (,wfp (,field fn2-core)))',core)
  node=b.unique(text,'(defun fn2-checkpoint-installation-step ?*body)');step=text[node.start:node.end]
  prefix=step[:step.index('(fn2-checkpoint-installation-pack-member')]
  for writer in ['fn2-fields-set-','fn2-fields-put','fn2-pool-write','fn2-pool-reset','fn2-checkpoints-set-','fn2-checkpoint-refs-set-','fn2-checkpoint-bytes-set-']:
   self.assertNotIn(writer,prefix)
 def test_ground_refutation_and_positive_evidence_explicit(self):
  for name in ['checkpoint-member-readonly-removal','checkpoint-member-interface-unit']:
   self.assertEqual((ROOT/'tests'/f'{name}.lisp').read_text(),b.source(ROOT,b.ROOT_SOURCE,'tests/'+name+'.lisp'))
  negative=(ROOT/'tests/checkpoint-member-readonly-removal.lisp').read_text()
  self.assertIn('(fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)',negative)
  self.assertIn('(fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)',negative)
  self.assertIn('(not (fn2-checkpointsp fn2-checkpoints))',negative)
  self.assertIn('(not (fn2-fieldsp (mv-nth 2 answer)))',negative)
  self.assertIn('(defun-nx',negative)
  positive=(ROOT/'tests/checkpoint-member-interface-unit.lisp').read_text()
  self.assertIn('(include-book "checkpoint-member-readonly-removal")',positive)
  self.assertIn('(and ,guard',positive)
  self.assertIn('tests/checkpoint-member-interface-unit',(ROOT/'Makefile').read_text())
if __name__=='__main__':unittest.main()
