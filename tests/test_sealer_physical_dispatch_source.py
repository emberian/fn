"""Actual sealer loader source controls; no ACL2 admission/runtime claim."""
from pathlib import Path
import sys,unittest,copy
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for v in x:yield from walk(v)
def tree(name):return [read_sexp(x) for x in forms((ROOT/'books'/name).read_text())]
def calls(f,name):return [x for x in walk(f) if x and x[0]==name]
class SealerPhysicalSource(unittest.TestCase):
 def test_actual_merge_miss_uses_one_shared_loader(self):
  fs=tree('machines-c-sealer-events.lisp');arms=next(f for f in fs if isinstance(f,list) and f[:2]==['defmachine-arms','fn2-sealer'])
  self.assertEqual(len(calls(arms,'fn2-run-page-bind')),1)
  self.assertEqual(len(calls(arms,'fn2-run-page-step')),1)
  self.assertEqual(len(calls(arms,'fn2-run-page-read')),1)
  self.assertTrue(any(x and x[0]==':issue' and calls(x,'fn2-run-page-read') for x in walk(arms)))
  self.assertFalse(any(x and x[0]==':do' and calls(x,'fn2-run-page-read') for x in walk(arms)))
  self.assertTrue(any(x and x[0]==':miss' for x in walk(arms)))
 def test_no_pool_wait_holds_unadmitted_source(self):
  fs=tree('machines-c-sealer-events.lisp');arms=next(f for f in fs if isinstance(f,list) and f[:2]==['defmachine-arms','fn2-sealer'])
  self.assertEqual(len(calls(arms,'fn2-sealer-load-reserve-op')),1)
  self.assertTrue(calls(arms,'fn2-sealer-load-drain-op'))
  self.assertTrue(calls(arms,'fn2-sealer-load-member-release-op'))
  self.assertTrue(calls(arms,'fn2-run-page-release'))
  helper=next(f for f in tree('sealer-physical-loader.lisp') if isinstance(f,list) and f[:2]==['defun','fn2-sealer-load-reserve'])
  self.assertIn(['equal',['fn2-seals-phase','0','fn2-seals'],'*fn2-seal-phase-idle*'],list(walk(helper)))
  self.assertEqual(len(calls(helper,'fn2-run-load-region-reserve')),1)
  self.assertFalse(calls(helper,'fn2-seal-start'))
 def test_actual_source_geometry_and_foreign_owner_rejection(self):
  f=next(f for f in tree('sealer-physical-loader.lisp') if isinstance(f,list) and f[:2]==['defun','fn2-sealer-load-owner'])
  for name in ('cbase','sbase','rbase'):
   self.assertIn(['equal',['fn2-ranges-'+name,'g','fn2-ranges'],['fn2-seals-'+name,'0','fn2-seals']],list(walk(f)))
  self.assertTrue(calls(f,'fn2-run-load-range-miss'))
  self.assertTrue(calls(f,'fn2-run-load-ownerp'))
  self.assertFalse(calls(f,'fn2-run-cache-lookup'))
 def test_readiness_keeps_active_seal_and_capacity_distinct(self):
  fs=tree('machines-c-sealer-events.lisp')
  self.assertTrue(calls(tree('sealer-physical-loader.lisp'),'fn2-sealer-copy-roomp'))
  self.assertTrue(calls(fs,'fn2-sealer-load-status'))
  kind=tree('machines-c-sealer-kind.lisp')
  self.assertIn([':read-result',[':wake']],list(walk(kind)))
 def test_retired_physical_row_uses_exact_catalog_promise(self):
  f=next(f for f in tree('sealer-physical-loader.lisp') if isinstance(f,list) and f[:2]==['defun','fn2-sealer-load-retire'])
  self.assertEqual(len(calls(f,'fn2-checkpoint-summary-retire-row')),1)
  self.assertFalse(calls(f,'fn2-run-cache-drop'))
  self.assertFalse(calls(f,'fn2-pool-release'))
  self.assertIn(['equal',['fn2-csnapshot-phase','0','fn2-csnapshot'],'*fn2-csnapshot-phase-held*'],list(walk(f)))
  fixture=tree('../tests/sealer-physical-loader-unit.lisp')
  self.assertTrue(calls(fixture,'fn2-checkpoint-cbase-promised-p'))
  self.assertTrue(calls(fixture,'fn2-checkpoint-summary-lease-current-p'))
  self.assertEqual(len(calls(fixture,'fn2-sealer-load-retire')),3)
 def test_foreign_source_octets_cross_real_owned_copy(self):
  f=next(f for f in tree('sealer.lisp') if isinstance(f,list) and f[:2]==['defun','fn2-seal-merge-add'])
  copy=calls(f,'fn2-run-entry-rehome-step')
  self.assertEqual(len(copy),1)
  for field in ('source-kind','source-slot','source-gen','okind','oslot','ogen'):
   self.assertTrue(calls(copy,'fn2-seals-'+field))
  self.assertTrue(calls(f,'fn2-run-build-add'))
  ready=list(walk(f))
  self.assertIn(['equal',['fn2-seals-copy-live','0','fn2-seals'],'1'],ready)
  helper=tree('sealer-physical-loader.lisp')
  self.assertTrue(calls(helper,'fn2-sealer-copy-class-need'))
  self.assertTrue(calls(tree('machines-c-sealer-events.lisp'),'fn2-sealer-copy-release-op'))
 def test_copy_control_uses_real_merge_encoder_and_decoder(self):
  f=next(f for f in tree('../tests/sealer-physical-loader-unit.lisp') if isinstance(f,list) and f[:2]==['defun','fn2-sealer-physical-copy-unit'])
  self.assertEqual(len(calls(f,'fn2-seal-merge-add')),1)
  self.assertEqual(len(calls(f,'fn2-spl-copy-drive')),1)
  self.assertEqual(len(calls(f,'fn2-run-layout-decode')),1)
  self.assertEqual(len(calls(f,'fn2-pool-read')),2)
  self.assertIn(['equal','byte','120'],list(walk(f)))
  self.assertIn(['equal','original','120'],list(walk(f)))
 def test_observer_closes_after_continuations_and_snapshot_waits(self):
  fs=tree('machines-c-sealer-events.lisp')
  self.assertTrue(calls(fs,'fn2-c-source-read-acquire'))
  self.assertTrue(calls(fs,'fn2-sealer-source-clear-op'))
  self.assertTrue(calls(fs,'fn2-sealer-source-quiescent-p'))
  snapshot=tree('c-snapshot.lisp')
  self.assertTrue(calls(snapshot,'fn2-csnapshot-sealer-quiescent-p'))
  self.assertTrue(calls(snapshot,'fn2-c-source-observers-live'))
  self.assertTrue(calls(snapshot,'fn2-seals-phase'))
  # Physical admission occurs only in the actual plan's NEED-LOADER case.
  f=next(f for f in tree('sealer.lisp') if isinstance(f,list) and f[:2]==['defun','fn2-seal-start'])
  self.assertTrue(calls(f,'fn2-seal-physical-inputs'))
  self.assertTrue(any(x and x[0]=='mv' and ':need-loader' in x for x in walk(f)))
if __name__=='__main__':unittest.main()
