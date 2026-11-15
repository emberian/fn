"""Source controls for the prepared actual 6KiB fixture; no ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
FILE=ROOT/'tests/cns-source-raw-reader-unit.lisp'
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x: yield from walk(y)
def body(name):
 return next(x for f in forms(FILE.read_text()) for x in walk(read_sexp(f)) if x[:2]==['defun',name])
def calls(x,name):return [y for y in walk(x) if y and y[0]==name]
class RawReaderFixture(unittest.TestCase):
 def test_actual_capture_issue_and_completion_not_ready_seed(self):
  x=body('fn2-crr-read')
  sequence=['fn2-cns-source-issue-children','fn2-outbox-ack','fn2-crr-input','fn2-post-result','fn2-harvest-next','fn2-pool-complete-in','fn2-cns-source-harvest','fn2-b-read-pin-harvest','fn2-op-finish']
  text=FILE.read_text();start=text.index('(defun fn2-crr-read');end=text.index('(defun fn2-crr-verify')
  offsets=[text.index('('+name,start,end) for name in sequence]
  self.assertEqual(offsets,sorted(offsets))
  for name in sequence:self.assertTrue(calls(x,name),name)
  self.assertFalse(calls(x,'fn2-cns-sources-put'))
  for name in ('fn2-cns-source-operations-live','fn2-cns-source-operations-generation','fn2-cns-source-operations-source-row','fn2-alloc-edge-matchesp','fn2-extents-outstanding-io','fn2-extents-promised-read'):
   self.assertTrue(calls(x,name),name)
 def test_real_hashes_and_whole_antecedent(self):
  x=body('fn2-cns-source-raw-reader-unit-body')
  self.assertEqual(len(calls(x,'fn2-block-hash-into')),4)
  self.assertEqual(len(calls(x,'fn2-digest-store')),4)
  self.assertEqual(len(calls(x,'fn2-cns-source-capture-children')),1)
  for name in ('fn2-pool-semanticp','fn2-ops-semanticp','fn2-cns-source-heldp','fn2-cns-source-hash-finish'):
   self.assertTrue(calls(x,name),name)
  self.assertIn('(fn2-crr-mv (and H',FILE.read_text())
 def test_actual_small_control_window_is_reused(self):
  x=body('fn2-crr-copy')
  self.assertTrue(calls(x,'fn2-pool-reset'))
  self.assertTrue(calls(x,'fn2-crr-bytes-equal'))
  self.assertTrue(calls(x,'fn2-cns-source-hash-update'))
  nexts=calls(x,'fn2-cns-source-next-children')
  self.assertEqual(len(nexts),1)
  self.assertEqual(nexts[0][9:12],['0','1024','5'])
  self.assertIn('(equal (fn2-pool-cap output fn2-pool) 4096)',FILE.read_text())
 def test_bounded_actual_source_hash_and_stale_controls(self):
  self.assertTrue(calls(body('fn2-crr-verify'),'fn2-cns-source-raw-step-children'))
  text=FILE.read_text()
  for required in ('(<= after (+ before 1024))','(eq stale-finish :stale)','(eq stale-next :bad)','(eq oldoff :bad)','(eq stale-final :bad)','(equal (+ n0 n1) 6144)','(eq output-hash :ok)'):
   self.assertIn(required,text)
 def test_actual_arities_and_literal_body_mv_shapes(self):
  defs={};outputs={}
  for p in list((ROOT/'books').glob('*.lisp'))+[FILE]:
   for f in forms(p.read_text()):
    try:tree=read_sexp(f)
    except (ValueError,IndexError):continue
    for a in walk(tree):
     if len(a)>2 and a[0]=='defun' and isinstance(a[1],str) and isinstance(a[2],list):
      defs[a[1]]=len(a[2]);counts={len(y)-1 for y in walk(a[3:]) if y and y[0]=='mv'}
      if len(counts)==1:outputs[a[1]]=next(iter(counts))
  actual=0;bindings=0
  for f in forms(FILE.read_text()):
   x=read_sexp(f)
   for a in walk(x[3:] if x and x[0]=='defun' else x):
    if a and isinstance(a[0],str) and a[0] in defs:
     actual+=1;self.assertEqual(len(a)-1,defs[a[0]],a[0])
    if len(a)==2 and isinstance(a[0],list) and a[0] and a[0][0]=='mv' and isinstance(a[1],list) and a[1] and isinstance(a[1][0],str) and a[1][0] in outputs:
     bindings+=1;self.assertEqual(len(a[0])-1,outputs[a[1][0]],a[1][0])
  self.assertGreater(actual,80);self.assertGreater(bindings,30)
if __name__=='__main__':unittest.main()
