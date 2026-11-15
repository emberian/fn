"""Source-only successor observer composition controls, not ACL2 admission."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
FILES=[ROOT/'books/machines-c-successor.lisp',ROOT/'books/machines-c-bind.lisp']
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def parsed(p):return [read_sexp(f) for f in forms(p.read_text())]
def function(n):return next(x for p in FILES for f in parsed(p) for x in walk(f) if x[:2]==['defun',n])
def calls(x,n):return [a for a in walk(x) if a and a[0]==n]
class SuccessorObserver(unittest.TestCase):
 def test_exact_receipt_precedes_same_actual_resolver(self):
  x=function('fn2-succ-resolve-observed');nodes=list(walk(x))
  self.assertEqual(len(calls(x,'fn2-succ-source-acquire')),1)
  self.assertEqual(len(calls(x,'fn2-succ-resolve')),1)
  self.assertEqual(len(calls(x,'fn2-succ-source-close')),1)
  text=FILES[0].read_text().split('(defun fn2-succ-resolve-observed',1)[1]
  self.assertLess(text.index('(fn2-succ-source-acquire'),text.index('(fn2-succ-resolve tx'))
  self.assertIn("(member-eq code '(:more :miss))",text)
  self.assertIn('(equal (fn2-succ-txns-ri tx fn2-succ-txns) *fn2-succ-slots*)',text)
  self.assertIn('(equal (fn2-succ-txns-rstate tx fn2-succ-txns) *fn2-succ-resolve-fresh*)',text)
 def test_close_checks_current_before_sanitizing_then_exact_release(self):
  x=function('fn2-succ-source-close')
  for n in ('fn2-c-source-reader-current-p','fn2-succ-clear-ref-rows','fn2-run-cursors-set-phase','fn2-c-source-reader-release','fn2-succ-txns-set-source-receipt'):
   self.assertTrue(calls(x,n),n)
  text=FILES[0].read_text().split('(defun fn2-succ-source-close',1)[1].split('(fn2-idc-fn-shape',1)[0]
  self.assertLess(text.index('(fn2-c-source-reader-current-p'),text.index('(fn2-succ-clear-ref-rows'))
  self.assertLess(text.index('(fn2-succ-clear-ref-rows'),text.index('(fn2-c-source-reader-release'))
  self.assertIn('(<= (+ b0 *fn2-idc-stride*) (fn2-fields-rows fn2-fields))',text)
 def test_same_scalar_materialization_and_borrowed_value_refusal(self):
  scalar=function('fn2-succ-copy-scalar-row')
  for field in ('ref-slot','ref-gen','ref-off','ref-len'):self.assertIn([field,'0'],list(walk(scalar)))
  x=function('fn2-succ-resolve-step')
  self.assertTrue(calls(x,'fn2-succ-source-values-scalar-p'))
  self.assertTrue(calls(x,'fn2-succ-copy-scalar-rows'))
  self.assertFalse(calls(x,'fn2-succ-copy-rows'))
 def test_abandoned_release_cannot_erase_a_live_receipt(self):
  self.assertTrue(calls(function('fn2-succ-release'),'fn2-succ-txns-source-receipt'))
  x=function('fn2-succ-release-observed')
  self.assertTrue(calls(x,'fn2-succ-source-close'))
  self.assertTrue(calls(x,'fn2-succ-release'))
  # Restart writes keep the same live receipt until actual cancellation.
  for n in ('fn2-succ-put','fn2-succ-touch'):
   self.assertFalse(calls(function(n),'fn2-succ-txns-set-source-receipt'))
 def test_actual_public_wrapper_and_outputs_stay_narrow(self):
  text=FILES[1].read_text()
  self.assertIn('(fn2-succ-wrap fn2-successor-resolve (tx budget)',text)
  self.assertIn('(fn2-succ-resolve-observed tx budget b0',text)
  self.assertIn('(fn2-succ-release-observed tx b0',text)
  for name in ('fn2-succ-resolve-observed','fn2-succ-release-observed'):
   final=function(name)[-1][-1]
   self.assertEqual(final[0],'mv',name)
   self.assertEqual(len(final)-1,8,name)
  for child in ('fn2-core-c-source-control','fn2-core-c-source-readers'):self.assertIn(child,text)
 def test_prepared_actual_wrapper_progress_cancel_and_error(self):
  text=(ROOT/'tests/successor-source-observer-unit.lisp').read_text()
  for name in ('fn2-successor-resolve','fn2-successor-release','fn2-c-source-writer-begin','fn2-c-source-writer-poll','fn2-succ-copy-scalar-row'):
   self.assertIn('('+name,text)
  self.assertNotIn('(ri *fn2-succ-slots*)',text)
  self.assertIn('(eq bypass :state)',text)
  self.assertIn('(eq writer :waiting)',text)
  self.assertIn('(eq poll :exclusive)',text)
  for mode in (':complete',':cancel',':error'):
   self.assertIn('(assert-event (fn2-successor-source-observer-unit '+mode+'))',text)
if __name__=='__main__':unittest.main()
