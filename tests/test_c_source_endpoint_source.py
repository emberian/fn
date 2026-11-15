"""Endpoint barrier source controls, not ACL2 admission or runtime evidence."""
from pathlib import Path
import copy,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def declarations(path):
 return [read_sexp(f) for f in forms((ROOT/path).read_text())]
def named(name):
 return next(f for p in ('books/c-source-observer.lisp','books/c-source-observer-state.lisp') for f in declarations(p) if isinstance(f,list) and len(f)>1 and f[1]==name)
def has(x,term):return term in list(walk(x))
class EndpointBarrier(unittest.TestCase):
 def test_existing_endpoint_requires_exact_saved_serial_before_writer_gate(self):
  f=named('fn2-c-source-reader-acquire-core');s=str(f)
  self.assertLess(s.index('fn2-c-source-reader-current-p'),s.index('*fn2-c-source-writer-phase-idle*'))
  self.assertTrue(has(f,['equal','expected-receipt','0']))
  current=named('fn2-c-source-reader-current-p')
  self.assertTrue(has(current,['equal',['fn2-c-source-readers-serial','endpoint','fn2-c-source-readers'],'receipt']))
  self.assertTrue(has(current,['posp','receipt']))
  mutant=copy.deepcopy(current)
  for x in walk(mutant):
   if x and x[0]=='fn2-c-source-readers-serial':x[0]='removed-serial'
  self.assertFalse(has(mutant,['equal',['fn2-c-source-readers-serial','endpoint','fn2-c-source-readers'],'receipt']))
 def test_new_receipt_is_monotone_checked_before_mutation(self):
  f=named('fn2-c-source-reader-acquire-core');s=str(f)
  self.assertTrue(has(f,['+','1',['fn2-c-source-control-next-receipt','0','fn2-c-source-control']]))
  self.assertLess(s.index('unsigned-byte-p'),s.index('fn2-c-source-readers-put'))
  self.assertTrue(has(f,['unsigned-byte-p','60','receipt']))
  self.assertTrue(has(f,['unsigned-byte-p','32','count']))
 def test_writer_full_receipt_and_pending_precedes_poll(self):
  f=named('fn2-c-source-writer-receipt-p')
  for arg,field in [('kind','writer-kind'),('owner','writer-owner'),('gen','writer-gen'),('token','writer-token'),('cutcommit','cut-commit'),('cutevent','cut-event')]:
   self.assertTrue(has(f,['equal',arg,['fn2-c-source-control-'+field,'0','fn2-c-source-control']]))
  begin=named('fn2-c-source-writer-begin')
  closing=next(x for x in walk(begin) if x and x[0]=='let')
  self.assertIn('*fn2-c-source-writer-phase-pending*',str(closing[1]))
  self.assertEqual(closing[2][0],'fn2-c-source-writer-poll')
 def test_release_exact_receipt_and_retained_wake(self):
  f=named('fn2-c-source-reader-release');s=str(f)
  self.assertLess(s.index('fn2-c-source-reader-current-p'),s.index('fn2-c-source-readers-put'))
  self.assertTrue(has(f,['equal','count','0']))
  self.assertIn('*fn2-c-source-writer-phase-pending*',s)
  self.assertIn('wake-pending',s)
  self.assertTrue(has(f,['serial','0']))
 def test_abort_only_pending_no_generic_end(self):
  f=named('fn2-c-source-writer-abort-pending')
  self.assertTrue(has(f,['equal',['fn2-c-source-control-phase','0','fn2-c-source-control'],'*fn2-c-source-writer-phase-pending*']))
  source=(ROOT/'books/c-source-observer.lisp').read_text()
  self.assertNotIn('(defun fn2-c-source-writer-end',source)
  self.assertNotIn('(defun fn2-c-source-writer-publish',source)
 def test_no_model_scan_in_served_leaves_and_invariant_transitions_named(self):
  for name in ('reader-acquire','reader-acquire-core','reader-acquire-under','reader-release','writer-begin','writer-poll','writer-abort-pending'):
   f=named('fn2-c-source-'+name)
   self.assertNotIn('reader-live-count',str(f));self.assertNotIn('count-invariant-p',str(f))
   theorem=named('fn2-c-source-'+name+'-preserves-count-invariant')
   self.assertIn('fn2-c-source-count-invariant-p',str(theorem))
  whole=named('fn2-c-source-exclusive-has-no-live-endpoint')
  self.assertIn('fn2-c-source-count-invariant-p',str(whole))
  self.assertTrue(has(whole,['equal',['fn2-c-source-readers-live','endpoint','fn2-c-source-readers'],'0']))
 def test_pending_extension_requires_actual_live_parent_not_a_flag(self):
  under=named('fn2-c-source-reader-acquire-under')
  self.assertTrue(has(under,['fn2-c-source-reader-current-p','parentendpoint','parentreceipt','fn2-c-source-readers']))
  self.assertTrue(has(under,['not',['equal','endpoint','parentendpoint']]))
  core=named('fn2-c-source-reader-acquire-core')
  gate=next(x for x in walk(core) if x and x[0]=='unless' and 'writer-phase-idle' in str(x))
  self.assertTrue(has(gate,['equal',['fn2-c-source-control-phase','0','fn2-c-source-control'],'*fn2-c-source-writer-phase-pending*']))
  self.assertTrue(has(gate,['fn2-c-source-reader-current-p','parentendpoint','parentreceipt','fn2-c-source-readers']))
  root=named('fn2-c-source-reader-acquire')
  self.assertTrue(has(root,['fn2-c-source-reader-acquire-core','endpoint','expected-receipt','0','0','fn2-c-source-control','fn2-c-source-readers']))
  calls=[x for x in walk(core) if x and x[0]=='fn2-c-source-readers-put']
  self.assertEqual(len(calls),1)
 def test_prepared_actual_nested_endpoint_and_hypothesis_controls(self):
  f=(ROOT/'tests/c-source-endpoint-unit.lisp').read_text()
  for required in ('(equal r 1)','(equal s 2)','(eq partial :waiting)','(equal wake 40)','(equal wakegen 11)',
                   '(eq too-late :owner)','(< old fresh)','(eq stale :stale)','(eq exhausted :exhausted)',
                   '(not (fn2-c-source-count-invariant-p','(fn2-c-source-count-hypothesis-removal-body'):
   self.assertIn(required,f)
  self.assertIn('UNEXECUTED',f)
if __name__=='__main__':unittest.main()
