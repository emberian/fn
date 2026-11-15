"""Connected direct lookup observer source controls; no ACL2 execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
PATH=ROOT/'books/machines-c-groups.lisp'
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def allnodes():return [n for t in forms(PATH.read_text()) for n in walk(read_sexp(t))]
def definition(name):return next(n for n in allnodes() if len(n)>2 and n[0] in ('defun','defmacro') and n[1]==name)
def calls(x,name):return [n for n in walk(x) if n and n[0]==name]
class GroupSourceObserver(unittest.TestCase):
 def test_both_direct_scalar_apis_use_one_actual_observed_emitter(self):
  for name in ('fn2-group-lookup','fn2-principal-lookup'):
   self.assertEqual(len([n for n in allnodes() if n[:2]==['fn2-directory-source-core-definition',name]]),1)
  macro=definition('fn2-directory-source-core-definition')
  for name in ('fn2-grp-lookup','fn2-succ-source-acquire','fn2-succ-source-close'):
   self.assertEqual(len(calls(macro,name)),1)
  text=PATH.read_text().split('(defmacro fn2-directory-source-core-definition',1)[1].split('(defmacro fn2-groups-core-events',1)[0]
  self.assertLess(text.index('(fn2-succ-source-acquire'),text.index('(fn2-grp-lookup'))
  self.assertLess(text.index('(fn2-grp-lookup'),text.index('(fn2-succ-source-close'))
  self.assertIn("(member-eq answer '(:more :miss))",text)
 def test_real_read_geometry_and_no_fabricated_actor_owner(self):
  for name in ('fn2-directory-source-core-definition','fn2-identity-decide'):
   node=definition(name)
   self.assertEqual(calls(node,'fn2-reads-rows'),[['fn2-reads-rows','fn2-reads']])
   self.assertFalse(calls(node,'fn2-c-source-reader-acquire'))
   self.assertFalse(calls(node,'fn2-c-source-reader-release'))
  for name in ('fn2-group-lookup','fn2-principal-lookup','fn2-identity-decide'):
   cost=next(n for n in allnodes() if n[:2]==['defcost',name])
   for child in ('fn2-core-reads','fn2-core-c-source-control','fn2-core-c-source-readers'):self.assertIn(child,str(cost))
 def test_identity_start_cannot_erase_a_retained_source_incarnation(self):
  start=definition('fn2-id-decide-start')
  self.assertIn(['equal',['fn2-succ-txns-source-receipt','tx','fn2-succ-txns'],'0'],list(walk(start)))
  self.assertFalse(calls(start,'fn2-succ-txns-set-source-receipt'))
 def test_identity_retains_across_both_reads_and_invalidates_abandoned_partial_facts(self):
  identity=definition('fn2-identity-decide')
  self.assertEqual(len(calls(identity,'fn2-id-decide-step')),1)
  self.assertEqual(len(calls(identity,'fn2-succ-source-acquire')),1)
  self.assertEqual(len(calls(identity,'fn2-succ-source-close')),1)
  self.assertEqual(calls(identity,'fn2-id-decides-set-phase'),[['fn2-id-decides-set-phase','tx','*fn2-id-decide-phase-idle*','fn2-id-decides']])
  text=PATH.read_text().split('(defun fn2-identity-decide ',1)[1]
  self.assertLess(text.index('(fn2-id-decided'),text.index('(fn2-succ-source-acquire'))
  self.assertLess(text.index('(fn2-succ-source-acquire'),text.index('(fn2-id-decide-step'))
  self.assertLess(text.index('(fn2-id-decide-step'),text.index('(fn2-succ-source-close'))
 def test_foreign_resolver_hold_is_rejected_before_shared_admission(self):
  macro=definition('fn2-directory-source-core-definition')
  first=next(n for n in walk(macro) if n and n[0]=='b*')[1][0]
  self.assertTrue(calls(first,'fn2-succ-txns-source-receipt'))
  self.assertTrue(calls(first,'fn2-succ-txns-lphase'))
  self.assertIn('*fn2-succ-lookup-idle*',str(first))
 def test_readonly_geometry_does_not_widen_public_or_child_outputs(self):
  for name in ('fn2-directory-source-core-definition','fn2-identity-decide'):
   node=definition(name)
   binding=next(n for n in walk(node) if n and n[0]=='stobj-let')
   self.assertNotIn('fn2-reads',binding[2])
   self.assertIn('fn2-c-source-control',binding[2])
   self.assertIn('fn2-c-source-readers',binding[2])
   self.assertLessEqual(len(binding[2]),32)
 def test_prepared_whole_h_control_uses_actual_public_calls_and_pending_poll(self):
  text=(ROOT/'tests/group-source-observer-unit.lisp').read_text()
  for name in ('UNEXECUTED','SYNTHETIC','fn2-group-lookup','fn2-principal-lookup','fn2-identity-decide','fn2-c-source-writer-begin','fn2-c-source-writer-poll','fn2-c-source-reader-release','fn2-gobs-whole-h','fn2-gobs-cleared','fn2-gobs-resolver-test','fn2-successor-put','fn2-successor-resolve','fn2-successor-release'):
   self.assertIn(name,text)
  for mode in ('group','principal','identity','error'):self.assertIn('(assert-event (fn2-gobs-test :'+mode+'))',text)
  for flag in ('(phase *fn2-c-source-writer-phase-exclusive*)','(readers 0)','(wake-pending 1)'):
   self.assertNotIn(flag,text)
 def test_no_production_direct_lower_call_bypasses_the_owned_core_path(self):
  # Named lower seams stay in this book; actual callers use public wrappers.
  for path in (ROOT/'books').glob('*.lisp'):
   if path==PATH:continue
   for t in forms(path.read_text()):
    for n in walk(read_sexp(t)):
     if n and n[0] in ('fn2-grp-lookup','fn2-id-decide-step','fn2-id-decide-start'):
      self.fail(f'{path.name} has a direct unobserved lower call: {n[0]}')
if __name__=='__main__':unittest.main()
