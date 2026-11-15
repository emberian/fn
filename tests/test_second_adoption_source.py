"""Prepared ancestry/source controls, not simulation or whole closure admission."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
import lisp_rewrite as lr
SUP=ROOT/'tests/checkpoint-second-adoption-support.lisp'
UNIT=ROOT/'tests/checkpoint-productive-second-adoption-unit.lisp'
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def tree(p):return [read_sexp(f) for f in forms(p.read_text())]
def calls(x,n):return [v for v in walk(x) if v and v[0]==n]
class SecondAdoption(unittest.TestCase):
 def test_real_same_sim_prefix_and_two_real_publications(self):
  x=tree(UNIT);self.assertEqual(len(calls(x,'fn2-clc-prefix-to-held')),2)
  self.assertEqual(len(calls(x,'fn2-sad-adopt')),2)
  self.assertEqual(len(calls(x,'fn2-cln-register-append')),1)
  self.assertFalse(calls(x,'fn2-core-init'));self.assertFalse(calls(x,'fn2-sim-init'))
  text=SUP.read_text();self.assertIn('(fn2-init-executor *fn2-ccp-profile* :node nil fn2-core)',text)
  self.assertIn('(fn2-ccp-live-complete-p t 0 fn2-core)',text)
  self.assertIn('(fn2-clc-full-live-source-p fn2-core)',UNIT.read_text())
  self.assertIn('TEST-ONLY CATALOG',text);self.assertIn('*fn2-checkpoint-activation-qualified*=NIL',text)
 def test_actual_physical_miss_selection_io_and_verifier_faces(self):
  x=tree(SUP)
  for n in ('fn2-c-actor-loader-plan','fn2-c-actor-loader-reserve','fn2-read-key','fn2-read-lookup','fn2-read-range','fn2-read-next','fn2-c-actor-loader-state','fn2-run-page-bind','fn2-run-page-step','fn2-run-page-read','fn2-sim-take-prefix','fn2-sim-complete','fn2-exec-harvest'):
   self.assertTrue(calls(x,n),n)
  text=SUP.read_text()
  self.assertIn('(equal value 1)',text);self.assertIn('(equal rvalue 1)',text)
  self.assertIn('(<= *fn2-storage-extent-units* lreads)',text)
  self.assertIn('(<= *fn2-storage-extent-units* rreads)',text)
  self.assertNotIn('fn2-run-bound-bind',text);self.assertNotIn('fn2-run-cache-install',text)
 def test_real_context_descriptor_refusal_then_named_byte_progress(self):
  text=SUP.read_text();x=tree(SUP)
  for required in ('(fn2-run-page-step c 0 fn2-core)','(fn2-run-page-step c 1 fn2-core)',
                   '(fn2-run-page-step c ordinary fn2-core)','(equal ordinary 32)',
                   '(fn2-run-page-step c *fn2-checkpoint-master-pure-byte-quantum* fn2-core)',
                   '(equal before (fn2-test-core-snapshot fn2-core))',
                   '(equal ops-before (fn2-test-snapshot-fn2-ops fn2-core))',
                   '*fn2-run-load-phase-verify*'):
   self.assertIn(required,text)
  self.assertTrue(calls(x,'fn2-sad-context-progress'))
 def test_actual_cleanup_and_monotone_second_subject(self):
  x=tree(SUP);self.assertEqual(len(calls(x,'fn2-read-release')),2)
  self.assertTrue(calls(x,'fn2-run-load-region-clean'))
  self.assertTrue(calls(x,'fn2-cln-pump'))
  t=UNIT.read_text()
  for n in ('(< tag newtag)','(< checkpoint newcheckpoint)','(< cut newcut)','(fn2-core-wfp fn2-core)','(eq (fn2-check-own fn2-core fn2-own) :pass)'):
   self.assertIn(n,t)
 def test_no_authority_ready_or_accepted_state_seeding(self):
  for p in (SUP,UNIT):
   x=tree(p)
   for f in walk(x):
    if f and isinstance(f[0],str):
     self.assertFalse(f[0].endswith('-put') or f[0].endswith('-put-core') or f[0].startswith('update-fn2-'),f[0])
   self.assertNotIn('fn2-post-result',p.read_text())
  x=tree(SUP)
  self.assertTrue(calls(x,'fn2-run-installed-physical-count'))
  self.assertTrue(calls(x,'fn2-sad-physical-count'))
 def test_actual_defs_known_face_arities_and_bounded_mv(self):
  definitions={}
  for p in list((ROOT/'books').glob('*.lisp'))+[SUP,UNIT]:
   for f in forms(p.read_text()):
    for x in walk(read_sexp(f)):
     if len(x)>2 and x[0]=='defun' and isinstance(x[1],str) and isinstance(x[2],list):definitions[x[1]]=len(x[2])
  definitions.update({'fn2-machine-take-fn2-cns':10,'fn2-run-page-reserve':5,'fn2-run-page-bind':5,'fn2-run-page-step':3,'fn2-run-page-read':3,'fn2-run-page-release':5})
  def nodes(x):
   if isinstance(x,lr.Lst):
    yield x
    for y in x.items:yield from nodes(y)
   elif isinstance(x,lr.Pre):yield from nodes(x.node)
  checked=0
  for p in (SUP,UNIT):
   for top in lr.parse(p.read_text()).forms:
    for x in nodes(top):
     name=getattr(x.items[0],'low','') if x.items else ''
     if name in definitions:
      checked+=1;self.assertEqual(len(x.items)-1,definitions[name],name)
     if name=='mv':self.assertLessEqual(len(x.items)-1,32)
  self.assertGreaterEqual(checked,49)
if __name__=='__main__':unittest.main()
