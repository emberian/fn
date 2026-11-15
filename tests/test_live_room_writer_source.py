"""Prepared actual writer-progress control: source shape, not execution/admission."""
from pathlib import Path
import re,sys,unittest
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
FIX=ROOT/'tests/run-physical-live-room-writer-unit.lisp'
def walk(x):
 if isinstance(x,list):
  yield x
  for v in x:yield from walk(v)
def trees(p):return [read_sexp(f) for f in forms(p.read_text())]
def calls(x,n):return [v for v in walk(x) if v and v[0]==n]
@lru_cache(maxsize=1)
def closure():
 todo=[FIX];seen={}
 while todo:
  p=todo.pop().resolve()
  if p in seen:continue
  if not p.exists():raise AssertionError('missing source provider '+str(p))
  seen[p]=p.read_text()
  for f in forms(seen[p]):
   m=re.match(r'\(include-book\s+"([^"]+)"',f,re.I)
   if m and ':dir' not in f:todo.append(p.parent/(m[1]+'.lisp'))
 return seen
class LiveRoomWriter(unittest.TestCase):
 def test_dependency_complete_named_source_providers(self):
  source=closure();self.assertGreater(len(source),400)
  for name in ('checkpoint-live-catalog','checkpoint-live-cbase','checkpoint-live-install','run-physical-readiness-live','run-physical-readiness-core'):
   self.assertIn(ROOT/'books'/(name+'.lisp'),source)
  assembly=source[ROOT/'books/assembly-callbacks-c.lisp']
  for name in ('catalog','cbase','install'):self.assertIn('(fn2-checkpoint-live-'+name+'-events)',assembly)
  e=source[ROOT/'books/assembly-callbacks-e-cns.lisp']
  self.assertIn('(fn2-c-actor-loader-core-events)',e)
  self.assertIn('(fn2-run-load-readiness-core-events)',e)
 def test_real_actors_and_canonical_resource_constructors(self):
  x=trees(FIX)
  for n in ('fn2-clc-produce-held','fn2-clc-full-live-source-p','fn2-machine-take-fn2-cns','fn2-c-actor-loader-plan','fn2-run-load-region-reserve','fn2-run-load-park-source','fn2-run-load-parked-machine-current-p'):
   self.assertTrue(calls(x,n),n)
  text=FIX.read_text()
  self.assertIn('(fn2-machine-connection-count *fn2-cns-admission-ordinal* fn2-core)',text)
  self.assertIn('(fn2-lrw-pressure population nil fn2-core)',text)
  self.assertIn('(fn2-lrw-pressure (1- remaining) t fn2-core)',text)
  self.assertIn('((and started (not (fn2-lrw-cold-room-p fn2-core))) (mv :pressured 0 fn2-core))',text)
  for n in ('fn2-pool-put','update-fn2-pool-class-countsi','fn2-run-loads-put','fn2-run-load-readiness-put','fn2-checkpoint-summary-put'):
   self.assertFalse(calls(x,n),n)
 def test_actual_exclusive_writer_and_full_scan(self):
  x=trees(FIX)
  for n in ('fn2-checkpoint-live-catalog-begin-op','fn2-checkpoint-live-catalog-step-op','fn2-checkpoint-live-cbase-step-op','fn2-checkpoint-live-replace-begin-op','fn2-run-load-readiness-live-begin-op','fn2-run-load-readiness-owned-step','fn2-run-load-readiness-live-complete-current-p'):
   self.assertTrue(calls(x,n),n)
  text=FIX.read_text()
  self.assertIn('(equal steps (+ rows 2))',text)
  self.assertIn('(fn2-lrw-scan (+ rows 3) fn2-core)',text)
  self.assertIn('(fn2-run-loads-rows fn2-run-loads)',text)
  self.assertIn('(fn2-run-load-ops-rows fn2-run-load-ops)',text)
 def test_preserves_all_children_except_intended_readiness_cursor(self):
  text=FIX.read_text()
  self.assertIn("(remove-assoc-eq 'fn2-core-run-load-readiness *fn2-core-children*)",text)
  self.assertIn('(equal before (fn2-lrw-preserved fn2-core))',text)
  self.assertIn('(fn2-lrw-complete-current-p fn2-core) (not (fn2-lrw-cold-room-p fn2-core))',text)
  self.assertIn('(not (fn2-core-stopped-p fn2-core))',text)
 def test_every_selected_generated_face_has_actual_child_provider(self):
  definitions=set();costs={}
  for text in closure().values():
   for f in forms(text):
    for x in walk(read_sexp(f)):
     if len(x)>2 and x[0]=='defun' and isinstance(x[1],str):definitions.add(x[1])
     if len(x)>3 and x[0]=='defcost' and isinstance(x[1],str) and ':child' in x:costs[x[1]]=x[x.index(':child')+1]
  for face in ('fn2-checkpoint-live-catalog-begin-op','fn2-checkpoint-live-catalog-step-op','fn2-checkpoint-live-cbase-step-op','fn2-checkpoint-live-replace-begin-op','fn2-run-load-readiness-live-begin-op'):
   self.assertIn(face,costs);self.assertIn(costs[face],definitions)
  self.assertIn('fn2-run-load-readiness-owned-step',definitions)
  self.assertIn('fn2-c-actor-loader-plan',definitions)
 def test_actual_leaf_arities_and_small_mv_outputs(self):
  definitions={}
  for p,text in closure().items():
   for f in forms(text):
    for x in walk(read_sexp(f)):
     if len(x)>2 and x[0]=='defun' and isinstance(x[1],str) and isinstance(x[2],list):definitions[x[1]]=len(x[2])
  actual=0
  for x in walk(trees(FIX)):
   if x and isinstance(x[0],str) and x[0] in definitions:
    self.assertEqual(len(x)-1,definitions[x[0]],x[0]);actual+=1
   if x and x[0]=='mv':self.assertLessEqual(len(x)-1,32)
  self.assertGreater(actual,30)
if __name__=='__main__':unittest.main()
