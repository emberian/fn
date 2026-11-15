"""Source protocol controls; ACL2 fixtures are prepared, not executed here."""
from pathlib import Path
import copy
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definitions(file):
 return {f[1]:f for raw in forms((ROOT/'books'/file).read_text()) if isinstance((f:=read_sexp(raw)),list) and f and f[0]=='defun'}
def calls(f,name):return [x for x in walk(f[3:]) if x and x[0]==name]
def equality(f,a,b):return ['equal',a,b] in list(walk(f))
class ObserverSource(unittest.TestCase):
 def setUp(self):self.d=definitions('c-source-observer.lisp');self.a=definitions('c-source-observer-adapters.lisp')
 def test_new_reader_requires_idle_writer_before_increment(self):
  f=self.d['fn2-c-source-read-acquire-raw']
  self.assertTrue(equality(f,['fn2-c-source-control-phase','0','fn2-c-source-control'],'*fn2-c-source-writer-phase-idle*'))
  source=(ROOT/'books/c-source-observer.lisp').read_text()
  part=source[source.index('(defun fn2-c-source-read-acquire-raw'):source.index('(defun fn2-c-source-read-release-raw')]
  self.assertLess(part.index('*fn2-c-source-writer-phase-idle*'),part.index('(n (+ 1'))
  self.assertEqual(len(calls(f,'fn2-c-source-observers-put')),1)
 def test_writer_closes_before_poll_and_exclusive_requires_zero(self):
  f=self.d['fn2-c-source-writer-begin-raw'];terms=list(walk(f))
  self.assertIn(['phase','*fn2-c-source-writer-phase-pending*'],terms)
  poll=self.d['fn2-c-source-writer-poll-raw']
  self.assertTrue(equality(poll,['fn2-c-source-control-readers','0','fn2-c-source-control'],'0'))
  bad=copy.deepcopy(poll)
  for x in walk(bad):
   if x and x[0]=='fn2-c-source-control-readers':x[0]='DROPPED-reader-count'
  self.assertFalse(equality(bad,['fn2-c-source-control-readers','0','fn2-c-source-control'],'0'))
 def test_exact_owner_generation_session_and_no_whole_scan(self):
  owner=self.d['fn2-c-source-observer-ownerp']
  self.assertTrue(equality(owner,'generation',['fn2-c-source-observers-generation','id','fn2-c-source-observers']))
  writer=self.d['fn2-c-source-writer-ownerp']
  for arg,field in [('token','serial'),('kind','writer-kind'),('id','writer-id'),('generation','writer-gen')]:
   self.assertTrue(equality(writer,arg,['fn2-c-source-control-'+field,'0','fn2-c-source-control']))
  for name,f in self.d.items():self.assertFalse(calls(f,name),name)
 def test_typed_adapters_validate_real_generation_and_global_partition(self):
  f=self.a['fn2-c-source-reader-currentp'];terms=list(walk(f))
  for kind in ('txn','auth','cns','cursor','sealer'):
   self.assertTrue(equality(f,'generation',['fn2-'+kind+'-generation','slot','fn2-'+kind]))
  self.assertIn(['equal','id',['+','base','slot']],terms)
  self.assertTrue(calls(self.a['fn2-c-source-read-release-children'],'fn2-c-source-master-currentp'))
 def test_uncertain_cannot_reopen_and_terminals_not_public(self):
  for name in ('fn2-c-source-writer-end-raw','fn2-c-source-writer-cancel-pending-raw'):
   self.assertTrue(calls(self.d[name],'fn2-c-source-writer-ownerp'))
  source=(ROOT/'books/c-source-observer-adapters.lisp').read_text()
  self.assertNotIn('(defcost fn2-c-source-writer-end',source)
  self.assertNotIn('(defcost fn2-c-source-writer-cancel',source)
  self.assertIn('*fn2-c-source-writer-phase-uncertain*',str(self.d['fn2-c-source-writer-poll-raw']))
 def test_actual_registration_and_prepared_nonvacuous_cases(self):
  source=(ROOT/'books/c-source-observer-state.lisp').read_text()
  self.assertIn('(fn2-c-source-observers-init (fn2-machine-index-count profile)',source)
  self.assertIn('(include-book "c-source-observer-state")',(ROOT/'books/machines-c.lisp').read_text())
  self.assertIn('(fn2-c-source-observer-core-faces)',(ROOT/'books/assembly-callbacks-c-prepare.lisp').read_text())
  fixture=(ROOT/'tests/c-source-observer-unit.lisp').read_text()
  for needle in ('(equal token 1)','(equal token2 2)','(equal tb 2)','(equal gb 33)','(eq blocked :busy)','(eq uncertain :uncertain)'):
   self.assertIn(needle,fixture)
 def test_prepared_typed_controls_use_actual_actor_take_and_shared_faces(self):
  source=(ROOT/'tests/c-source-observer-admitted-unit.lisp').read_text()
  self.assertEqual(source.count('(fn2-machine-take-fn2-auth '),2)
  self.assertIn('(fn2-c-source-read-release id0 (+ gen0 1)',source)
  self.assertIn('(equal tb writer)',source);self.assertIn('(equal tbgen wgen)',source)
  for name in ('fn2-c-source-read-acquire','fn2-c-source-read-release','fn2-c-source-writer-begin','fn2-c-source-writer-poll'):
   self.assertIn('('+name+' ',source)
  adapters=(ROOT/'books/c-source-observer-adapters.lisp').read_text()
  for line in adapters.splitlines():
   if line.startswith(' :tables '):
    for kind in ('txn','auth','cns','cursor','sealer','checkpoint-master'):
     self.assertNotIn('fn2-'+kind+' ',line)
if __name__=='__main__':unittest.main()
