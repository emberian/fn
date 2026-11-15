"""Actual READ CLOSE propagation controls; no ACL2/runtime qualification."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym,MUT
from read_close_park_rewrite import project,project_endpoint_fixture,PARK,MORE

def source(p):return (ROOT/p).read_text()
def defs(s):return {sym(n.items[1]):n for f in lr.parse(s).forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>3 and sym(n.items[0])=='defun'}
def emit(n):return " ".join(lr.emit(n,drop_comments=True).split())
def closes_before_release(f):
 s=emit(f);return 'fn2-read-source-close' in s and s.index('fn2-read-source-close')<s.index('fn2-c-source-reader-release') and '(unless (eq parked :ok))' in s
class ReadClose(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.now=source('books/machines-c-read.lisp');cls.f=defs(cls.now)
  cls.base=subprocess.check_output(['git','show','a0b13a692:books/machines-c-read.lisp'],cwd=ROOT,text=True)
 def test_exact_actual_projection_and_no_double_apply(self):
  self.assertEqual(project(self.base,source('tools/fixtures/read-close-park/helpers.lisp')),self.now)
  with self.assertRaises(ValueError):project(self.now,'')
 def test_original_rd_kernels_are_identical(self):
  for name,f in defs(self.base).items():
   if name.startswith('fn2-rd-'):self.assertEqual(self.base[f.start:f.end],self.now[self.f[name].start:self.f[name].end],name)
 def test_close_derives_actual_read_region_and_retained_owner(self):
  s=emit(self.f['fn2-read-source-close'])
  self.assertIn('(fn2-id-decides-rows fn2-id-decides)',s);self.assertIn('(fn2-reads-rows fn2-reads)',s)
  self.assertIn('(fn2-run-load-region-park (+ transactions x) 1',s)
  self.assertIn('(* *fn2-b-range-source-cursors* x)',s)
  self.assertIn('*fn2-b-range-source-cursors* 0 0 kind owner generation',s)
  owner=emit(self.f['fn2-read-source-owner'])
  for field in ('kind','owner','generation','windows','pending'):self.assertIn('fn2-run-loads-'+field,owner)
  self.assertIn('fn2-checkpoint-summary-leases-live',owner)
  for wrong in ('fn2-reads-qk','fn2-reads-qs','fn2-reads-qg','caller-owner'):self.assertNotIn(wrong,owner)
 def test_refused_park_cannot_drop_receipt(self):
  f=self.f['fn2-read-observer-release'];self.assertTrue(closes_before_release(f))
  mutant=emit(f).replace('fn2-read-source-close','skipped-source-close',1)
  self.assertFalse(closes_before_release(defs(mutant)['fn2-read-observer-release']))
  self.assertIn('(if fresh (fn2-read-observer-release',emit(self.f['fn2-read-observer-enter']))
 def test_key_and_release_close_before_same_old_kernel(self):
  for op in ('key','key-octets','release'):
   b=self.f['fn2-read-'+op+'-children'].items[-1]
   self.assertEqual(sym(b.items[0]),'mv-let');self.assertEqual(sym(b.items[2].items[0]),'fn2-read-observer-release')
   self.assertEqual(emit(b.items[3].items[1]),'(eq closed :ok)')
   self.assertIn('fn2-rd-',emit(b.items[3].items[2]));self.assertNotIn('fn2-rd-',emit(b.items[3].items[3]))
 def test_all_mutating_child_core_and_cost_carriers_are_exact(self):
  costs={sym(f.items[1]):f for f in lr.parse(self.now).forms if isinstance(f,lr.Lst) and f.items and sym(f.items[0])=='defcost'}
  for op in MUT:
   child=self.f['fn2-read-'+op+'-children'];inputs=[sym(v) for v in child.items[2].items]
   self.assertEqual(len(inputs),len(set(inputs)))
   for carrier in MORE:self.assertIn(carrier,inputs)
   st=self.f['fn2-read-'+op].items[-1];outs=[sym(v) for v in st.items[2].items]
   self.assertEqual(len(outs),len(set(outs)));self.assertLessEqual(len(outs),32)
   for carrier in PARK:self.assertIn(carrier,outs)
   self.assertNotIn('fn2-pool',outs)
   self.assertEqual(len(st.items[3].items)-1,len(child.items[2].items))
   cost=costs['fn2-read-'+op];i=next(i for i,v in enumerate(cost.items) if sym(v)==':tables');tables=[sym(v) for v in cost.items[i+1].items]
   for carrier in MORE+[v for v in outs if v.startswith('fn2-')]:self.assertIn(carrier.replace('fn2-','fn2-core-',1),tables)
   self.assertNotIn(':effects',emit(cost))
 def test_known_mv_bindings_match_actual_child_projections(self):
  known={'fn2-read-observer-release':8,'fn2-read-observer-enter':8,'fn2-read-source-close':5,'fn2-read-source-owner':4,
         'fn2-run-load-region-park':5,'fn2-c-source-reader-acquire':4,'fn2-c-source-reader-acquire-under':4,'fn2-c-source-reader-release':5,
         'fn2-run-load-reserve':3,'fn2-run-load-release':6}
  for op in MUT:known['fn2-read-'+op+'-children']=len(self.f['fn2-read-'+op].items[-1].items[2].items)
  def expected(call):
   if not isinstance(call,lr.Lst) or not call.items:return None
   name=sym(call.items[0])
   if name in known:return known[name]
   if name=='mv':return len(call.items)-1
   if name=='if':
    a,b=expected(call.items[2]),expected(call.items[3])
    return a if a==b else None
   return None
  checked=0
  for f in list(self.f.values())+list(defs(source('tests/read-close-park-unit.lisp')).values()):
   for n in nodes(f.items[-1]):
    if not isinstance(n,lr.Lst) or not n.items:continue
    if sym(n.items[0])=='mv-let':lhs,call=n.items[1],n.items[2];actual=len(lhs.items)
    elif len(n.items)==2 and isinstance(n.items[0],lr.Lst) and sym(n.items[0].items[0])=='mv':lhs,call=n.items;actual=len(lhs.items)-1
    else:continue
    count=expected(call)
    if count is not None:checked+=1;self.assertEqual(actual,count)
  self.assertEqual(checked,20)
 def test_endpoint_fixture_is_same_projection_with_bounded_outputs(self):
  old=subprocess.check_output(['git','show','a0b13a692:tests/read-observer-endpoint-unit.lisp'],cwd=ROOT,text=True)
  now=source('tests/read-observer-endpoint-unit.lisp');self.assertEqual(project_endpoint_fixture(old),now)
  p=next(f for f in lr.parse(now).forms if isinstance(f,lr.Lst) and len(f.items)>2 and sym(f.items[1])=='*fn2-rdo-stobjs*')
  self.assertEqual(len(p.items[2].node.items),11);self.assertLessEqual(1+len(p.items[2].node.items),32)
 def test_prepared_pending_mixed_owner_and_park_fixture_uses_actual_key(self):
  s=source('tests/read-close-park-unit.lisp')
  self.assertIn('UNEXECUTED',s);self.assertIn('SYNTHETIC',s)
  self.assertEqual(s.count('(fn2-read-key-children '),3)
  self.assertIn('(fn2-run-load-reserve 1 7 8 1',s)
  self.assertIn('(fn2-run-load-reserve 2 7 10 1',s)
  for fact in ('(eq pending-refused :state)','(eq owner-refused :state)',
               '(equal (fn2-reads-observer-serial 0 fn2-reads) receipt)',
               '(equal (fn2-checkpoint-summary-leases-live 1 fn2-checkpoint-summary-leases) 1)',
               '(eq key :ok)','(equal (fn2-checkpoint-summary-lease-count 0 fn2-checkpoint-summary) 0)',
               '(equal (fn2-run-loads-windows 1 fn2-run-loads) 2)',
               '(eq (fn2-pool-workspace-code (fn2-run-loads-page 1',
               '(eq (fn2-pool-workspace-code (fn2-run-loads-scratch 1'):
   self.assertIn(fact,s)
if __name__=='__main__':unittest.main()
