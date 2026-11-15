"""Actual txn/auth loader source controls; no ACL2 execution claim."""
from pathlib import Path
import sys,unittest,copy
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from c_actor_loader_rewrite import transform,route,answers,lower_statuses
RUNTIME=ROOT/'books/c-actor-loader.lisp';FORM=ROOT/'books/c-actor-loader-form.lisp'
def walk(x):
 if isinstance(x,list):
  yield x
  for a in x:yield from walk(a)
def tree(p):return [read_sexp(f) for f in forms(p.read_text())]
def fn(name,path=RUNTIME):return next(x for f in tree(path) for x in walk(f) if x[:2]==['defun',name])
def calls(x,name):return [a for a in walk(x) if a and a[0]==name]
def resident_contract(work):
 branches=[a for a in walk(work) if a and a[0]==[':resident']]
 return branches==[[[':resident'],['unquote-splicing','original']]]
class TxnAuthLoader(unittest.TestCase):
 def test_zero_allocation_is_resampled_each_actual_work_turn(self):
  work=fn('fn2-c-actor-loader-work',FORM)
  self.assertTrue(resident_contract(work))
  bad=copy.deepcopy(work)
  next(a for a in walk(bad) if a and a[0]==[':resident']).insert(1,[':set',['loader','HELD']])
  self.assertFalse(resident_contract(bad))
  self.assertTrue(calls(fn('fn2-c-actor-loader-wrap-arms',FORM),'fn2-c-actor-loader-work'))
  text=FORM.read_text()
  self.assertIn("'(:lookup :prepare :ready)",text)
  self.assertIn("'(:lookup :allocate :bhead :outcome :head :get :ready)",text)
  admit=fn('fn2-c-actor-loader-admit')
  self.assertTrue(calls(admit,'fn2-run-installed-physical-count'))
  self.assertTrue(calls(admit,'fn2-run-load-region-freep'))
  self.assertTrue(calls(admit,'fn2-run-load-region-reserve'))
 def test_writer_gate_precedes_every_fresh_reservation_and_count_sample(self):
  x=fn('fn2-c-actor-load-admission-code')
  for n in ('fn2-c-source-reader-current-p','fn2-succ-txns-source-receipt','fn2-read-observer-current-p','fn2-reads-observer-parent-serial'):
   self.assertTrue(calls(x,n),n)
  self.assertFalse(calls(x,'fn2-c-source-control-readers'))
  text=RUNTIME.read_text().split('(defun fn2-c-actor-loader-admit',1)[1]
  self.assertLess(text.index('(fn2-c-actor-load-admission-code'),text.index('(fn2-run-installed-physical-count'))
  self.assertLess(text.index('(fn2-c-actor-load-admission-code'),text.index('(fn2-run-load-region-reserve'))
  self.assertIn('((:blocked) (:charge :steps *fn2-work-poll* :runnable t))',FORM.read_text())
 def test_prepared_pending_writer_blocks_new_actor_without_allocation_churn(self):
  text=(ROOT/'tests/txn-auth-loader-admission-unit.lisp').read_text()
  for call in ('fn2-machine-take-fn2-auth','fn2-successor-resolve','fn2-c-source-writer-begin','fn2-c-actor-loader-reserve','fn2-successor-release','fn2-c-source-writer-poll'):
   self.assertIn('('+call,text)
  self.assertIn('(eq blocked :blocked) (equal complete 0) blocked-kept',text)
  self.assertIn('(eq existing :resident) (equal existing-complete 0) existing-kept',text)
  self.assertIn('(equal before (fn2-tal-capacity-view fn2-core))',text)
  self.assertNotIn('update-fn2-run-installed-physical-count',text)
 def test_real_receipt_and_selected_miss_before_owner_capture(self):
  x=fn('fn2-c-actor-tx-missp')
  for name in ('fn2-c-source-reader-current-p','fn2-succ-txns-source-receipt','fn2-c-source-successor-endpoint','fn2-run-cursors-priority'):
   self.assertTrue(calls(x,name),name)
  self.assertFalse(calls(x,'fn2-run-cursors-run'))
  owner=fn('fn2-c-actor-tx-owner')
  self.assertTrue(calls(owner,'fn2-c-actor-tx-missp'))
  self.assertTrue(calls(owner,'fn2-run-load-ownerp'))
  self.assertTrue(calls(fn('fn2-c-actor-loader-plan'),'fn2-machine-generation'))
 def test_explicit_io_wake_and_bounded_cleanup(self):
  work=fn('fn2-c-actor-loader-work',FORM)
  issues=[x for x in walk(work) if x and x[0]==':issue']
  self.assertEqual(len(issues),1);self.assertEqual(issues[0][1][0],'fn2-run-page-read')
  self.assertIn(':read-result (:wake)',FORM.read_text())
  drain=fn('fn2-c-actor-loader-drain-body',FORM)
  self.assertTrue(calls(drain,'fn2-c-actor-loader-drain'))
  self.assertTrue(calls(drain,'fn2-c-actor-loader-member-release'))
  self.assertTrue(calls(drain,'fn2-run-page-release'))
  self.assertNotIn(':park :pool',FORM.read_text())
  self.assertNotIn('source-observation',FORM.read_text())
 def test_structural_actor_rewrite_is_idempotent(self):
  for name in ('txn','authority'):
   p=ROOT/'books'/(name+'-kind.lisp');text=p.read_text();self.assertEqual(transform(text,True),(text,0))
   text=(ROOT/'books'/(name+'.lisp')).read_text()
   self.assertEqual(transform(text),(text,0));self.assertEqual(route(text),(text,0))
   self.assertEqual(answers(text),(text,0));self.assertEqual(lower_statuses(text),(text,0))
  self.assertNotIn('fn2-cns-row-loader',RUNTIME.read_text());self.assertNotIn('fn2-cns-row-storage',RUNTIME.read_text())
 def test_source_actual_arities_and_known_mv(self):
  definitions={}
  for p in (ROOT/'books').glob('*.lisp'):
   for f in forms(p.read_text()):
    try:x=read_sexp(f)
    except (ValueError,IndexError):continue
    for a in walk(x):
     if len(a)>2 and a[0]=='defun' and isinstance(a[1],str) and isinstance(a[2],list):definitions[a[1]]=len(a[2])
     if len(a)>2 and a[0]=='defcolumns' and isinstance(a[1],str) and isinstance(a[2],list):
      prefix=a[1];definitions[prefix+'-rows']=1;definitions[prefix+'-wfp']=1
      for col in a[2]:
       if isinstance(col,list) and col and isinstance(col[0],str):definitions[prefix+'-'+col[0]]=2;definitions[prefix+'-set-'+col[0]]=3
  known={'fn2-c-actor-loader-plan':8,'fn2-c-actor-load-active':3,'fn2-c-actor-tx-owner':4,
   'fn2-read-loader-selected':2,'fn2-read-loader-owner':4,'fn2-run-load-region-reserve':7,
   'fn2-run-load-region-drain':2,'fn2-run-load-region-member-release':6,'fn2-run-page-release':2}
  checked=0;mv=0
  for f in tree(RUNTIME):
   for function in walk(f):
    if len(function)<4 or function[0]!='defun':continue
    for a in walk(function[3:]):
     if a and isinstance(a[0],str) and a[0] in definitions:
      checked+=1;self.assertEqual(len(a)-1,definitions[a[0]],a[0])
     if len(a)==2 and isinstance(a[0],list) and a[0] and a[0][0]=='mv' and isinstance(a[1],list) and a[1] and isinstance(a[1][0],str) and a[1][0] in known:
      mv+=1;self.assertEqual(len(a[0])-1,known[a[1][0]],a[1][0])
  self.assertGreater(checked,100);self.assertEqual(mv,8)
if __name__=='__main__':unittest.main()
