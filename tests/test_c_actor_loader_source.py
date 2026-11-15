"""Source-only actor boundary controls. No ACL2 execution/admission claim."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from c_actor_loader_rewrite import transform,route,answers,cns_lease_union,cns_commit_outputs,cns_continuations,CNS_CONTINUATIONS

def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def parsed(path):return [read_sexp(x) for x in forms((ROOT/path).read_text())]
def function(name,fs):return next(x for f in fs for x in walk(f) if x[:2]==['defun',name])
def calls(f,name):return [x for x in walk(f) if x and x[0]==name]
class ActorLoader(unittest.TestCase):
 def test_rewrite_actual_class_once_and_idempotent(self):
  for name in ('txn','authority','cns'):
   kind='fn2-auth' if name=='authority' else 'fn2-'+name
   for suffix,decl in (('-kind',True),('',False)):
    p=ROOT/'books'/(name+suffix+'.lisp');text=p.read_text()
    self.assertIn(('fn2-c-actor-loader-kind ' if decl else 'fn2-c-actor-loader-arms ')+kind,text)
    self.assertEqual(transform(text,decl),(text,0))
   body=(ROOT/'books'/(name+'.lisp')).read_text()
   self.assertEqual(route(body),(body,0))
   self.assertEqual(answers(body),(body,0))
  sample='(in-package "ACL2")\n(fn2-book-layer :d)\n(defmachine fn2-txn :phases (:lookup) :holds ((:lookup :transaction-row)))'
  changed,n=transform(sample,True)
  self.assertEqual(n,2)
  self.assertIn('(fn2-c-actor-loader-kind fn2-txn',changed)
  self.assertEqual(transform(changed,True),(changed,0))
 def test_actual_actor_generation_and_geometry(self):
  f=function('fn2-c-actor-loader-plan',parsed('books/c-actor-loader.lisp'))
  nodes=list(walk(f))
  self.assertIn(['equal','gen',['fn2-machine-generation','id','fn2-core']],nodes)
  for kind in ('txn','auth','cns'):
   self.assertTrue(calls(f,'fn2-'+kind+'-snapshot-read-code'))
  for dep in ('fn2-machine-slot','fn2-machine-connection-count','fn2-id-decides-rows','fn2-reads-rows'):
   self.assertTrue(calls(f,dep))
  import copy
  bad=copy.deepcopy(f)
  for x in walk(bad):
   if x and x[0]=='fn2-machine-generation':x[0]='REMOVED-generation'
  self.assertNotIn(['equal','gen',['fn2-machine-generation','id','fn2-core']],list(walk(bad)))
 def test_shared_real_job_resources_and_selected_owner(self):
  fs=parsed('books/c-actor-loader.lisp')
  self.assertTrue(calls(function('fn2-c-actor-loader-admit',fs),'fn2-run-load-region-reserve'))
  for op in ('fn2-c-actor-loader-reserve','fn2-c-actor-loader-reserve-held'):
   self.assertTrue(calls(function(op,fs),'fn2-c-actor-loader-admit'))
  self.assertTrue(calls(function('fn2-c-actor-loader-member-release',fs),'fn2-run-load-region-member-release'))
  owner=function('fn2-c-actor-tx-owner',fs)
  self.assertTrue(calls(owner,'fn2-c-actor-tx-missp'))
  self.assertTrue(calls(owner,'fn2-run-load-ownerp'))
  for field in ('owner-kind','owner-slot','owner-gen'):
   self.assertTrue(calls(owner,'fn2-checkpoint-summary-leases-'+field))
  state=function('fn2-c-actor-loader-state',fs)
  self.assertTrue(calls(state,'fn2-read-loader-selected'))
  self.assertTrue(calls(state,'fn2-read-loader-owner'))
  self.assertFalse(calls(state,'fn2-block-read-children'))
 def test_resident_zero_count_does_not_claim_a_bundle(self):
  fs=parsed('books/c-actor-loader.lisp')
  reserve=function('fn2-c-actor-loader-admit',fs)
  self.assertIn(['equal',['fn2-run-installed-physical-count','fn2-run-installed'],'0'],list(walk(reserve)))
  self.assertIn(['mv',':resident','0','fn2-core'],list(walk(reserve)))
  text=(ROOT/'books/c-actor-loader.lisp').read_text()
  self.assertLess(text.index('(fn2-run-installed-physical-count'),text.index('(fn2-run-load-region-reserve'))
  form=function('fn2-c-actor-loader-admit-op',parsed('books/c-actor-loader-form.lisp'))
  self.assertTrue(any(x and x[0]==[':resident'] for x in walk(form)))
 def test_generated_explicit_io_and_ranked_drain(self):
  fs=parsed('books/c-actor-loader-form.lisp')
  work=function('fn2-c-actor-loader-work',fs)
  self.assertEqual(len(calls(work,'fn2-run-page-read')),1)
  issues=calls(work,':issue')
  self.assertEqual(len(issues),1)
  self.assertEqual(issues[0][1][0],'fn2-run-page-read')
  self.assertFalse(calls(work,'fn2-block-read-children'))
  drain=function('fn2-c-actor-loader-drain-body',fs)
  self.assertTrue(calls(drain,'fn2-c-actor-loader-member-release'))
  self.assertTrue(calls(drain,'fn2-c-actor-loader-last-op'))
  last=function('fn2-c-actor-loader-last-op',fs)
  self.assertTrue(calls(last,'fn2-run-page-release'))
  self.assertIn([':release',[':storage-window']],list(walk(last)))
  self.assertTrue(any(x and x[0]==':read-result' and [':wake'] in x for f in fs for x in walk(f)))
 def test_miss_retains_lookup_and_authority_progress(self):
  fs=parsed('books/authority.lisp')
  step=function('fn2-auth-lookup-step',fs)
  self.assertIn([':more',':miss',':ok'],list(walk(step)))
  allows=function('fn2-authority-allows',fs)
  self.assertEqual(len([x for x in walk(allows) if x and x[0]==':miss']),3)
  cns=function('fn2-cns-authority-allows',fs)
  self.assertEqual(len([x for x in walk(cns) if x[:3]==['member-eq','c',['quote',[':more',':miss']]]]),4)
  for book in ('txn','authority','cns'):
   for f in parsed('books/'+book+'.lisp'):
    for x in walk(f):
     if len(x)>2 and x[0]==':do' and isinstance(x[2],list) and x[2] and x[2][0] in ('fn2-authority-allows','fn2-cns-authority-allows'):
      self.assertTrue(any(y and y[0]==[':more',':miss'] for y in walk(x)))
 def test_cns_continuations_do_not_repeat_consumed_commit_or_fetch(self):
  text=(ROOT/'books/cns.lisp').read_text()
  self.assertEqual(cns_commit_outputs(text),(text,0))
  self.assertEqual(cns_continuations(text),(text,0))
  for f in parsed('books/cns.lisp'):
   for x in walk(f):
    if x and x[0]==':commit':
     self.assertFalse(calls(x,'fn2-cns-lookup-cursor'))
    if len(x)>2 and x[0]==':do' and isinstance(x[2],list) and x[2] and x[2][0] in CNS_CONTINUATIONS:
     self.assertIn([':more',':miss'],list(walk(x)))
  self.assertNotIn('((eq icode :more) (:set (more 1))',text)
  forms=parsed('books/c-actor-loader-form.lisp')
  outputs=function('fn2-c-actor-loader-cns-output-arms',forms)
  self.assertIn([':next',':item-output'],list(walk(outputs)))
  self.assertIn([':next',':article-output'],list(walk(outputs)))
  self.assertTrue(calls(outputs,'fn2-cns-lookup-cursor'))
  self.assertIn(['equal','row-register-check','1'],list(walk(outputs)))
 def test_cns_storage_rank_is_union_of_real_lease_and_loader(self):
  fs=parsed('books/c-actor-loader-form.lisp')
  hold=function('fn2-c-actor-loader-resource',fs)
  self.assertIn([':storage-window',':while',['storage',':held']],list(walk(hold)))
  lease=function('fn2-c-actor-loader-cns-lease-forms',fs)
  self.assertIn(['equal','row-loader','*fn2-cns-loader-held*'],list(walk(lease)))
  self.assertIn([':acquire',[':storage-window']],list(walk(lease)))
  self.assertIn([':release',[':storage-window']],list(walk(lease)))
  last=function('fn2-c-actor-loader-drain-body',fs)
  self.assertIn(['equal','row-lease','*fn2-cns-lease-held*'],list(walk(last)))
  self.assertIn(['equal','row-pending','0'],list(walk(last)))
  costs=parsed('books/c-actor-loader.lisp')
  reserve=next(f for f in costs if isinstance(f,list) and f[:2]==['defcost','fn2-c-actor-loader-reserve'])
  self.assertEqual(reserve[reserve.index(':effects')+1],[[':acquire',[':storage-window']]])
  held=next(f for f in costs if isinstance(f,list) and f[:2]==['defcost','fn2-c-actor-loader-reserve-held'])
  self.assertNotIn(':effects',held)
  proof=function('fn2-c-actor-loader-article-held-p',costs)
  self.assertTrue(calls(proof,'fn2-pool-ownerp'))
  self.assertTrue(calls(proof,'fn2-pool-gen'))
  self.assertTrue(calls(function('fn2-c-actor-loader-reserve-held',costs),'fn2-c-actor-loader-article-held-p'))
  last=function('fn2-c-actor-loader-last-held',costs)
  self.assertTrue(calls(last,'fn2-c-actor-loader-article-held-p'))
  self.assertTrue(calls(last,'fn2-run-load-region-drain'))
 def test_no_same_rank_pool_wait_and_common_events_once(self):
  text=(ROOT/'books/cns.lisp').read_text()
  self.assertEqual(cns_lease_union(text),(text,0))
  self.assertNotIn('(:park :pool class',text)
  event=(ROOT/'books/assembly-callbacks-e-cns.lisp').read_text()
  self.assertEqual(event.count('(fn2-c-actor-loader-core-events)'),1)

class ActorPriority(unittest.TestCase):
 def test_selected_query_priority_is_distinct_from_wire_identity(self):
  selected=function('fn2-c-actor-tx-missp',parsed('books/c-actor-loader.lisp'))
  self.assertTrue(calls(selected,'fn2-run-cursors-priority'))
  self.assertFalse(calls(selected,'fn2-run-cursors-run'))

class ActorPark(unittest.TestCase):
 def test_checked_resolve_boundary_and_real_terminal_scan(self):
  fs=parsed('books/c-actor-loader.lisp')
  resolved=function('fn2-c-actor-loader-resolvedp',fs)
  for getter in ('fn2-succ-txns-ri','fn2-succ-txns-rstate','fn2-succ-txns-phase','fn2-txn-row-prepared','fn2-auth-row-wstep','fn2-cns-row-wstep'):
   self.assertTrue(calls(resolved,getter),getter)
  park=function('fn2-c-actor-loader-park-step',fs)
  for helper in ('fn2-c-actor-loader-resolvedp','fn2-c-actor-loader-parkedp','fn2-run-load-park-source'):
   self.assertTrue(calls(park,helper),helper)
  self.assertFalse(calls(park,'fn2-run-page-release'))
  terminal=function('fn2-c-actor-loader-parkedp',fs)
  for getter in ('fn2-run-loads-pending','fn2-run-loads-lease-mode','fn2-checkpoint-summary-leases-live','fn2-pool-workspace-code'):
   self.assertTrue(calls(terminal,getter),getter)

if __name__=='__main__':unittest.main()
