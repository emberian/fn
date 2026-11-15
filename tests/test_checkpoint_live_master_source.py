"""Actual master route/emission source controls; no macroexecution/admission."""
from pathlib import Path
import json,re,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_live_master_rewrite import state,arms,assembly,PHASES
BEFORE=json.loads((ROOT/'tools/fixtures/checkpoint-live-master-before.json').read_text())
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def tree(name):return [read_sexp(f) for f in forms((ROOT/'books'/(name+'.lisp')).read_text())]
def arm(name):
 xs=next(x for x in tree('checkpoint-master-arms') if x[:2]==['defmachine-arms','fn2-checkpoint-master'])
 return next(x for x in xs[xs.index(':arms')+1] if x[0]==name)
def edges(x):return [y[1] for y in walk(x) if len(y)==2 and y[0]==':next']
def ordered_source_events():
 seen=set();active=set();events=[]
 def visit(p):
  p=p.resolve()
  if p in active:raise AssertionError('include cycle '+str(p))
  if p in seen:return
  seen.add(p);active.add(p)
  if not p.exists():raise AssertionError('missing source '+str(p))
  for f in forms(p.read_text()):
   m=re.match(r'\(include-book\s+"([^"]+)"',f,re.I)
   if m and ':dir' not in f:visit(p.parent/(m[1]+'.lisp'))
   else:events.append((p,read_sexp(f)))
  active.remove(p)
 visit(ROOT/'books/assembly-attach.lisp');return events
class LiveMaster(unittest.TestCase):
 def test_actual_named_transform_and_idempotence(self):
  for name,fn in [('checkpoint-master-state',state),('checkpoint-master-arms',arms)]:
   got,n=fn(BEFORE[name]);self.assertGreaterEqual(n,3);self.assertEqual(got,(ROOT/'books'/(name+'.lisp')).read_text())
   self.assertEqual(fn(got),(got,0))
  c,e,n=assembly(BEFORE['assembly-callbacks-c'],BEFORE['assembly-callbacks-e-cns']);self.assertEqual(n,3)
  self.assertEqual(assembly(c,e),(c,e,0))
 def test_declared_complete_phase_hold_class(self):
  x=next(x for x in tree('checkpoint-master-state') if x[:2]==['defmachine','fn2-checkpoint-master'])
  self.assertTrue(set(PHASES).issubset(x[x.index(':states')+1]))
  holds=x[x.index(':holds')+1];decl=x[x.index(':arms')+1]
  for p in PHASES:self.assertIn([p,':storage-window',':storage-window'],holds);self.assertIn([p],decl)
  self.assertIn(['defconst','*fn2-checkpoint-activation-qualified*','nil'],tree('checkpoint-master-state'))
 def test_actual_pipeline_keeps_archive_and_sole_consume_before_reopen(self):
  path=[(':summary-authority-copy',':live-catalog-begin'),(':live-catalog-begin',':live-catalog-copy'),(':live-catalog-copy',':live-cbase'),(':live-cbase',':live-exclusive'),(':live-exclusive',':live-install'),(':live-install',':live-retire'),(':live-retire',':live-readiness-begin'),(':live-readiness-begin',':live-readiness-scan'),(':live-readiness-scan',':live-promote'),(':live-promote',':rebase-begin'),(':rebase-begin',':rebase-source'),(':rebase-source',':rebase-archive'),(':rebase-archive',':rebase-consume'),(':rebase-consume',':live-reopen'),(':live-reopen',':release')]
  for a,b in path:self.assertIn(b,edges(arm(a)),a)
  for p in PHASES:
   if p!=':live-reopen':self.assertNotIn(':release',edges(arm(p)))
  old=next(x for f in forms(BEFORE['checkpoint-master-arms']) for x in [read_sexp(f)] if x[:2]==['defmachine-arms','fn2-checkpoint-master'])
  oldarms=old[old.index(':arms')+1]
  for p in (':rebase-begin',':rebase-source',':rebase-archive',':release',':thaw',':snapshot-release',':teardown-cold-copy'):
   self.assertEqual(arm(p),next(x for x in oldarms if x[0]==p),p)
 def test_writer_wait_is_runnable_and_real_faces_only(self):
  a=arm(':live-exclusive');self.assertIn(':waiting',str(a))
  branch=next(x for x in walk(a) if x and x[0]==[':waiting'])
  self.assertIn(':runnable',str(branch));self.assertNotIn(':yield',str(branch))
  for p in PHASES:self.assertNotIn(':issue',str(arm(p)))
  self.assertIn('fn2-checkpoint-live-replace-finish-op',str(arm(':live-promote')))
  self.assertIn('fn2-checkpoint-live-replace-reopen-op',str(arm(':live-reopen')))
 def test_actual_emission_dag_orders_needed_functions_before_master(self):
  events=ordered_source_events();names=[x[0] if isinstance(x,list) and x and isinstance(x[0],str) else '' for _,x in events]
  self.assertEqual(names.count('fn2-checkpoint-master-events'),1)
  master=names.index('fn2-checkpoint-master-events')
  providers={'fn2-c-actor-loader-core-events':'fn2-c-actor-loader-plan','fn2-run-load-readiness-core-events':'fn2-run-load-readiness-owned-step','fn2-checkpoint-live-finish-events':'fn2-checkpoint-live-replace-finish'}
  for macro,fun in providers.items():
   self.assertLess(names.index(macro),master,macro)
   defs=[x for _,f in events[:master] for x in walk(f) if x[:2]==['defmacro',macro]]
   self.assertEqual(len(defs),1);self.assertTrue(any(x[:2]==['defun',fun] for x in walk(defs[0])))
  self.assertEqual(events[master][0].name,'assembly-callbacks-e-cns.lisp')
 def test_pure_byte_quantum_is_independent_of_descriptor_credit(self):
  names=('fn2-checkpoint-root1-step-op','fn2-checkpoint-events-step','fn2-checkpoint-map-source-step-op','fn2-checkpoint-build-source-op')
  actual=tree('checkpoint-master-arms')
  def contract(t):
   return all(len([x for x in walk(t) if x and x[0]==n])==1 and
              next(x for x in walk(t) if x and x[0]==n)[1]=='*fn2-checkpoint-master-pure-byte-quantum*' for n in names)
  self.assertTrue(contract(actual))
  import copy
  mutant=copy.deepcopy(actual);next(x for x in walk(mutant) if x and x[0]==names[0])[1]='budget'
  self.assertFalse(contract(mutant))
  self.assertIn(['defconst','*fn2-checkpoint-master-pure-byte-quantum*','*fn2-commit-unit-bytes*'],tree('checkpoint-master-work'))
  for p in (':root1-read',':events-read'):
   old=next(x for f in forms(BEFORE['checkpoint-master-arms']) for top in [read_sexp(f)] if top[:2]==['defmachine-arms','fn2-checkpoint-master'] for x in top[top.index(':arms')+1] if x[0]==p)
   self.assertEqual(arm(p),old)
  for op in ('fn2-checkpoint-master-abort-step-op','fn2-checkpoint-root1-consume-op','fn2-checkpoint-root1-release-op','fn2-checkpoint-build-bind-op','fn2-checkpoint-build-consume-op'):
   self.assertTrue(all(x[1]=='budget' for x in walk(actual) if x and x[0]==op),op)
 def test_four_pure_results_charge_bytes_including_page_wait_yield(self):
  expected={':root1-source':'*fn2-checkpoint-root1-turn-bytes*',':events-source':'4096',':map-source':'4096',':descriptor-source':'4096'}
  for phase,byte in expected.items():
   a=arm(phase)
   self.assertFalse(any(x in [[':yield'],[':idle']] for x in walk(a)),phase)
   for x in walk(a):
    if x and x[0]==':charge':
     self.assertEqual(x[x.index(':bytes')+1],byte,phase)
     self.assertEqual(x[x.index(':steps')+1],'*fn2-work-stage*',phase)
   waits=[x for x in walk(a) if x and x[0]==[':wait']]
   for x in waits:self.assertEqual(x[1][-1],'nil')
   for x in walk(a):
    if x and x[0]==[':page']:
     self.assertTrue(any(y and y[0]==':charge' and y[y.index(':bytes')+1]==byte for y in walk(x)))
 def test_full_post_do_charges_include_refusal_and_controller(self):
  expected={':live-catalog-begin':('64','*fn2-master-live-one-turn-steps*'),':live-catalog-copy':('64','*fn2-master-live-two-turn-steps*'),':live-cbase':('32','*fn2-master-live-two-turn-steps*'),':live-exclusive':('64','*fn2-master-live-two-turn-steps*'),':live-install':('64','*fn2-master-live-three-turn-steps*'),':live-retire':('64','*fn2-master-live-three-turn-steps*'),':live-readiness-begin':('0','*fn2-master-live-one-turn-steps*'),':live-readiness-scan':('0','*fn2-master-live-three-turn-steps*'),':live-promote':('*fn2-checkpoint-live-promotion-bytes*','*fn2-master-promote-turn-steps*'),':live-reopen':('*fn2-checkpoint-live-reopen-bytes*','*fn2-master-reopen-turn-steps*'),':rebase-consume':('*fn2-directory-rebase-consume-bytes*','*fn2-master-consume-turn-steps*')}
  for phase,(byte,step) in expected.items():
   for x in walk(arm(phase)):
    if x and x[0]==':charge':
     if ':bytes' not in x:
      self.assertEqual(x[2],'*fn2-master-three-case-controller-steps*');continue
     self.assertEqual(x[x.index(':bytes')+1],byte,phase)
     self.assertEqual(x[x.index(':steps')+1],step,phase)
  prepared=(ROOT/'tests/checkpoint-master-controller-source-unit.lisp').read_text()
  for n in ('fn2-arms-events','fn2-machine-work-ceiling','fn2-run-quantitiesp','fn2-machine-registry-quantity-max'):
   self.assertIn('('+n+' ',prepared)
 def test_partial_class_is_refused(self):
  with self.assertRaises(ValueError):state(BEFORE['checkpoint-master-state'].replace(':states (',':states (:live-promote ',1))
  with self.assertRaises(ValueError):arms(BEFORE['checkpoint-master-arms'].replace('(:next :release)','(:next :uncertain)',1))
if __name__=='__main__':unittest.main()
