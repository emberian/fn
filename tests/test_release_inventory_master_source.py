"""Actual master/rearm routing; source controls only, no ACL2 execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def source(name):return (ROOT/'books'/(name+'.lisp')).read_text()
def tree(name):return [read_sexp(f) for f in forms(source(name))]
def named(name,head,key):return next(n for f in tree(name) for n in walk(f) if n[:2]==[head,key])
def arm(phase):
 node=named('checkpoint-master-arms','defmachine-arms','fn2-checkpoint-master')
 return next(n for n in node[node.index(':arms')+1] if n and n[0]==phase)
def rearm_terminal_bound(code):
 return 'fn2-release-inventory-transfer-terminal-p' in str(code) and 'fn2-event-producer-donep' in str(code)
class Master(unittest.TestCase):
 def test_postthaw_actual_transfer_dominates_rearm(self):
  thaw=arm(':thaw');transfer=arm(':inventory-transfer');rearm=arm(':event-rearm')
  self.assertIn([':next',':inventory-transfer'],list(walk(thaw)))
  self.assertNotIn([':next',':event-rearm'],list(walk(thaw)))
  self.assertIn(['fn2-checkpoint-events-transfer','budget'],list(walk(transfer)))
  self.assertEqual(str(transfer).count('fn2-checkpoint-events-transfer'),1)
  self.assertIn([':next',':event-rearm'],list(walk(transfer)))
  self.assertIn([':next',':uncertain'],list(walk(transfer)))
  self.assertIn([':yield'],list(walk(transfer)))
  self.assertNotIn(':idle',str(transfer));self.assertNotIn(':park',str(transfer))
  self.assertIn(['fn2-checkpoint-events-rearm'],list(walk(rearm)))
 def test_exact_real_carrier_footprint_and_stable_appended_phase(self):
  cost=named('event-build-kind','defcost','fn2-checkpoint-events-transfer')
  self.assertEqual(cost[3],'fn2-release-inventory-transfer-step')
  table=cost[cost.index(':tables')+1]
  children=next(f[2][1] for f in tree('release-inventory-transfer') if f[:2]==['defconst','*fn2-release-inventory-transfer-children*'])
  self.assertEqual(table,[n.replace('fn2-','fn2-core-',1) for n in children])
  state=named('checkpoint-master-state','defmachine','fn2-checkpoint-master')
  self.assertEqual(state[state.index(':states')+1][-1],':inventory-transfer')
  self.assertIn([':inventory-transfer'],state[state.index(':arms')+1])
  self.assertNotIn(':inventory-transfer',str(state[state.index(':holds')+1]))
  self.assertIn('(defconst *fn2-checkpoint-activation-qualified* nil)',source('checkpoint-master-state'))
 def test_atomic_rearm_cannot_forget_untransferred_obligations(self):
  rearm=named('event-rearm','defun','fn2-event-producer-rearm')
  self.assertTrue(rearm_terminal_bound(rearm))
  self.assertFalse(rearm_terminal_bound(str(rearm).replace('fn2-release-inventory-transfer-terminal-p','MUTANT')))
  calls=list(walk(rearm));names=[n[0] for n in calls if n]
  self.assertLess(names.index('fn2-release-inventory-transfer-terminal-p'),names.index('fn2-release-inventory-build-init'))
  self.assertEqual(names.count('fn2-release-inventory-build-init'),1)
  self.assertIn(['fn2-release-inventory-build-init','1','fn2-release-inventory-build'],calls)
  for owner in ('fn2-event-producer-writer-request-p','fn2-checkpoint-lifecycle-ownerp','fn2-event-producer-donep'):
   self.assertIn(owner,names)
  for forbidden in ('fn2-alloc-free','fn2-release-evidence-init','fn2-checkpoint-refs-init','fn2-mk-init'):
   self.assertNotIn(forbidden,names)
if __name__=='__main__':unittest.main()
