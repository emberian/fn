"""Byte-accounting source controls only; leaf structural step contract is unresolved."""
import subprocess,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import loader_actor_cost_projection
PARENT='255b5d598e3265c0ebe90a0f6c1e6cacdf97ebea'
def original(ref,path):return subprocess.check_output(['git','show',ref+':'+path],cwd=ROOT,text=True)
def forms(text):
 return {(n.items[0].low,lr.flat(n.items[1])):lr.flat(n) for n in lr.parse(text).forms if isinstance(n,lr.Lst) and len(n.items)>1 and isinstance(n.items[0],lr.Atom)}
class ActorByteCost(unittest.TestCase):
 def test_cost_projection_changes_only_the_six_source_charge_sites(self):
  path='books/checkpoint-master-arms.lisp';before=original(PARENT,path)
  after=loader_actor_cost_projection.transform(before)
  self.assertEqual((ROOT/path).read_text(),after)
  self.assertEqual(after.count(loader_actor_cost_projection.TURN),6)
  self.assertEqual(loader_actor_cost_projection.transform(after),after)
  self.assertEqual(after.replace(loader_actor_cost_projection.TURN,'4096'),before)
 def test_current_master_states_and_nonbyte_quota_are_preserved(self):
  path='books/checkpoint-master-state.lisp'
  before=forms(original(PARENT,path));after=forms((ROOT/path).read_text())
  for key,value in before.items():
   actual=after.get(key)
   if key==('defmachine','fn2-checkpoint-master'):
    actual=actual.replace('*fn2-checkpoint-master-byte-budget*','16384').replace(':budget-cost',':budget')
   self.assertEqual(actual,value,key)
 def test_each_actual_master_arm_has_at_most_one_C_cost_root1_call(self):
  text=(ROOT/'books/checkpoint-master-arms.lisp').read_text()
  definition=next(n for n in lr.parse(text).forms if isinstance(n,lr.Lst) and n.items[0].low=='defmachine-arms')
  index=next(i for i,n in enumerate(definition.items) if isinstance(n,lr.Atom) and n.low==':arms')
  arms=definition.items[index+1].items
  names={'fn2-checkpoint-root1-'+n+'-op' for n in ('begin','select','bind','consume','work','payload-start','retention','closure','step')}
  for arm in arms:
   calls=lr.match('(:do ?outputs (?op ?*args) ?*tail)',[arm],deep=True)
   costly=[m for m in calls if isinstance(m.captures['op'],lr.Atom) and m.captures['op'].low in names]
   self.assertLessEqual(len(costly),1,lr.flat(arm.items[0]))
if __name__=='__main__':unittest.main()
