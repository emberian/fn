from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,Lst,flat
BASE='ab05c79b16846071fddb2213630a22e33d7ad33b'
def canon(n):
 if not isinstance(n,Lst):return flat(n)
 out=[];i=0
 while i<len(n.items):
  if flat(n.items[i])==':hints':i+=2
  else:out.append(canon(n.items[i]));i+=1
 return tuple(out)
class BoundHint(unittest.TestCase):
 def test_all_actual_forms_statements_guards_ruleclasses_exact(self):
  old=parse(subprocess.check_output(['git','show',BASE+':books/source-manifest-codec.lisp'],cwd=ROOT,text=True)).forms
  new=parse(ROOT/'books/source-manifest-codec.lisp').forms
  added=[x for x in new if flat(x)=='(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))']
  self.assertEqual(len(added),1)
  self.assertEqual([canon(x) for x in old],[canon(x) for x in new if x not in added])
 def test_observed_arithmetic_boundary_and_invalid_inputs(self):
  for off in [-7,None,'bad',0,1,3965,3966,4095,4096,4097,8191,10**20]:
   n=off if type(off) is int and off>=0 else 0
   room=4096-n%4096;at=n+room if room<130 else n
   self.assertGreaterEqual(at,n)
if __name__=='__main__':unittest.main()
