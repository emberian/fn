"""Pure preflight equivalence/refusal-order control; not work qualification."""
from pathlib import Path
import copy,subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def defun(s,name):return next(read_sexp(f) for f in forms(s) if f.startswith('(defun '+name+' '))
def gate(f):
 return next(b for b in f[-1][1] if isinstance(b,list) and len(b)==2 and isinstance(b[1],list) and b[1][:2]==['mv',':authority'])
def same_guard(old,new):
 a,b=gate(old),gate(new)
 return a[1]==b[1] and a[0][1][0]=='and' and b[0][1]==['and',a[0][1][-1],*a[0][1][2:-1]]
class ConsumePreflight(unittest.TestCase):
 def test_same_predicates_and_same_authority_failure_before_any_mutation(self):
  old=defun(subprocess.check_output(['git','show','88f7d786d:books/checkpoint-directory-consume.lisp'],cwd=ROOT,text=True),'fn2-directory-rebase-consume')
  new=defun((ROOT/'books/checkpoint-directory-consume.lisp').read_text(),'fn2-directory-rebase-consume')
  self.assertTrue(same_guard(old,new))
  before,after=copy.deepcopy(old),copy.deepcopy(new)
  before[-1][1].remove(gate(before));after[-1][1].remove(gate(after))
  self.assertEqual(before,after)
  mutant=copy.deepcopy(new);gate(mutant)[0][1].pop(1)
  self.assertFalse(same_guard(old,mutant))
 def test_subject_contains_the_exact_removed_authority_complete_check(self):
  f=defun((ROOT/'books/event-catalog.lisp').read_text(),'fn2-event-catalog-subject-p')
  calls=[x for x in f[-1] if isinstance(x,list) and x and x[0]=='fn2-checkpoint-summary-authority-row-complete-p']
  self.assertEqual(calls,[['fn2-checkpoint-summary-authority-row-complete-p','r','fn2-checkpoint-summary-authority','fn2-checkpoints','fn2-checkpoint-refs','fn2-checkpoint-bytes']])
  consume=defun((ROOT/'books/checkpoint-directory-consume.lisp').read_text(),'fn2-directory-rebase-consume')
  self.assertEqual(gate(consume)[0][1][1][:2],['fn2-event-catalog-subject-p','1'])
 def test_cost_face_is_not_bound_to_the_rejected_expression_counter(self):
  s=(ROOT/'books/checkpoint-directory-consume.lisp').read_text()
  self.assertNotIn('*fn2-directory-consume-directory-rebase-consume-evals*',s)
if __name__=='__main__':unittest.main()
