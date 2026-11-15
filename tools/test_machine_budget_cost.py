from pathlib import Path
import json,unittest
from lisp_rewrite import parse,match
ROOT=Path(__file__).resolve().parents[1]
class BudgetCost(unittest.TestCase):
 def test_sole_literal_emitter_unchanged(self):
  f=json.loads((ROOT/'tools/fixtures/machine_budget_cost.json').read_text())
  self.assertEqual(f['literal'].replace('(defmacro defmachine ','(defmacro fn2-defmachine-literal ',1),f['emitter'])
  p=parse(ROOT/'books/machines.lisp')
  m=match(None,p.forms,deep=False,head='defmacro',name='fn2-defmachine-literal')[0]
  self.assertEqual(p.text[m.start:m.end],f['emitter'])
 def test_public_wrapper_preserves_literal_face(self):
  p=parse(ROOT/'books/machines.lisp');m=match(None,p.forms,deep=False,head='defmacro',name='defmachine')[0]
  s=p.text[m.start:m.end]
  self.assertIn('(member-eq :budget-cost args)',s)
  self.assertIn('`(fn2-defmachine-literal ,name ,@args)',s)
 def test_resolution_is_existing_acl2_cost_language(self):
  p=parse(ROOT/'books/machines.lisp');m=match(None,p.forms,deep=False,head='defun',name='fn2-machine-resolved-declaration')[0]
  s=p.text[m.start:m.end]
  for requirement in ['(fn2-cost-values cost world)','(fn2-cost-plistp cost)','(not (member-eq :budget args))','(natp (car values))','(natp (cadr values))','(natp (caddr values))']:
   self.assertIn(requirement,s)
if __name__=='__main__':unittest.main()
