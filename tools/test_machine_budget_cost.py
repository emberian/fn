from pathlib import Path
import json,unittest,subprocess
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
 def test_all_other_current_compiler_forms_including_enqueue_are_exact(self):
  before=subprocess.check_output(['git','show','d560fdf88acdff2c96fadf505d71e4fd751c5b60:books/machines.lisp'],cwd=ROOT,text=True)
  def named(text):
   p=parse(text)
   return {(n.items[0].low,p.text[n.items[1].start:n.items[1].end]):p.text[n.start:n.end] for n in p.forms if hasattr(n,'items') and len(n.items)>1 and hasattr(n.items[0],'low')}
  a=named(before);b=named((ROOT/'books/machines.lisp').read_text())
  for key,value in a.items():
   if key!=('defmacro','defmachine'):self.assertEqual(b.get(key),value,key)
 def test_actual_master_uses_supported_resolution_face(self):
  p=parse(ROOT/'books/checkpoint-master-state.lisp')
  m=match(None,p.forms,deep=False,head='defmachine',name='fn2-checkpoint-master')[0]
  text=p.text[m.start:m.end]
  self.assertIn(':budget-cost (:bytes *fn2-checkpoint-master-byte-budget* :steps 32 :descriptors 4)',text)
  self.assertNotIn(':budget (:bytes *fn2-checkpoint-master-byte-budget*',text)
 def test_actual_registry_and_refusal_witnesses_are_supplied_unexecuted(self):
  text=(ROOT/'tests/machine-budget-cost-unit.lisp').read_text()
  for name in ('fn2-budget-literal','fn2-budget-derived','fn2-budget-unknown','fn2-budget-runtime','fn2-budget-conflict'):self.assertIn(name,text)
  self.assertIn('(equal literal derived)',text)
  self.assertEqual(text.count('(must-fail'),3)
if __name__=='__main__':unittest.main()
