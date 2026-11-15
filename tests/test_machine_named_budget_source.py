"""Source boundary controls for named-budget reentry, not ACL2 admission."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from lisp_source import forms,read_sexp
ROOT=Path(__file__).resolve().parents[1]
def walk(x):
 if isinstance(x,list):
  yield x
  for v in x:yield from walk(v)
class NamedBudgetSource(unittest.TestCase):
 def setUp(self):
  self.source=(ROOT/'books/machines.lisp').read_text()
  self.defs={f[1]:f for raw in forms(self.source) if isinstance((f:=read_sexp(raw)),list) and f and f[0] in ('defun','defmacro')}
 def test_only_declared_cost_resolution_reenters_same_generator(self):
  f=self.defs['fn2-machine-budget-event']
  calls=[x for x in walk(f) if x and x[0]=='fn2-cost-value']
  self.assertEqual(len(calls),3)
  self.assertIn(['cons',['quote','defmachine'],['cons','name',['fn2-decl-set',':budget',['list',':bytes','bytes',':steps','steps',':descriptors','descriptors'],'args']]],list(walk(f)))
  self.assertFalse(any(x and x[0] in ('eval','trans-eval','read') for x in walk(f)))
 def test_all_dimensions_require_actual_naturals(self):
  f=self.defs['fn2-machine-budget-event']
  for dim in ('bytes','steps','descriptors'):self.assertIn(['natp',dim],list(walk(f)))
  self.assertIn(['and',['natp','bytes'],['natp','steps'],['natp','descriptors']],list(walk(f)))
 def test_literal_path_and_every_declaration_argument_preserved(self):
  f=self.defs['defmachine']; terms=list(walk(f))
  self.assertTrue(any(x and x[0]=='fn2-machine-events' for x in terms))
  args=next(x for x in terms if x and x[0]=='list' and len(x)>3 and x[1:3]==[':states','states'])
  for key in ('states','phases','fields','budget','continuations','observes','capacity','initial','holds','admission','taken','arms','subarms','stops','links','sub','genesis'):
   self.assertIn(':'+key,args);self.assertIn(key,args)
 def test_prepared_positive_and_refusal_controls_are_explicit(self):
  s=(ROOT/'tests/machine-named-budget-unit.lisp').read_text()
  for name in ('fn2-budget-literal','fn2-budget-named','fn2-budget-derived','fn2-budget-unknown','fn2-budget-negative'):self.assertIn(name,s)
  self.assertEqual(s.count('(must-fail'),2)
if __name__=='__main__':unittest.main()
