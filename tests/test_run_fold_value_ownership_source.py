"""Source controls for the real declaration gate; no ACL2 evaluation."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def parsed(p):return [read_sexp(x) for x in forms(p.read_text())]
def defs():return {f[1]:f for f in parsed(ROOT/'books/runs-schema.lisp') if isinstance(f,list) and f and f[0]=='defun'}
def calls(f,name):return [x for x in walk(f) if x and x[0]==name]
class FoldOwnership(unittest.TestCase):
 def test_real_constructor_rejects_borrowed_fold_before_layouts(self):
  d=defs();constructor=d['fn2-defrunschema'];cond=next(x for x in walk(constructor) if x and x[0]=='cond')
  self.assertEqual(cond[1][0],['and','fold',['not',['fn2-rf-valuesp','value']]])
  self.assertTrue(calls(d['fn2-rf-okp'],'fn2-rf-valuesp'))
  self.assertTrue(calls(d['fn2-rf-valuesp'],'fn2-rf-value-kindp'))
 def test_scalar_classifier_cannot_acquire_ref_types(self):
  d=defs();kind=d['fn2-rf-value-kindp'];allowed=next(x[2][1] for x in walk(kind) if len(x)==3 and x[:2]==['member-eq','kind'])
  self.assertEqual(set(allowed),{':u8',':u16',':u32',':u60',':bool',':varint'})
  self.assertNotIn(':digest',allowed)
  self.assertIn(['eq',['car','kind'],':id'],list(walk(kind)))
 def test_all_actual_served_fold_values_use_that_same_classifier(self):
  d=defs();kind=d['fn2-rf-value-kindp'];allowed=set(next(x[2][1] for x in walk(kind) if len(x)==3 and x[:2]==['member-eq','kind']))
  folds=[]
  for book in ('identity','ordered','authority-schema','folds','runs-manifest'):
   for f in parsed(ROOT/'books'/(book+'.lisp')):
    if not isinstance(f,list) or not f or f[0]!='defrunschema' or ':fold' not in f:continue
    values=f[f.index(':value')+1];folds.append(f[1])
    for field in values:
     typ=field[1]
     self.assertTrue(typ in allowed if isinstance(typ,str) else typ[0]==':id',(f[1],field))
  self.assertEqual(len(folds),7)
  self.assertIn('fn2-identity-summary',folds)
  self.assertIn('fn2-authority-head',folds)
 def test_union_does_not_confuse_large_value_octets_with_key_bounds(self):
  d=defs();ints=d['fn2-rs-int-valuesp']
  self.assertTrue(calls(ints,'fn2-rs-scalar-value-kindp'))
  self.assertFalse(calls(ints,'fn2-rs-octetsp'))
  ctor=d['fn2-defrunschema']
  self.assertTrue(calls(ctor,'fn2-rs-int-valuesp'))
 def test_prepared_controls_nonvacuous_and_fold_specific(self):
  text=(ROOT/'tests/run-fold-value-ownership-unit.lisp').read_text()
  self.assertIn('fn2-rf-owned-control',text)
  self.assertIn('fn2-rf-borrowed-control',text)
  self.assertIn('fn2-rf-byte-control',text)
  self.assertIn('fn2-rf-unique-control',text)
  self.assertIn('fn2-rf-union-control',text)
  self.assertIn('(< 0 (fn2-rs-fold-descriptor-count',text)
  self.assertIn('(fn2-rs-fold-values-ownedp',text)
if __name__=='__main__':unittest.main()
