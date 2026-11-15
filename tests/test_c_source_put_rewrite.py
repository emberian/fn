"""Actual endpoint PUT macro ABI controls; no ACL2 macro evaluation."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from c_source_put_rewrite import transform,FIELDS
from lisp_rewrite import parse,match,Lst,Atom
class SourcePut(unittest.TestCase):
 def test_declared_macro_abi_is_field_pairs_and_implicit_stobj(self):
  columns=(ROOT/'books/columns.lisp').read_text()
  self.assertIn('(defmacro ,(fn2-columns-sym name "-PUT") (slot &rest fields)',columns)
  self.assertIn("(fn2-columns-put-expansion ',name ',cols ',put-policy slot fields)",columns)
  self.assertIn('(fn2-columns-put-bindings (fn2-columns-sym name "-SET") name slot fields)',columns)
 def test_actual_provider_and_teeth_have_only_valid_macro_pairs(self):
  counts=[]
  for filename in ('books/c-source-observer.lisp','tests/c-source-endpoint-unit.lisp'):
   src=(ROOT/filename).read_text();self.assertEqual(transform(src),(src,0));calls=[]
   for table,fields in FIELDS.items():
    for found in match(f'({table}-put ?*args)',parse(src).forms):
     node=found.node;calls.append(node)
     for pair in node.items[2:]:
      self.assertIsInstance(pair,Lst);self.assertEqual(len(pair.items),2)
      self.assertIsInstance(pair.items[0],Atom);self.assertIn(pair.items[0].low,fields)
   counts.append(len(calls))
  self.assertEqual(counts,[7,2])
 def test_whole_repair_class_keeps_field_order_and_dynamic_values(self):
  old='''(fn2-c-source-control-put 0
 `((readers ,count) (next-receipt ,receipt)
   (wake-pending ,(if wake 1 (fn2-c-source-control-wake-pending 0 fn2-c-source-control)))) fn2-c-source-control)'''
  fixed,n=transform(old);self.assertEqual(n,1)
  self.assertEqual(fixed,'''(fn2-c-source-control-put 0
        (readers count)
        (next-receipt receipt)
        (wake-pending (if wake 1 (fn2-c-source-control-wake-pending 0 fn2-c-source-control))))''')
  self.assertEqual(transform(fixed),(fixed,0))
  literal,n=transform("(fn2-c-source-readers-put endpoint '((live 0) (serial 0)) fn2-c-source-readers)")
  self.assertEqual(n,1);self.assertEqual(literal,'(fn2-c-source-readers-put endpoint\n        (live 0)\n        (serial 0))')
  symbol,n=transform("(fn2-c-source-control-put 0 '((phase idle)) fn2-c-source-control)")
  self.assertEqual(symbol,"(fn2-c-source-control-put 0\n        (phase 'idle))")
 def test_refuses_bad_alist_stobj_or_field_shape(self):
  for bad in (
   '(fn2-c-source-control-put 0 `((readers ,@xs)) fn2-c-source-control)',
   '(fn2-c-source-control-put 0 `((unknown ,count)) fn2-c-source-control)',
   '(fn2-c-source-control-put 0 `((readers ,count) (readers 0)) fn2-c-source-control)',
   '(fn2-c-source-control-put 0 `((readers ,count)) other-stobj)',
   '(fn2-c-source-control-put 0 (readers count) fn2-c-source-control)',
  ):
   with self.subTest(bad=bad),self.assertRaises(ValueError):transform(bad)
if __name__=='__main__':unittest.main()
