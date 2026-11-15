"""Narrow structural rewrite controls; no ACL2/model execution."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from c_read_cost_rewrite import transform,STEP,CALLBACK
class ReadCostRewrite(unittest.TestCase):
 def test_reader_cost_and_physical_read_is_unchanged(self):
  s='(defcost fn2-read-next :bytes 4096)\n(defcost fn2-run-page-read :bytes 4096 :descriptors 1)'
  out,n=transform(s);self.assertEqual(n['costs'],1)
  self.assertIn(f'fn2-read-next :bytes {STEP}',out)
  self.assertIn('(defcost fn2-run-page-read :bytes 4096 :descriptors 1)',out)
 def test_reader_arm_only_preserves_old_expression(self):
  s='(defmachine-arms fn2-cursor :children :subarms ((lookup (:do (x) (fn2-read-lookup 0 1 4096)) (:charge :bytes (+ 4096 row-n))) (io (:do (x) (fn2-run-page-step 1 4096)) (:charge :bytes 4096))))'
  out,n=transform(s);self.assertEqual(n['charges'],1)
  self.assertIn(f'(:charge :bytes (+ {CALLBACK} (+ 4096 row-n)))',out)
  self.assertIn('(fn2-run-page-step 1 4096)) (:charge :bytes 4096)',out)
 def test_kind_budget_is_derived_and_idempotent(self):
  s='(fn2-c-actor-loader-kind fn2-cns :budget (:bytes 32768 :steps 32 :descriptors 4))'
  out,n=transform(s);self.assertEqual(n['budgets'],1)
  self.assertIn(f'(+ 32768 (* 17 {CALLBACK}))',out)
  again,n=transform(out);self.assertEqual(again,out);self.assertFalse(any(n.values()))
 def test_unknown_cost_refuses(self):
  with self.assertRaises(ValueError):transform('(defcost fn2-read-next :bytes 12)')
 def test_strings_comments_and_unrelated_kind_are_preserved(self):
  s='; fn2-read-next\n(defcost other :bytes 4096 :doc "fn2-read-next")\n(defmachine other :budget (:bytes 4096 :steps 32 :descriptors 4))'
  self.assertEqual(transform(s)[0],s)
 def test_actual_reader_templates_are_supported(self):
  s="(defmacro template () '(defmachine-arms fn2-cns :children :arms ((:read (:do (x) (fn2-cns-item-next 1)) (:charge :bytes 8192)))))"
  out,n=transform(s);self.assertEqual(n['charges'],1);self.assertIn(f'(+ {CALLBACK} 8192)',out)
if __name__=='__main__':unittest.main()
