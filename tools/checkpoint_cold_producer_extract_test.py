from pathlib import Path
import unittest
import lisp_rewrite as lr
from checkpoint_cold_producer_extract import extract,HELPER
ROOT=Path(__file__).resolve().parents[1]
class Producer(unittest.TestCase):
 def setUp(self):
  self.before=(ROOT/'tools/fixtures/checkpoint-cold-path-unit-before-producer.lisp').read_text()
  self.helper,self.unit=extract(self.before)
 def test_actual_sources_equal_exact_extraction(self):
  self.assertEqual(self.helper,(ROOT/f'tests/{HELPER}.lisp').read_text())
  self.assertEqual(self.unit,(ROOT/'tests/checkpoint-cold-path-unit.lisp').read_text())
 def test_helpers_byte_unchanged_and_no_assertions(self):
  old=lr.parse(self.before).forms;new=lr.parse(self.helper).forms
  for node in old:
   if lr.match('(defun fn2-ccp-body ?*body)',[node],deep=False):break
   if isinstance(node,lr.Lst) and node.items and isinstance(node.items[0],lr.Atom) and node.items[0].low in ('defun','defconst'):
    matches=lr.match(lr.flat(node),new,deep=False);self.assertEqual(len(matches),1)
    self.assertEqual(self.before[node.start:node.end],self.helper[matches[0].node.start:matches[0].node.end])
  self.assertFalse(lr.match('(assert-event ?*body)',new,deep=False))
 def test_unit_body_and_existing_assertions_unchanged(self):
  old=lr.parse(self.before).forms;new=lr.parse(self.unit).forms
  a=lr.match('(defun fn2-ccp-body ?*body)',old,deep=False)[0].node.start
  b=lr.match('(defun fn2-ccp-body ?*body)',new,deep=False)[0].node.start
  self.assertEqual(self.before[a:],self.unit[b:])
 def test_repeat_and_missing_dependency_refuse(self):
  with self.assertRaises(ValueError):extract(self.unit)
  with self.assertRaises(ValueError):extract(self.before.replace('(include-book "checkpoint-cold-path-drive")',''))
if __name__=='__main__':unittest.main()
