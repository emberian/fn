#!/usr/bin/env python3
"""Preserve actual declarations/bodies while removing orchestration dependencies."""
import unittest
from pathlib import Path
import lisp_rewrite as lr
import boot_geometry_lower_rewrite as rewrite
ROOT=Path(__file__).resolve().parents[1]
def read(path):return (ROOT/path).read_text()
def pick(s,pattern):return lr.match(pattern,lr.parse(s).forms,deep=False)[0].node
def tree(n):return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
class LowerGeometry(unittest.TestCase):
 def test_parent_current_whole_declaration_is_preserved(self):
  before=read('tools/fixtures/boot-geometry-boot-kind.lisp')
  after,lower=rewrite.kind(before)
  for head,name in [('defconst','*fn2-boot-group-entry-bytes*'),('defcolumns','fn2-boot-config')]:
   pattern='('+head+' '+name+' ?*body)'
   self.assertEqual(tree(pick(before,pattern)),tree(pick(lower,pattern)))
   self.assertFalse(lr.match(pattern,lr.parse(after).forms,deep=False))
  self.assertIn('(defconst *unrelated-bank-state* 91)',after)
 def test_new_fields_are_not_lost_by_replaying_extraction(self):
  before=read('tools/fixtures/boot-geometry-boot-kind.lisp')
  before=before.replace(':extra-fields\n (',':extra-fields\n ((fn2-boot-config-new-epoch :type (unsigned-byte 60) :initially 0 :why "Current source field.") ')
  _,lower=rewrite.kind(before)
  self.assertEqual(tree(pick(before,'(defcolumns fn2-boot-config ?*body)')),tree(pick(lower,'(defcolumns fn2-boot-config ?*body)')))
 def test_geometry_helper_bodies_and_contracts_are_unchanged(self):
  before=read('tools/fixtures/boot-geometry-checkpoint-boot.lisp')
  _,lower=rewrite.geometry(before)
  for head,name in [('defun','fn2-checkpoint-boot-geometry-word'),('defthm','fn2-checkpoint-boot-geometry-word-type'),
                    ('defun','fn2-checkpoint-boot-geometry-copy'),('defun','fn2-checkpoint-boot-geometry-load'),
                    ('fn2-digests-preserves','fn2-checkpoint-boot-geometry-load')]:
   p='('+head+' '+name+' ?*body)';self.assertEqual(tree(pick(before,p)),tree(pick(lower,p)))
   self.assertEqual(tree(pick(lower,p)),tree(pick(read('books/boot-geometry-state.lisp'),p)))
 def test_bound_engine_has_no_catalog_or_boot_orchestration_include(self):
  seen=set()
  def visit(name):
   if name in seen:return
   seen.add(name);path=ROOT/'books'/(name+'.lisp')
   if not path.exists():return
   for call in lr.match('(include-book ?name ?*opts)',lr.parse(path.read_text()).forms,deep=False):
    n=call.captures['name'];value=path.read_text()[n.start:n.end].strip('"')
    if '/' not in value:visit(value)
  visit('run-physical-bound-step')
  self.assertNotIn('checkpoint-summary-leases',seen)
  self.assertNotIn('checkpoint-summary-catalog',seen)
  self.assertNotIn('boot-kind',seen)
  self.assertNotIn('checkpoint-boot',seen)
if __name__=='__main__':unittest.main()
