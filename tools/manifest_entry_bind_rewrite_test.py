#!/usr/bin/env python3
"""Preserve every actual schema10 field when sharing the no-filter binder."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import manifest_entry_bind_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def tree(n):return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
class ManifestBind(unittest.TestCase):
 def test_generated_helper_retains_all_original_field_assignments(self):
  old=read('tools/fixtures/manifest-bind-root1.lisp')
  helper=rw.helper(old)
  _,before,fields=rw.extract(old,'defun','fn2-checkpoint-metadata-manifest-emit')
  n=lr.match('(defun fn2-manifest-bind-unfiltered ?*body)',lr.parse(helper).forms,deep=False)[0].node
  assignments=lr.match('(fn2-fields ?value)',[n])
  self.assertEqual(len(assignments),12)
  self.assertEqual(set(fields),rw.EXPECTED)
  # The two digest windows and all canonical absent-filter zeros are verbatim.
  for field in ['root-hash','filter-hash','filter-unit','filter-epoch','filter-allocation']:
   self.assertIn(tree(fields[field][0]),[tree(x.node) for x in assignments])
 def test_both_producers_supply_the_exact_old_values(self):
  for fixture,head,name,refusal in [('root1','defun','fn2-checkpoint-metadata-manifest-emit','(fn2-checkpoint-metadata-manifest-emit-mv field-code)'),
     ('archive','fn2-event-archive-operation','fn2-event-archive-manifest-emit','(mv field-code fn2-event-archive fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)')]:
   old=read('tools/fixtures/manifest-bind-'+fixture+'.lisp')
   _,_,fields=rw.extract(old,head,name)
   after=rw.replace(old,head,name,refusal)
   call=lr.match('(fn2-manifest-bind-unfiltered ?*args)',lr.parse(after).forms)[0].node
   values=[tree(fields[f][1].items[2]) for f in rw.SCALARS]
   self.assertEqual([tree(x) for x in call.items[2:9]],values)
   self.assertEqual(len(call.items)-1,11)
   self.assertIn(refusal,after)
 def test_no_field_setter_class_remains_in_actual_emitters(self):
  for book,head,name in [('checkpoint-metadata-manifest.lisp','defun','fn2-checkpoint-metadata-manifest-emit'),
                         ('event-archive-manifest.lisp','fn2-event-archive-operation','fn2-event-archive-manifest-emit')]:
   n=lr.match('('+head+' '+name+' ?*body)',lr.parse(read('books/'+book)).forms,deep=False)[0].node
   self.assertEqual(len(lr.match('(fn2-manifest-bind-unfiltered ?*args)',[n])),1)
   self.assertFalse(lr.match('(fn2-fields-set-value ?*args)',[n]))
if __name__=='__main__':unittest.main()
