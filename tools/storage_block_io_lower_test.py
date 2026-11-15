#!/usr/bin/env python3
"""Source-identity controls for the owning B primitive separation; no ACL2."""
from pathlib import Path
import subprocess,unittest
import lisp_rewrite as lr
import storage_block_io_lower as rw
ROOT=Path(__file__).resolve().parents[1]
BASE='de31cba77741e057b78e00faa33539346340d3d8'
def read(p):return (ROOT/p).read_text()
def tree(n):
 if isinstance(n,lr.Pre):return (n.prefix,tree(n.node))
 return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low
class StorageBlockLower(unittest.TestCase):
 def test_every_original_function_guard_and_contract_is_exact(self):
  before=read('tools/fixtures/storage-block-io-before.lisp');a,b,c=rw.transform(before,'(include-book "machines-b")\n(defun unchanged () 1)')
  originals=[tree(n) for n in rw.selected(before)]
  actual=[tree(n) for n in rw.selected(read('books/storage-block-io.lisp'))]
  self.assertEqual(originals,actual);self.assertEqual(originals,[tree(n) for n in rw.selected(c)])
  self.assertFalse(lr.match('(defun fn2-pinned-block-io-children ?*b)',lr.parse(a).forms,deep=False))
  self.assertIn('unrelated-reserve',a);self.assertIn('defcost fn2-block-read',a);self.assertIn('defcost fn2-block-write',a)
  self.assertIn('(defun unchanged () 1)',b)
 def test_actual_registry_changes_only_the_selected_owning_forms(self):
  before=subprocess.check_output(['git','show',BASE+':books/machines-b.lisp'],cwd=ROOT,text=True)
  resources='(include-book \"machines-b\")\n'
  a,b,c=rw.transform(before,resources)
  self.assertEqual(a,read('books/machines-b.lisp'));self.assertEqual(b,'(include-book \"storage-block-io\")\n');self.assertEqual(c,read('books/storage-block-io.lisp'))
 def test_local_encapsulation_and_all_eight_results_remain_whole(self):
  leaf=read('books/storage-block-io.lisp');enc=[n for n in lr.parse(leaf).forms if hasattr(n,'items') and n.items and n.items[0].low=='encapsulate']
  self.assertEqual(len(enc),1)
  for text in ('stobjs-out','fn2-extents 6','fn2-alloc-edges 7','fn2-block-issue-identity-events','fn2-issued-wrapper-events','fn2-issue-wrapper-effect-events'):self.assertIn(text,leaf)
 def test_leaf_imports_only_the_existing_production_pilot_roots(self):
  leaf=read('books/storage-block-io.lisp')
  for name in ('arm-issue-effects','read-pins','commit-geometry'):self.assertIn('(include-book "'+name+'")',leaf)
  for name in ('machines-b','core','commit','checkpoint'):self.assertNotIn('(include-book "'+name+'")',leaf)
  self.assertNotIn('defcost ',leaf)
 def test_missing_or_duplicate_subject_fails_closed(self):
  before=read('tools/fixtures/storage-block-io-before.lisp')
  for s in ('',before+before):
   with self.assertRaises(ValueError):rw.transform(s,'(include-book "machines-b")')
  with self.assertRaises(ValueError):rw.transform(before,'(include-book "other")')
if __name__=='__main__':unittest.main()
