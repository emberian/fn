#!/usr/bin/env python3
"""Source-identity controls for the owning B primitive separation; no ACL2."""
from pathlib import Path
import subprocess,unittest
import lisp_rewrite as lr
import storage_block_io_lower as rw
from add_pool_dimension_interfaces import request
ROOT=Path(__file__).resolve().parents[1]
BASE='de31cba77741e057b78e00faa33539346340d3d8'
IDENTITY_ADDITION="\n; The public read/write wrappers preserve the same successful reservation\n; identity as their actual pinned producer; no second implementation.\n(make-event\n (value (cons 'progn\n   (fn2-block-issue-identity-events\n    '(fn2-block-read-children fn2-block-write-children) (w state)))))\n"
def without_identity_addition(leaf):
 assert leaf.endswith(IDENTITY_ADDITION)
 return leaf[:-len(IDENTITY_ADDITION)]

def read(p):return (ROOT/p).read_text()
def tree(n):
 if isinstance(n,lr.Pre):return (n.prefix,tree(n.node))
 return tuple(tree(x) for x in n.items) if hasattr(n,'items') else n.low

def without_reviewed_dimensions(leaf):
 parsed=lr.parse(leaf).forms
 includes=lr.match('(include-book "pool-dimensions")',parsed,deep=False)
 assert len(includes)==1
 assert len(lr.match('(include-book "pool-dimensions")',parsed,deep=True))==1
 actual=lr.match('(fn2-pool-dimensions ?*body)',parsed,deep=True)
 expected=[lr.parse(request(name)).forms[0] for name in
           ('fn2-pinned-block-io-children','fn2-block-read-children','fn2-block-write-children')]
 assert [tree(x.node) for x in actual]==[tree(x) for x in expected]
 return lr.write(leaf,[(x.start,x.end,'') for x in includes+actual])

def forms(text):return [tree(x) for x in lr.parse(text).forms]

MOVED_FUNCTIONS=('fn2-block-issue-identity-events','fn2-pinned-block-io-children',
                 'fn2-block-read-children','fn2-block-write-children')

class StorageBlockLower(unittest.TestCase):
 def check_current_registry_contract(self,registry,leaf):
  before=subprocess.check_output(['git','show',BASE+':books/machines-b.lisp'],cwd=ROOT,text=True)
  _,resources,original_leaf=rw.transform(before,'(include-book "machines-b")\n')
  # The extracted implementation, guards, contracts and resource import are
  # still exact. Later registry layout changes do not belong to this move.
  self.assertEqual(resources,'(include-book "storage-block-io")\n')
  self.assertEqual(forms(without_reviewed_dimensions(leaf)),forms(original_leaf+IDENTITY_ADDITION))
  parsed=lr.parse(registry).forms
  self.assertEqual(len(lr.match('(include-book "storage-block-io")',parsed,deep=False)),1)
  self.assertEqual(len(lr.match('(include-book "storage-block-io")',parsed,deep=True)),1)
  for name in MOVED_FUNCTIONS:
   # Deep matching rejects a hidden LOCAL copy as well as a public twin.
   self.assertFalse(lr.match('(defun '+name+' ?*body)',parsed,deep=True),name)
  original=lr.parse(before).forms
  for operation,child in [('fn2-block-read','fn2-block-read-children'),
                          ('fn2-block-write','fn2-block-write-children')]:
   old=lr.match('(defcost '+operation+' ?*body)',original,deep=False)
   new=lr.match('(defcost '+operation+' ?*body)',parsed,deep=False)
   self.assertEqual(len(old),1);self.assertEqual(len(new),1)
   self.assertEqual(tree(old[0].node),tree(new[0].node))
   self.assertIn(':child '+child,registry[new[0].start:new[0].end])
   self.assertEqual(len(lr.match('(defun '+child+' ?*body)',lr.parse(leaf).forms,deep=True)),1)
 def test_every_original_function_guard_and_contract_is_exact(self):
  before=read('tools/fixtures/storage-block-io-before.lisp');a,b,c=rw.transform(before,'(include-book "machines-b")\n(defun unchanged () 1)')
  originals=[tree(n) for n in rw.selected(before)]
  actual=[tree(n) for n in rw.selected(without_identity_addition(without_reviewed_dimensions(read('books/storage-block-io.lisp'))))]
  self.assertEqual(originals,actual);self.assertEqual(originals,[tree(n) for n in rw.selected(c)])
  self.assertFalse(lr.match('(defun fn2-pinned-block-io-children ?*b)',lr.parse(a).forms,deep=False))
  self.assertIn('unrelated-reserve',a);self.assertIn('defcost fn2-block-read',a);self.assertIn('defcost fn2-block-write',a)
  self.assertIn('(defun unchanged () 1)',b)
 def test_actual_registry_changes_only_the_selected_owning_forms(self):
  before=subprocess.check_output(['git','show',BASE+':books/machines-b.lisp'],cwd=ROOT,text=True)
  resources='(include-book \"machines-b\")\n'
  a,b,c=rw.transform(before,resources)
  self.assertEqual(b,'(include-book \"storage-block-io\")\n');self.assertEqual(forms(c),forms(without_identity_addition(without_reviewed_dimensions(read('books/storage-block-io.lisp')))))
  self.assertFalse(lr.match('(defun fn2-pinned-block-io-children ?*body)',lr.parse(a).forms,deep=True))
  self.check_current_registry_contract(read('books/machines-b.lisp'),read('books/storage-block-io.lisp'))
 def test_current_registry_hidden_twins_missing_import_and_changed_child_fail(self):
  registry=read('books/machines-b.lisp');leaf=read('books/storage-block-io.lisp')
  moved=rw.one(leaf,'(defun fn2-block-read-children ?*body)')
  definition=leaf[moved.start:moved.end]
  damaged=(registry+'\n'+definition,
           registry+'\n(local '+definition+')',
           registry+'\n(encapsulate () (local '+definition+'))',
           registry.replace('(include-book "storage-block-io")','',1),
           registry.replace(':child fn2-block-read-children',':child fn2-block-write-children',1))
  for mutation in damaged:
   with self.assertRaises(AssertionError):self.check_current_registry_contract(mutation,leaf)
 def test_changed_extracted_body_or_guard_fails(self):
  registry=read('books/machines-b.lisp');leaf=read('books/storage-block-io.lisp')
  for mutation in (leaf.replace('(fn2-pinned-block-io-children nil','(fn2-pinned-block-io-children t',1),
                   leaf.replace(':guard (and',':guard (or',1)):
   self.assertNotEqual(mutation,leaf)
   with self.assertRaises(AssertionError):self.check_current_registry_contract(registry,mutation)
 def test_only_complete_reviewed_dimension_requests_are_allowed(self):
  registry=read('books/machines-b.lisp');leaf=read('books/storage-block-io.lisp')
  actual=request('fn2-block-read-children')
  self.assertEqual(leaf.count(actual),1)
  for mutation in (leaf.replace(actual,'',1),leaf.replace(actual,actual+'\n'+actual,1),
                   leaf.replace(actual,actual[:-1]+' :observations (:rows))',1)):
   with self.assertRaises(AssertionError):self.check_current_registry_contract(registry,mutation)
 def test_only_exact_appended_wrapper_identity_registration_allowed(self):
  leaf=read('books/storage-block-io.lisp')
  original=without_identity_addition(leaf)
  self.assertEqual(leaf,original+IDENTITY_ADDITION)
  for changed in (leaf.replace("'(fn2-block-read-children fn2-block-write-children) (w state)))))", "'(fn2-block-read-children) (w state)))))"),leaf+IDENTITY_ADDITION):
   with self.assertRaises(AssertionError):
    stripped=without_identity_addition(changed)
    self.assertEqual(stripped,original)
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
