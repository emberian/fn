"""Frozen-donor repair class and rejection controls; source only."""
import subprocess,unittest
from pathlib import Path
import physical_loader_repair as rw
ROOT=Path(__file__).resolve().parents[1]
def src(p):return (ROOT/p).read_text()
def donor(ref,p):return subprocess.check_output(['git','show',ref+':'+p],cwd=ROOT,text=True)
class LoaderRepair(unittest.TestCase):
 def test_frozen_donors_project_to_actual_books(self):
  for book,ref in [('run-physical-region','8909df8ea'),('run-physical-bound-step','5d9fe3965')]:
   rw.require_projection(book+'.lisp',donor(ref,'books/'+book+'.lisp'),src('books/'+book+'.lisp'))
 def test_frozen_subject_fixtures_are_exact_donor_forms(self):
  import lisp_rewrite as lr
  for book,ref,fn in [('run-physical-region','8909df8ea','fn2-run-load-region-freep'),('run-physical-bound-step','5d9fe3965','fn2-run-bound-step')]:
   original=donor(ref,'books/'+book+'.lisp');n=rw.one('(defun '+fn+' ?*body)',lr.parse(original).forms)
   self.assertEqual(original[n.start:n.end]+'\n',src('tools/fixtures/physical-loader-repair/'+book+'-before.lisp'))
 def test_duplicate_repair_refuses(self):
  for book in ('run-physical-region','run-physical-bound-step'):
   with self.assertRaises(ValueError):rw.project(book+'.lisp',src('books/'+book+'.lisp'))
 def test_changed_copy_count_is_rejected(self):
  before=donor('5d9fe3965','books/run-physical-bound-step.lisp');after=rw.project('run-physical-bound-step.lisp',before)
  bad=after.replace('(min (floor budget 2) (- *fn2-commit-unit-bytes* copied))','(min budget (- *fn2-commit-unit-bytes* copied))',1)
  self.assertNotEqual(after,bad)
  with self.assertRaises(ValueError):rw.require_projection('run-physical-bound-step.lisp',before,bad)
 def test_full_copy_then_forever_yield_guard_is_rejected(self):
  before=donor('5d9fe3965','books/run-physical-bound-step.lisp');after=rw.project('run-physical-bound-step.lisp',before)
  bad=after.replace('(n (fn2-run-load-copy-count budget copied))','(n (min budget (- *fn2-commit-unit-bytes* copied)))\n         ((when (< budget (* 2 n))) (fn2-run-load-step-mv :yield))',1)
  self.assertNotEqual(after,bad)
  with self.assertRaises(ValueError):rw.require_projection('run-physical-bound-step.lisp',before,bad)
 def test_removed_pending_or_window_guard_is_rejected(self):
  before=donor('8909df8ea','books/run-physical-region.lisp');after=rw.project('run-physical-region.lisp',before)
  for guard in ('(equal (fn2-run-loads-pending c fn2-run-loads) 0)','(equal (fn2-run-loads-windows c fn2-run-loads) 0)'):
   bad=after.replace(guard,'t',1);self.assertNotEqual(after,bad)
   with self.assertRaises(ValueError):rw.require_projection('run-physical-region.lisp',before,bad)
 def test_changed_original_subject_and_unrelated_authority_refuse(self):
  before=donor('5d9fe3965','books/run-physical-bound-step.lisp')
  with self.assertRaises(ValueError):rw.project('run-physical-bound-step.lisp',before.replace('(n (min budget ','(n (min (* 2 budget) ',1))
  after=rw.project('run-physical-bound-step.lisp',before)
  with self.assertRaises(ValueError):rw.require_projection('run-physical-bound-step.lisp',before,after.replace('(fn2-format-run :page nil','(fn2-unapproved-format :page nil',1))
 def test_actual_step_fixture_preserves_entire_existing_io_driver(self):
  before=donor('c62b3e0bd','tests/txn-auth-loader-physical-unit.lisp')
  rw.require_actual_step_fixture(before,src('tests/txn-auth-loader-physical-unit.lisp'))
 def test_actual_step_progress_or_phase_mutation_is_rejected(self):
  before=donor('c62b3e0bd','tests/txn-auth-loader-physical-unit.lisp');after=rw.project_actual_step_fixture(before)
  for old,new in [('(fn2-tal-bound-step-op c 4096 fn2-core)','(fn2-tal-bound-step-op c 8192 fn2-core)'),('(fn2-run-loads-copied c fn2-run-loads) 2048','(fn2-run-loads-copied c fn2-run-loads) 4096'),('(+ 1 sector))','sector)')]:
   bad=after.replace(old,new,1);self.assertNotEqual(after,bad)
   with self.assertRaises(ValueError):rw.require_actual_step_fixture(before,bad)
if __name__=='__main__':unittest.main()
