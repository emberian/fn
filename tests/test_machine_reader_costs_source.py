"""Actual emitted reader class controls; source-only, no ACL2 expansion."""
from pathlib import Path
import sys,unittest
sys.path.insert(0,'tools')
from machine_reader_costs import machine_reader_inventory,ROW_STEPS
class Readers(unittest.TestCase):
 def test_finite_actual_producer_classification(self):
  inventory=machine_reader_inventory()
  for name,steps,kind in [('fn2-machine-kind',4,'directory-index'),('fn2-machine-slot',4,'directory-index'),('fn2-machine-generation',22,'kind-field'),('fn2-machine-generation-read-code',12,'kind-field-code'),('fn2-machine-phase',22,'kind-field'),('fn2-machine-wait-reason',4,'directory-field'),('fn2-boot-snapshot-read-code',16,'kind-snapshot'),('fn2-boot-row-generation',22,'kind-row'),('fn2-boot-row-ready-prev',19,'kind-row-directory')]:
   self.assertEqual(inventory[name],{'steps':steps,'class':kind})
  self.assertNotIn('fn2-machine-invented-absent-field',inventory)
  self.assertEqual(ROW_STEPS,22)
 def test_templates_are_actual_served_bodies(self):
  source=Path('books/machines.lisp').read_text()
  for name in ['fn2-machine-checked-reader-events','fn2-machine-field-events','fn2-machine-directory-field-events','fn2-machine-snapshot-events','fn2-machine-row-reader-events']:
   self.assertIn('(defun '+name+' ',source)
  self.assertIn('(if (eq (,code ,@call) :ok) ,value-body',source)
  self.assertIn('(if (eq (,code id fn2-core) :ok)',source)
  self.assertIn('(fn2-machine-directory-fieldp (caar columns))',source)
 def test_prepared_gate_uses_actual_operation_rows(self):
  gate=Path('tests/machine-reader-cost-face-source-unit.lisp').read_text()
  self.assertIn('PREPARED UNEXECUTED',gate)
  self.assertIn("(fn2-operation-row 'fn2-machine-generation world)",gate)
  self.assertIn("(fn2-operation-row 'fn2-machine-generation-read-code world)",gate)
  self.assertIn("(fn2-decl-get :definition generation)",gate)
  self.assertIn("(eq (car tree) 'quote)",gate)
  self.assertNotIn('(defun fn2-machine-generation ',gate)
 def test_unknown_access_cannot_be_zero_cost(self):
  import directory_consume_metadata_audit as a
  self.assertEqual(a.ex(['fn2-machine-generation','id','fn2-core'])['metadata'],22)
  with self.assertRaises(ValueError):a.ex(['fn2-machine-invented-absent-field','id','fn2-core'])
if __name__=='__main__':unittest.main()
