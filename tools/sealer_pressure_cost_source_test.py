"""SOURCE template/category controls only; no emitted or physical qualification."""
import unittest
from pathlib import Path
import sealer_pressure_cost_audit as a
class Cost(unittest.TestCase):
 def test_actual_callbacks(self):
  self.assertEqual(a.report(),{'fn2-sealer-checkpoint-pending-op':74,'fn2-sealer-checkpoint-resumed-p':82,'fn2-sealer-checkpoint-resumable-p':160,'fn2-sealer-checkpoint-wake-target':236})
 def test_unknown_callee_refuses(self):
  with self.assertRaises(ValueError):a.expr(['fn2-seals-invented-field','0','table'])
  with self.assertRaises(ValueError):a.expr(['fn2-invented-helper','table'])
 def test_actual_geometry_and_region_reads(self):
  self.assertIn('(defconst *fn2-run-active-source-cursors* 8)',Path('books/run-active-geometry.lisp').read_text())
  self.assertIn('(defconst *fn2-b-seal-source-cursors* *fn2-run-active-source-cursors*)',Path('books/machines-b.lisp').read_text())
  self.assertEqual(a.N,8)
  actual=a.D[a.REGION][-1]
  # Scalar termination and exactly six nonterminal physical metadata reads.
  self.assertEqual(actual[0],'or')
  calls=[]
  def walk(x):
   if isinstance(x,list):
    if x and isinstance(x[0],str) and x[0].startswith(('fn2-run-loads-','fn2-checkpoint-summary-leases-')):calls.append(x[0])
    for y in x:walk(y)
  walk(actual);self.assertEqual(len(calls),6)
 def test_real_generated_access_contracts(self):
  s=Path('books/machines.lisp').read_text()
  self.assertIn('(if (eq (,code ,@call) :ok) ,value-body',s)
  self.assertIn('(let ((code (fn2-machine-phase-read-code id fn2-core)))',s)
  self.assertIn('(let ((slot (fn2-machine-slot id fn2-core)))',s)
  self.assertIn('(case (fn2-machine-kind id fn2-core)',s)
  self.assertEqual((a.ID,a.INDEX,a.FIELD_CODE,a.FIELD,a.SNAPSHOT),(2,4,12,22,16))
if __name__=='__main__':unittest.main()
