from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from recovery_suffix_rewrite import rewrite
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def shape(n):
 if isinstance(n,lr.Pre):return [n.prefix,shape(n.node)]
 if isinstance(n,lr.Lst):return [shape(v) for v in n.items]
 return n.text.lower()
class RecoverySuffixRewrite(unittest.TestCase):
 def test_only_owned_arm_origin_changes(self):
  source='(defun other () (rc-chain 0)) (defmachine-arms fn2-recovery-machine :declare :arms ((:read (:set (rc-chain 0)))))'
  self.assertEqual(rewrite(source,[('(rc-chain 0)','(rc-chain row-rc-base)',1)]),source.replace('(:set (rc-chain 0))','(:set (rc-chain row-rc-base))'))
 def test_actual_arm_class_is_exact_rewrite(self):
  before=(ROOT/'tools/fixtures/recovery-full-origin-before.lisp').read_text()
  after=lr.match('(defmachine-arms fn2-recovery-machine ?*rest)',lr.parse(ROOT/'books/recovery-machine.lisp').forms,deep=False)[0].node
  self.assertEqual(shape(lr.parse(rewrite(before)).forms[0]),shape(after))
 def test_drift_refuses(self):
  with self.assertRaises(ValueError):rewrite('(defmachine-arms fn2-recovery-machine :declare :arms ())')
 def test_missing_actual_owner_refuses(self):
  with self.assertRaises(ValueError):rewrite('(defmachine-arms other :declare :arms ())')
if __name__=='__main__':unittest.main()
