from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from commit_directory_rewrite import replace_batch_indices
class DirectoryRewrite(unittest.TestCase):
 def test_scope_and_metadata_are_preserved(self):
  source="(defun target (batch s) (list (read batch s) (read 0 s))) (defun other (batch s) (read batch s))"
  result=replace_batch_indices(source,'target',['read'],'batch','row',1)
  self.assertEqual(result,"(defun target (batch s) (list (read row s) (read 0 s))) (defun other (batch s) (read batch s))")
 def test_unexpected_identity_expression_refuses(self):
  with self.assertRaises(ValueError):replace_batch_indices('(defun target (b s) (read (+ b 1) s))','target',['read'],'b','row',1)
 def test_count_drift_refuses(self):
  with self.assertRaises(ValueError):replace_batch_indices('(defun target (b s) (read b s))','target',['read'],'b','row',2)
if __name__=='__main__':unittest.main()
