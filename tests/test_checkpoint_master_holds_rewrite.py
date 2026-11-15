import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from rewrite_checkpoint_master_holds import rewrite
class Holds(unittest.TestCase):
 def test_scope_comments_idempotence(self):
  text='; (:context :storage-window)\n(defmachine other :holds ((:context :storage-window)))\n(defmachine fn2-checkpoint-master :doc "(:context :storage-window)" :holds ((:context :storage-window) (:page-wait :storage-window) (:page-accept-return :storage-window) (:loan-uncertain :storage-window)))'
  result=rewrite(text)
  self.assertEqual(result,text.replace(':holds ((:context :storage-window) (:page-wait',':holds ((:context :storage-window :storage-window) (:page-wait'))
  self.assertEqual(rewrite(result),result)
 def test_fail_closed(self):
  with self.assertRaises(ValueError):rewrite('(defmachine fn2-checkpoint-master :holds ((:context :other)))')
if __name__=='__main__':unittest.main()
