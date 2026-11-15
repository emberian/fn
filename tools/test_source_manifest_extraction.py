"""Exact existing decoder-tail extraction; no executable integrity claim."""
from pathlib import Path
import subprocess
import unittest
ROOT=Path(__file__).resolve().parents[1]
class Extraction(unittest.TestCase):
 def test_exact_tail(self):
  old=subprocess.check_output(["git","show","ad7229772fa008a40677f4176cccb566d2efd69b:books/cursor.lisp"],cwd=ROOT,text=True)
  old=old[old.index("(defun fn2-cursor-manifest-entry-of "):]
  tail=old[old.index("       (mpos (nfix mpos))"):old.index("\n(defthm fn2-cursor-manifest-entry-of-shape")]
  tail=tail.replace("*fn2-article-location-hashes-max*","prefix")
  new=(ROOT/"books/source-manifest-entry.lisp").read_text()
  self.assertIn(tail,new)
 def test_old_wrapper_uses_shared_tail(self):
  s=(ROOT/"books/cursor.lisp").read_text()
  body=s[s.index("(defun fn2-cursor-manifest-entry-of "):s.index("\n(defthm fn2-cursor-manifest-entry-of-shape")]
  self.assertIn("fn2-source-manifest-entry base *fn2-article-location-hashes-max*",body)
  self.assertNotIn("fn2-am-get-entry",body)
 def test_no_authenticity_flag(self):
  s=(ROOT/"books/source-manifest-entry.lisp").read_text()
  self.assertIn("callers verify the complete location",s)
  self.assertNotIn("verified :bool",s)
if __name__=="__main__": unittest.main()
