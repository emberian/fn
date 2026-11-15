"""Proof-only raw bridge keeps the canonical full statement; no ACL2 execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'));import lisp_rewrite as lr
class RawFrames(unittest.TestCase):
 def test_canonical_statement_only_hint_replaced(self):
  source=(ROOT/'books/columns-raw-frames.lisp').read_text();lr.parse(source)
  for exact in ['(fn2-columns-preserves table name args position nil','(raw (car (last (cdr events))))','(append (take 3 raw)',':use ,public',':in-theory (e/d (,rows) (,name ,public))',"(fn2-decl-row (list :columns ',table) (w state))"]:
   self.assertIn(exact,source)
  self.assertNotIn('(defthm',source)
 def test_actual_consumer_no_runtime_or_guard_change(self):
  import subprocess
  old=subprocess.check_output(['git','show','f5f63a843:books/checkpoint.lisp'],cwd=ROOT,text=True)
  new=(ROOT/'books/checkpoint.lisp').read_text()
  def functions(text):return [text[n.start:n.end] for n in lr.parse(text).forms if isinstance(n,lr.Lst) and n.items and getattr(n.items[0],'low',None)=='defun']
  self.assertEqual(functions(old),functions(new))
  self.assertIn('(fn2-columns-raw-row-frame fn2-fields fn2-checkpoint-decode',new)
if __name__=='__main__':unittest.main()
