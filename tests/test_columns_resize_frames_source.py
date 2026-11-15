"""Source controls only: actual registry, canonical proof generator, no resizer twin."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr

class ExtraResizeFrames(unittest.TestCase):
 def test_registry_and_extra_only(self):
  source=(ROOT/'books/columns-resize-frames.lisp').read_text();lr.parse(source)
  self.assertIn("(fn2-decl-row (list :columns ',table) (w state))",source)
  self.assertIn('(fn2-decl-get :extra-fields schema)',source)
  self.assertNotIn('(fn2-decl-get :columns schema)',source)
  for gate in ['fn2-columns-numeric-fieldp','fn2-columns-arrayp','(cadr (member-eq :resizable field))']:
   self.assertIn(gate,source)
  self.assertIn('(fn2-columns-sym table "-PRESERVES")',source)
  self.assertIn(':specs (("-ROWS" ,rows nil :frame ,table))',source)
  self.assertIn(':in-theory (enable ,rows ,resize)',source)
  self.assertNotIn('(defun resize-',source)
 def test_actual_allocator_consumer_and_formula(self):
  import subprocess
  old=subprocess.check_output(['git','show','f5f63a843:books/commit-alloc.lisp'],cwd=ROOT,text=True)
  now=(ROOT/'books/commit-alloc.lisp').read_text();lr.parse(now)
  self.assertIn('(include-book "columns-resize-frames")',now)
  self.assertIn('(fn2-columns-extra-resize-frames fn2-extents)',now)
  def events(s):
   return [s[n.start:n.end] for n in lr.parse(s).forms if isinstance(n,lr.Lst) and n.items and getattr(n.items[0],'low',None)=='defthm']
  self.assertEqual(events(old),events(now))
  self.assertEqual((ROOT/'books/alloc.lisp').read_bytes(),subprocess.check_output(['git','show','f5f63a843:books/alloc.lisp'],cwd=ROOT))

if __name__=='__main__':unittest.main()
