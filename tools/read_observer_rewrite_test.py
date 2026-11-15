import subprocess, unittest
from pathlib import Path
import lisp_rewrite as lr
from read_observer_rewrite import project, nodes, sym, ALL, MUT
ROOT=Path(__file__).resolve().parents[1]
def formmap(text):
 return {sym(n.items[1]):n for f in lr.parse(text).forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defun'}
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(c):
  c.base=subprocess.check_output(['git','show','f0e1a6132:books/machines-c-read.lisp'],cwd=ROOT,text=True)
  c.now=(ROOT/'books/machines-c-read.lisp').read_text();c.helpers=(ROOT/'tools/fixtures/read-observer/helpers.lisp').read_text();c.frames=(ROOT/'tools/fixtures/read-observer/frames.lisp').read_text();c.f=formmap(c.now)
 def test_exact_actual_projection(self):self.assertEqual(project(self.base,self.helpers,self.frames),self.now)
 def test_rejects_duplicate(self):
  with self.assertRaises(ValueError):project(self.now,self.helpers,self.frames)
 def test_resident_lower_algorithms_unchanged(self):
  # All old RD bodies/APIs/guards remain the SAME implementation.
  for name,n in formmap(self.base).items():
   if name.startswith('fn2-rd-'):self.assertEqual(lr.emit(n,drop_comments=True),lr.emit(self.f[name],drop_comments=True),name)
 def test_every_core_uses_same_child_and_full_carriers(self):
  for op in ALL:
   n=self.f['fn2-read-'+op];s=lr.emit(n,drop_comments=True)
   self.assertIn('(fn2-read-'+op+'-children ',s)
   self.assertIn('(fn2-c-source-readers (fn2-core-c-source-readers fn2-core))',s)
   self.assertEqual('fn2-core-c-source-control' in s,op in MUT)
 def test_explicit_current_receipts_for_continuations(self):
  for op in {'next','seek-step','scan-next','value','octets'}:
   n=self.f['fn2-read-'+op+'-children'];body=n.items[-1]
   self.assertEqual(sym(body.items[0]),'if')
   self.assertEqual(sym(body.items[1].items[0]),'fn2-read-observer-current-p')
   self.assertEqual(sym(body.items[3].items[1]),':stale' if op in {'value','octets'} else ':more')
 def test_fresh_start_family_admits_before_existing_body(self):
  for op in {'lookup','range','seek','scan','identity'}:
   n=self.f['fn2-read-'+op+'-children'];body=n.items[-1]
   self.assertEqual(sym(body.items[0]),'mv-let')
   self.assertEqual(sym(body.items[2].items[0]),'fn2-read-observer-enter')
   self.assertNotIn(':absent',lr.emit(body.items[3].items[3],drop_comments=True))
 def test_only_successful_key_release_closes(self):
  for op in {'key','key-octets','release'}:
   b=self.f['fn2-read-'+op+'-children'].items[-1]
   self.assertEqual(sym(b.items[0]),'mv-let')
   self.assertEqual(lr.emit(b.items[3].items[1]),'(eq code :ok)')
   self.assertIn('fn2-read-observer-release',lr.emit(b.items[3].items[2],drop_comments=True))
 def test_serial_and_frames(self):
  self.assertIn('(observer-serial :u60)',self.now)
  self.assertIn('(fn2-c-source-reader-release x receipt',self.helpers)
  self.assertIn('(fn2-c-source-reader-acquire x expected',self.helpers)
  for name in ('release','enter'):self.assertIn('(fn2-rd-shape fn2-read-observer-'+name,self.now)
if __name__=='__main__':unittest.main()
