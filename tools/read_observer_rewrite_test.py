import subprocess, unittest
from pathlib import Path
import lisp_rewrite as lr
from read_observer_rewrite import project, nodes, sym, ALL, MUT
from read_close_park_rewrite import project as project_close, PARK
ROOT=Path(__file__).resolve().parents[1]
def formmap(text):
 return {sym(n.items[1]):n for f in lr.parse(text).forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defun'}
from physical_view_owner_rewrite import project as project_view
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(c):
  c.base=subprocess.check_output(['git','show','f0e1a6132:books/machines-c-read.lisp'],cwd=ROOT,text=True)
  c.now=(ROOT/'books/machines-c-read.lisp').read_text();c.helpers=(ROOT/'tools/fixtures/read-observer/helpers.lisp').read_text();c.frames=(ROOT/'tools/fixtures/read-observer/frames.lisp').read_text();c.f=formmap(c.now)
 def test_exact_actual_projection(self):self.assertEqual(project_view('machines-c-read.lisp',project_close(project(self.base,self.helpers,self.frames),(ROOT/'tools/fixtures/read-close-park/helpers.lisp').read_text())),self.now)
 def test_rejects_duplicate(self):
  with self.assertRaises(ValueError):project(self.now,self.helpers,self.frames)
 def test_resident_lower_algorithms_unchanged(self):
  # Same kernels except the exact physical decoded-view owner projection.
  for name,n in formmap(project_view('machines-c-read.lisp',self.base)).items():
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
 def test_key_release_closes_before_any_old_kernel_mutation(self):
  for op in {'key','key-octets','release'}:
   b=self.f['fn2-read-'+op+'-children'].items[-1]
   self.assertEqual(sym(b.items[0]),'mv-let')
   self.assertEqual(lr.emit(b.items[3].items[1]),'(eq closed :ok)')
   self.assertEqual(sym(b.items[2].items[0]),'fn2-read-observer-release')
   self.assertIn('fn2-rd-',lr.emit(b.items[3].items[2],drop_comments=True))
 def test_serial_and_frames(self):
  self.assertIn('(observer-serial :u60)',self.now)
  self.assertIn('(fn2-c-source-reader-release x receipt',self.helpers)
  self.assertIn('(fn2-c-source-reader-acquire x expected',self.helpers)
  for name in ('release','enter'):self.assertIn('(fn2-rd-shape fn2-read-observer-'+name,self.now)
 def test_parent_bind_clear_atomic_preflight(self):
  for name in ('bind','clear'):
   body=self.f['fn2-read-parent-'+name+'-pair'].items[-1]
   self.assertEqual(sym(body.items[0]),'if')
   self.assertIn('fn2-read-parent-pair-p',lr.emit(body.items[1],drop_comments=True))
   self.assertNotIn('fn2-reads-put',lr.emit(body.items[2],drop_comments=True))
   self.assertEqual(lr.emit(body.items[3],drop_comments=True).count('fn2-reads-put'),2)
 def test_single_and_pair_share_exact_row_preflight(self):
  for mode, pred in [('bind','bindable'),('clear','bound')]:
   for arity in ['one','pair']:
    body=self.f['fn2-read-parent-'+mode+'-'+arity].items[-1]
    self.assertEqual(sym(body.items[0]),'if')
    self.assertIn('fn2-read-parent-'+pred+'-p',lr.emit(body.items[1],drop_comments=True))
    self.assertNotIn('fn2-reads-put',lr.emit(body.items[2],drop_comments=True))
   pred_body=lr.emit(self.f['fn2-read-parent-'+pred+'-p'],drop_comments=True)
   self.assertIn('fn2-read-parent-row-p',pred_body)
  row=lr.emit(self.f['fn2-read-parent-row-p'],drop_comments=True)
  for field in ['fn2-c-source-reader-current-p','fn2-c-source-readers-live','fn2-reads-observer-serial']:
   self.assertIn(field,row)
 def test_binding_current_does_not_require_child_dead(self):
  text=lr.emit(self.f['fn2-read-parent-binding-current-p'],drop_comments=True)
  self.assertIn('fn2-c-source-reader-current-p',text)
  self.assertNotIn('fn2-reads-observer-serial',text)
  self.assertNotIn('fn2-c-source-readers-live',text)
  for name in ['bindable','bound']:
   self.assertIn('fn2-read-parent-binding-current-p',lr.emit(self.f['fn2-read-parent-'+name+'-p'],drop_comments=True))
 def test_parent_tuple_preserved_across_read_release(self):
  base=formmap(self.base)
  for name in ('fn2-rd-release','fn2-rd-key','fn2-rd-key-octets'):
   self.assertNotIn('observer-parent',lr.emit(self.f[name],drop_comments=True))
  enter=lr.emit(self.f['fn2-read-observer-enter'],drop_comments=True)
  self.assertIn('fn2-c-source-reader-acquire-under',enter)
  current=lr.emit(self.f['fn2-read-observer-current-p'],drop_comments=True)
  self.assertIn('fn2-reads-observer-parent-serial',current)
  self.assertEqual(current.count('fn2-c-source-reader-current-p'),2)
 def test_prepared_local_mv_bound(self):
  s=(ROOT/'tests/read-observer-endpoint-unit.lisp').read_text()
  p=lr.parse(s)
  decl=next(n for n in p.forms if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defconst' and sym(n.items[1])=='*fn2-rdo-stobjs*')
  self.assertIsInstance(decl.items[2],lr.Pre)
  self.assertEqual(len(decl.items[2].node.items),6+len(PARK)+1)
  self.assertLessEqual(1+len(decl.items[2].node.items),32)
if __name__=='__main__':unittest.main()
