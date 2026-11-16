"""Actual cold consumer projection, not admission or persistence evidence."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from boot_semantic_projection import BOOKS,project,DONOR

def sym(n):return getattr(n,'low','')
def nodes(n):
 yield n
 if isinstance(n,lr.Lst):
  for a in n.items:yield from nodes(a)
 elif isinstance(n,lr.Pre):yield from nodes(n.node)
def src(name):return (ROOT/'books'/(name+'.lisp')).read_text()
def old(name):
 return subprocess.check_output(['git','show',DONOR+':books/'+name+'.lisp'],cwd=ROOT,text=True)
def funcs(s):return {sym(n.items[1]):n for f in lr.parse(s).forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defun'}
class Controls(unittest.TestCase):
 def test_exact_named_projection(self):
  for name in BOOKS:
   origin='checkpoint-restore-reach' if name=='checkpoint-restore-reach-core' else name
   self.assertEqual(project(name,old(origin)),src(name),name)
 def test_all_retained_runtime_bodies_guards_are_actual(self):
  for name in BOOKS:
   origin='checkpoint-restore-reach' if name=='checkpoint-restore-reach-core' else name
   before=funcs(old(origin))
   for fn,form in funcs(src(name)).items():self.assertEqual(lr.emit(form,drop_comments=True),lr.emit(before[fn],drop_comments=True),fn)
 def test_no_old_boot_core_or_arena_dependency(self):
  for name in BOOKS:
   s=src(name)
   for banned in ('(include-book "boot")','(include-book "boot-kind")','(include-book "recovery")','(include-book "checkpoint-restore-arena")','(defstobj fn2-core'):
    self.assertNotIn(banned,s)
  self.assertNotIn('fn2-checkpoint-restore-reach-arena-consume',src('checkpoint-restore-reach-core'))
 def test_map_current_is_mandatory_before_begin(self):
  b=lr.emit(funcs(src('checkpoint-restore-semantic'))['fn2-checkpoint-restore-semantic-begin'],drop_comments=True)
  self.assertIn('fn2-checkpoint-restore-map-current-p',b)
  self.assertIn('*fn2-checkpoint-restore-semantic-phase-idle*',b)
  self.assertNotIn('verified',b);self.assertNotIn('ready',b)
 def test_extent_bounded_gray_closed_not_fifo_completion(self):
  s=src('checkpoint-restore-semantic-work')
  self.assertIn('*fn2-checkpoint-restore-semantic-work-state-gray*',s)
  self.assertIn('*fn2-checkpoint-restore-semantic-work-state-closed*',s)
  self.assertIn(':cycle',s)
  self.assertIn(':payload-required',s)
  self.assertIn('fn2-checkpoint-restore-semantic-work-word',s)
 def test_catalog_capture_is_not_adoption(self):
  s=src('checkpoint-summary-catalog')
  self.assertIn('*fn2-checkpoint-summary-phase-captured*',s)
  self.assertNotIn('*fn2-checkpoint-summary-phase-applied*',s)
  self.assertIn('fn2-checkpoint-restore-semantic-entry',s)
  self.assertIn('*fn2-checkpoint-restore-semantic-work-state-closed*',s)
 def test_only_two_actual_semantic_children(self):
  s=src('boot-semantic-kind');p=lr.parse(s)
  children=[sym(n.items[1]) for n in p.forms if isinstance(n,lr.Lst) and n.items and sym(n.items[0])=='defcorechild']
  self.assertEqual(children,['fn2-core-checkpoint-restore-semantic','fn2-core-checkpoint-restore-semantic-work'])
  self.assertIn('(fn2-b-capacity :extent-slots 16 profile)',s)
 def test_literal_dependency_graph(self):
  done=set();active=[]
  def visit(p):
   p=p.resolve();self.assertNotIn(p,active,'include cycle '+str(active+[p]))
   if p in done:return
   self.assertTrue(p.exists(),'missing local book '+str(p));active.append(p)
   for n in lr.parse(p.read_text()).forms:
    if isinstance(n,lr.Lst) and len(n.items)>1 and sym(n.items[0])=='include-book' and isinstance(n.items[1],lr.Str):
     if not any(sym(a)==':dir' for a in n.items[2:]):visit(p.parent/(n.items[1].text[1:-1]+'.lisp'))
   active.pop();done.add(p)
  for name in BOOKS+('boot-semantic-kind',):visit(ROOT/'books'/(name+'.lisp'))
 def test_transport_derives_cursor_from_owned_page_fill(self):
  s=src('boot-semantic-consumer');f=funcs(s)
  n=f['fn2-boot-semantic-target-children'];body=lr.emit(n,drop_comments=True)
  self.assertNotIn('cursor',lr.emit(n.items[2]))
  self.assertIn('(fn2-pool-fill slot fn2-pool)',body)
  self.assertIn('fn2-boot-config-image-size',body)
  self.assertIn('fn2-boot-semantic-transport-current-p',body)
 def test_copy_never_exposes_entries_or_ready(self):
  f=funcs(src('boot-semantic-consumer'));s=lr.emit(f['fn2-boot-semantic-copy-children'],drop_comments=True)
  self.assertIn('fn2-pool-copy-range',s)
  self.assertIn('(not (equal slot rxslot))',s)
  self.assertNotIn('set-phase',s)
  for status in (':entries',':ready',':applied'):self.assertNotIn(status,s)
  self.assertNotIn('verified',lr.emit(f['fn2-boot-semantic-copy-children'].items[2]))
 def test_constructor_and_frames_are_actual_mutable_subset(self):
  s=src('boot-semantic-consumer');f=funcs(s)
  b=lr.emit(f['fn2-boot-semantic-start-children'],drop_comments=True)
  self.assertIn('fn2-checkpoint-restore-semantic-begin',b)
  self.assertIn('fn2-checkpoint-summary-begin',b)
  self.assertIn('fn2-checkpoint-restore-reach-current-p',b)
  self.assertNotIn('*fn2-checkpoint-summary-phase-applied*',s)
  self.assertIn('"-ROWS"',s);self.assertIn('fn2-pool-data-length',s)
  for name,n in f.items():
   if name.endswith('-children'):
    for x in nodes(n.items[-1]):
     if isinstance(x,lr.Lst) and x.items and sym(x.items[0])=='mv':self.assertLessEqual(len(x.items)-1,9)
 def test_kind_declares_its_provider_before_registration(self):
  s=src('boot-semantic-kind')
  self.assertLess(s.index('(include-book "machines-b")'),s.index('(defcorechild'))
if __name__=='__main__':unittest.main()
