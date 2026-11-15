"""Source-only projection controls; no ACL2/runtime or serving qualification."""
import subprocess,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym
from physical_loader_repair import project as repair_loader

def source(path):return (ROOT/path).read_text()
def defs(s):return {sym(n.items[1]):n for f in lr.parse(s).forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defun'}
def donor(commit,path):return subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT,text=True)
class Controls(unittest.TestCase):
 def test_region_and_range_are_actual_donor(self):
  for b in ('run-physical-region','run-physical-range'):
   original=donor('8909df8ea','books/'+b+'.lisp')
   expected=repair_loader(b+'.lisp',original) if b=='run-physical-region' else original
   self.assertEqual(source('books/'+b+'.lisp'),expected)
 def test_bound_engine_is_current_unchanged(self):
  for b in ('run-physical-bound-bind','run-physical-bound-io','run-physical-bound-step'):
   original=donor('5d9fe3965','books/'+b+'.lisp')
   expected=repair_loader(b+'.lisp',original) if b=='run-physical-bound-step' else original
   self.assertEqual(source('books/'+b+'.lisp'),expected)
 def test_selected_requires_actual_read_and_parent_receipt(self):
  n=defs(source('books/machines-c-read-loader.lisp'))['fn2-read-loader-selected']
  s=lr.emit(n.items[-1].items[1].items[0],drop_comments=True)
  self.assertIn('(fn2-read-observer-current-p x fn2-reads fn2-c-source-readers)',s)
 def test_range_uses_shared_selector(self):
  n=defs(source('books/machines-c-read-loader.lisp'))['fn2-read-loader-range-select']
  self.assertEqual(sym(n.items[-1].items[0]),'fn2-run-load-range-miss')
  self.assertNotIn('fn2-read-loader-range-select',lr.emit(n.items[-1],drop_comments=True))
 def test_reservation_uses_actual_shared_regions(self):
  n=defs(source('books/machines-c-read-loader.lisp'))['fn2-run-page-bundle-reserve-children']
  s=lr.emit(n,drop_comments=True)
  self.assertIn('fn2-run-load-region-reserve',s)
  self.assertNotIn('fn2-pool-reserve',s)
  self.assertIn('*fn2-b-query-read-rows*',s);self.assertIn('*fn2-b-range-source-cursors*',s)
 def test_only_private_actual_actor_owner_changes(self):
  n=defs(source('books/machines-c-read-loader.lisp'))['fn2-read-loader-owner']
  s=lr.emit(n,drop_comments=True)
  self.assertIn('(posp generation)',s)
  self.assertIn('(fn2-read-loader-selected',s)
  self.assertIn('(okind kind)',s);self.assertIn('(oslot owner)',s);self.assertIn('(ogen generation)',s)
  self.assertNotIn('(qk ',s);self.assertNotIn('(qs ',s);self.assertNotIn('(qg ',s)
 def test_declared_physical_faces_share_compiler(self):
  s=source('books/machines-c-read-loader.lisp')
  self.assertIn('fn2-run-loader-core-face-events *fn2-read-loader-core-operations*',s)
  self.assertNotIn('(defun fn2-read-loader-core-face-events',s)
  self.assertNotIn('(defcost fn2-run-page-step',s)
  self.assertNotIn('c-source-observers',s)
 def test_real_pending_drains_before_release(self):
  d=defs(source('books/run-physical-region.lisp'))
  s=lr.emit(d['fn2-run-load-region-drain'],drop_comments=True)
  self.assertIn('(fn2-run-loads-pending c fn2-run-loads)',s)
  self.assertIn('(mv :wait c)',s)
  self.assertIn('fn2-run-load-region-suffix',s)
  s=lr.emit(d['fn2-run-load-region-reserve'],drop_comments=True)
  self.assertIn('fn2-run-load-region-freep',s);self.assertIn('fn2-run-load-roomp',s)
  self.assertIn('fn2-run-load-region-clean',s);self.assertIn('fn2-run-load-region-retainedp',s)
 def test_prepared_fixture_mv_bound(self):
  p=lr.parse(source('tests/live-read-loader-unit.lisp'))
  n=next(n for n in p.forms if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defconst' and sym(n.items[1])=='*fn2-lrl-stobjs*')
  self.assertIsInstance(n.items[2],lr.Pre)
  self.assertEqual(len(n.items[2].node.items),8)
  self.assertLessEqual(1+len(n.items[2].node.items),32)
 def test_literal_dependency_graph_has_no_cycle_or_missing_book(self):
  active=[];done=set()
  def visit(path):
   path=path.resolve()
   self.assertNotIn(path,active,'literal include cycle: '+str(active+[path]))
   if path in done:return
   self.assertTrue(path.exists(),'missing local include '+str(path))
   active.append(path)
   for n in lr.parse(path.read_text()).forms:
    if isinstance(n,lr.Lst) and len(n.items)>1 and sym(n.items[0])=='include-book' and isinstance(n.items[1],lr.Str):
     if not any(sym(a)==':dir' for a in n.items[2:]):visit(path.parent/(n.items[1].text[1:-1]+'.lisp'))
   active.pop();done.add(path)
  for name in ('run-physical-region','run-physical-range','machines-c-read-loader'):visit(ROOT/'books'/(name+'.lisp'))
  self.assertGreater(len(done),3)
if __name__=='__main__':unittest.main()
