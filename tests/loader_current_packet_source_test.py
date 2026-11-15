"""SOURCE controls for the actual loader projection onto current cold parent."""
import subprocess
import sys
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import lisp_source
import certs
import loader_fixed_cursor_rows
PARENT='255b5d598e3265c0ebe90a0f6c1e6cacdf97ebea'
SOURCE='798bc89ef7de3380129931d263ebd880965d7be7'
NEW=('checkpoint-source-loader','run-physical-bound','run-physical-bound-bind',
 'run-physical-bound-io','run-physical-bound-step','run-physical-source',
 'run-physical-io','run-physical-step','run-physical-release')
def original(ref,path):
 return subprocess.check_output(['git','show',ref+':'+path],cwd=ROOT,text=True)
def forms(text):
 return {(n.items[0].low,lr.flat(n.items[1])):lr.flat(n)
  for n in lr.parse(text).forms if isinstance(n,lr.Lst) and len(n.items)>1 and isinstance(n.items[0],lr.Atom)}
class LoaderPacket(unittest.TestCase):
 def test_exact_shared_engine_and_authority_wrappers(self):
  for name in NEW:
   p='books/'+name+'.lisp'
   expected=original(SOURCE,p)
   if name=='checkpoint-source-loader':expected=loader_fixed_cursor_rows.transform(expected)
   self.assertEqual((ROOT/p).read_text(),expected,p)
 def test_parent_foundations_and_release_stay_exact(self):
  for p in ('alloc','pool','columns','core','layout','checkpoint-working-release','checkpoint-working-reserve','checkpoint-working-credit',
   'allocation-release-coordinator','allocation-release-geometry','checkpoint-lifecycle-coordinator',
   'commit-arms','commit','recovery-release','release-allocation-state','release-allocation',
   'release-member-binding','retirement-coordinator'):
   path='books/'+p+'.lisp';self.assertEqual((ROOT/path).read_text(),original(PARENT,path),path)
 def test_B_changes_are_only_cursor_geometry(self):
  p='books/machines-b.lisp';before=forms(original(PARENT,p));after=forms((ROOT/p).read_text())
  for key,value in before.items():
   if key!=('defun','fn2-b-run-cursor-rows'):self.assertEqual(after.get(key),value,key)
 def test_B_original_event_order_is_preserved(self):
  path='books/machines-b.lisp'
  def keys(text):
   return [(n.items[0].low,lr.flat(n.items[1])) for n in lr.parse(text).forms if isinstance(n,lr.Lst) and len(n.items)>1 and isinstance(n.items[0],lr.Atom)]
  before=keys(original(PARENT,path));after=keys((ROOT/path).read_text())
  self.assertEqual([k for k in after if k in set(before)],before)
 def test_resident_cache_and_all_installed_transitions_are_preserved(self):
  p='books/runs.lisp';before=forms(original(PARENT,p));after=forms((ROOT/p).read_text())
  allowed={('defcolumns','fn2-run-cursors'),('defcolumns','fn2-run-paths'),('defun','fn2-run-cursor-start')}
  for key,value in before.items():
   if key not in allowed:self.assertEqual(after.get(key),value,key)
  source=forms(original(SOURCE,p))
  for key in after.keys()-before.keys():self.assertEqual(after[key],source[key],key)
 def test_actual_C_constructor_uses_canonical_geometry(self):
  p='books/machines-c.lisp';before=original(PARENT,p)
  old='(+ (nfix (fn2-profile-t profile)) (* 9 (fn2-b-read-rows profile)) *fn2-idc-seal-cursors* 1)'
  self.assertEqual(before.count(old),2)
  self.assertEqual((ROOT/p).read_text(),before.replace(old,'(fn2-b-run-cursor-rows profile)'))
 def test_driver_actual_return_projection_stays_within_ACL2_limit(self):
  fs=[lisp_source.read_sexp(x) for x in lisp_source.forms((ROOT/'books/checkpoint-metadata-driver.lisp').read_text())]
  decl=next(x for x in fs if x[:2]==['defconst','*fn2-checkpoint-root1-outputs*'])[2][1]
  for name,*outputs in decl:
   self.assertLessEqual(len(outputs)+(3 if name=='fn2-checkpoint-root1-read' else 1),32,name)
 def test_malformed_fixed_row_domains_are_checked_before_selection(self):
  source=(ROOT/'books/checkpoint-source-loader.lisp').read_text()
  self.assertEqual(source.count('(fn2-b-fixed-cursor-rows-p (fn2-run-loads-rows fn2-run-loads))'),3)
  self.assertEqual(loader_fixed_cursor_rows.transform(source),source)
  b=(ROOT/'books/machines-b.lisp').read_text()
  self.assertIn('(and (natp rows) (<= 2 rows))',b)
  self.assertEqual(b.count(':guard (fn2-b-fixed-cursor-rows-p rows)'),2)
  fixture=(ROOT/'tests/loader-fixed-cursor-rows-unit.lisp').read_text()
  for n in (0,1,2):self.assertIn('(assert-event (fn2-loader-fixed-row-control '+str(n)+'))',fixture)
 def test_pending_read_wait_is_not_reported_as_runnable_more(self):
  driver=(ROOT/'books/checkpoint-metadata-driver.lisp').read_text()
  self.assertNotIn('(if (eq code :wait) :more code)',driver)
 def test_literal_dependency_graph_is_complete_and_acyclic(self):
  seen=set();active=[]
  def visit(book):
   self.assertNotIn(book,active,active+[book])
   if book in seen:return
   p=ROOT/(book+'.lisp');self.assertTrue(p.exists(),book)
   seen.add(book);active.append(book);digest,refs=certs.book_facts(p)
   for child in certs._include_targets(ROOT,book,p,digest,refs):visit(child)
   active.pop()
  for root in ('books/checkpoint-metadata-driver','books/checkpoint-metadata-release','books/run-physical-bound-step','books/checkpoint-master-events'):visit(root)
  self.assertGreater(len(seen),len(NEW))
if __name__=='__main__':unittest.main()
