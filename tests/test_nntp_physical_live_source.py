"""Actual cursor source port controls; not runtime/ACL2 qualification."""
import subprocess,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym
from nntp_physical_port import port_cursor,port_kind,port_observer,named_lists
BASE='f25d00ef6'
def src(p):return (ROOT/p).read_text()
def old(p,ref=BASE):return subprocess.check_output(['git','show',ref+':'+p],cwd=ROOT,text=True)
def render(n):return lr.emit(n,drop_comments=True)
class Controls(unittest.TestCase):
 def test_actual_projection(self):
  self.assertEqual(port_cursor(old('books/cursor.lisp'),old('books/cursor.lisp','bdbf7e9bb')),src('books/cursor.lisp'))
  self.assertEqual(port_kind(old('books/cursor-kind.lisp')),src('books/cursor-kind.lisp'))
  self.assertEqual(port_observer(old('books/cursor-source-observer.lisp')),src('books/cursor-source-observer.lisp'))
 def test_parent_and_current_draining_preserved(self):
  before=named_lists(old('books/cursor.lisp'));after=named_lists(src('books/cursor.lisp'))
  self.assertEqual(render(before[':draining']),render(after[':draining']))
  select=render(after[':select'])
  self.assertLess(select.index('fn2-cursor-request-acquire'),select.index('fn2-cursor-parse'))
  self.assertLess(select.index('fn2-cursor-parse'),select.index('fn2-run-page-bundle-reserve'))
  self.assertIn('(observer-serial receipt)',select)
  self.assertIn('(:exhausted)',select);self.assertIn('(if (equal complete 1) 0 1)',select)
 def test_all_ten_real_reads_dispatch_miss(self):
  count=0
  for f in lr.parse(src('books/cursor.lisp')).forms:
   for n in nodes(f):
    if not isinstance(n,lr.Lst) or len(n.items)<3 or sym(n.items[0])!=':do':continue
    c=n.items[2]
    if not isinstance(c,lr.Lst) or not c.items or sym(c.items[0]) not in {'fn2-read-lookup','fn2-read-next','fn2-read-scan-next','fn2-read-identity','fn2-read-seek-step'}:continue
    s=render(n);self.assertIn('(:miss)',s);self.assertIn('run-load-start',s)
    self.assertIn('(:more)',s);count+=1
  self.assertEqual(count,10)
 def test_issue_is_explicit_with_full_unit_credit(self):
  d=named_lists(src('books/cursor.lisp'))
  issue=render(d['run-load-read']);step=render(d['run-load-step'])
  self.assertIn('(:issue (fn2-run-page-read',issue)
  self.assertNotIn('(:do',issue)
  for s in (issue,step):self.assertIn('(<= *fn2-commit-unit-bytes* budget)',s)
  self.assertIn('(:wait :completion',issue)
 def test_exact_harvest_then_observer_only_wakes(self):
  c=src('books/machines-c.lisp');self.assertIn(':harvest (fn2-run-load-harvest',c)
  obs=named_lists(src('books/cursor.lisp'))[':read-result'];s=render(obs)
  self.assertIn('(:wake)',s);self.assertNotIn('fn2-run-load-harvest',s)
  h=src('books/run-physical-harvest.lisp')
  for check in ('fn2-run-load-ops-generation','fn2-run-loads-op-slot','fn2-run-loads-op-gen','(equal cell 0)'):self.assertIn(check,h)
 def test_pending_precedes_reference_and_workspace_cleanup(self):
  f=named_lists(src('books/cursor.lisp'))[':finish'];s=render(f)
  self.assertLess(s.index('row-pending'),s.index('fn2-read-release'))
  self.assertLess(s.index('row-pending'),s.index('fn2-cursor-lease-release'))
  self.assertIn('run-load-drain',s);self.assertIn('row-load-refuse',s)
  self.assertLess(s.index('run-load-drain'),s.index('fn2-read-release'))
  self.assertNotIn('fn2-read-value',s);self.assertNotIn('fn2-read-next',s)
  d=render(named_lists(src('books/cursor.lisp'))['run-load-drain'])
  self.assertIn('(:wait)',d);self.assertIn('fn2-read-loader-member-release-op',d)
  self.assertIn('fn2-run-page-release',d)
 def test_article_lease_not_double_releasing_query_rank(self):
  for f in lr.parse(src('books/cursor.lisp')).forms:
   for n in nodes(f):
    if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])==':do' and isinstance(n.items[2],lr.Lst) and n.items[2].items and sym(n.items[2].items[0])=='fn2-cursor-lease-release':
     self.assertNotIn(':effects',render(n))
  self.assertIn('(:storage-window :while (query-bundle :held))',src('books/cursor-kind.lisp'))
 def test_actor_generation_cannot_drop_parent_early(self):
  s=src('books/cursor-source-observer.lisp')
  self.assertIn('(equal (fn2-cursor-query-bundle slot fn2-cursor-table) *fn2-cursor-query-bundle-none*)',s)
  self.assertIn('(equal (fn2-cursor-load-active slot fn2-cursor-table) 0)',s)
  s=src('books/assembly-callbacks-d-cursor.lisp')
  self.assertLess(s.index('(fn2-read-loader-core-faces)'),s.index('(defmachine-arms'))
 def test_all_lower_algorithms_unchanged(self):
  for b in ('machines-c-read','run-physical-release','run-physical-bound-bind','run-physical-bound-io','run-physical-bound-step','cns'):
   self.assertEqual(old('books/'+b+'.lisp'),src('books/'+b+'.lisp'))
 def test_duplicate_projection_refuses(self):
  with self.assertRaises(ValueError):port_cursor(src('books/cursor.lisp'),old('books/cursor.lisp','bdbf7e9bb'))
  with self.assertRaises(ValueError):port_kind(src('books/cursor-kind.lisp'))
if __name__=='__main__':unittest.main()
