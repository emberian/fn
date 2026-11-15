"""Actual cursor source port controls; not runtime/ACL2 qualification."""
import subprocess,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym
from nntp_physical_port import port_cursor,port_kind,port_observer,named_lists
from nntp_physical_admission import port as admission,kind as admission_kind
from physical_view_owner_rewrite import project as project_view
from run_physical_park_recipe import project as repair_park
from physical_loader_repair import project as repair_loader
BASE='f25d00ef6'
def src(p):return (ROOT/p).read_text()
def old(p,ref=BASE):return subprocess.check_output(['git','show',ref+':'+p],cwd=ROOT,text=True)
def render(n):return lr.emit(n,drop_comments=True)
class Controls(unittest.TestCase):
 def test_actual_projection(self):
  self.assertEqual(admission(port_cursor(old('books/cursor.lisp'),old('books/cursor.lisp','bdbf7e9bb'))),src('books/cursor.lisp'))
  self.assertEqual(admission_kind(port_kind(old('books/cursor-kind.lisp'))),src('books/cursor-kind.lisp'))
  self.assertEqual(port_observer(old('books/cursor-source-observer.lisp')).replace('(equal (fn2-cursor-load-active slot fn2-cursor-table) 0)', '(equal (fn2-cursor-load-active slot fn2-cursor-table) 0)\n                    (equal (fn2-cursor-storage-hold slot fn2-cursor-table) *fn2-cursor-storage-hold-none*)'),src('books/cursor-source-observer.lisp'))
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
 def test_article_rank_preserves_resident_and_physical_routes(self):
  d=named_lists(src('books/cursor.lisp'))
  for name in ('art-fail','art-end'):
   body=render(d[name]);self.assertIn('(not (equal row-query-bundle *fn2-cursor-query-bundle-held*))',body)
   self.assertIn(':effects ((:release (:storage-window)))',body)
   self.assertIn('(storage-hold *fn2-cursor-storage-hold-none*)',body)
  f=render(d[':finish']);self.assertEqual(f.count('fn2-cursor-lease-release'),2)
  self.assertEqual(f.count(':effects ((:release (:storage-window)))'),1)
  self.assertIn('(:storage-window :while (storage-hold :held))',src('books/cursor-kind.lisp'))
 def test_actor_generation_cannot_drop_parent_early(self):
  s=src('books/cursor-source-observer.lisp')
  self.assertIn('(equal (fn2-cursor-query-bundle slot fn2-cursor-table) *fn2-cursor-query-bundle-none*)',s)
  self.assertIn('(equal (fn2-cursor-load-active slot fn2-cursor-table) 0)',s)
  s=src('books/assembly-callbacks-d-cursor.lisp')
  self.assertLess(s.index('(fn2-read-loader-core-faces)'),s.index('(defmachine-arms'))
 def test_all_lower_algorithms_unchanged(self):
  # READ callback plumbing has a separately checked CLOSE-park donor. Its
  # actual rd kernels preserve only the named verified-view projection; compare
  # those and the exact named COPY repair rather than forbid
  # the required current lifetime join in the same source book.
  def kernels(text):
   return {sym(m.node.items[1]):text[m.start:m.end]
    for m in lr.match('(defun ?name ?*body)',lr.parse(text).forms,deep=False)
    if sym(m.node.items[1]).startswith('fn2-rd-')}
  before=kernels(project_view('machines-c-read.lisp',old('books/machines-c-read.lisp')))
  self.assertTrue(before)
  self.assertEqual(before,kernels(src('books/machines-c-read.lisp')))
  for b in ('run-physical-release','run-physical-bound-bind','run-physical-bound-io','run-physical-bound-step','cns'):
   original=old('books/'+b+'.lisp')
   expected=repair_loader(b+'.lisp',original) if b=='run-physical-bound-step' else (repair_park(original) if b=='run-physical-release' else original)
   self.assertEqual(expected,src('books/'+b+'.lisp'))
 def test_duplicate_projection_refuses(self):
  with self.assertRaises(ValueError):port_cursor(src('books/cursor.lisp'),old('books/cursor.lisp','bdbf7e9bb'))
  with self.assertRaises(ValueError):port_kind(src('books/cursor-kind.lisp'))
 def test_actual_physical_count_resident_branch(self):
  select=' '.join(render(named_lists(src('books/cursor.lisp'))[':select']).split())
  self.assertIn('(:let physical (fn2-cursor-physical-count))',select)
  self.assertIn('((equal physical 0) (:next :seek)',select)
  self.assertLess(select.index('fn2-cursor-request-acquire'),select.index('fn2-cursor-physical-count'))
  self.assertIn(':child fn2-run-installed-physical-count',src('books/cursor.lisp'))
 def test_article_query_recipe_uses_real_pool_and_same_bundle(self):
  s=src('books/cursor-physical-admission.lisp')
  self.assertLess(s.index('(fn2-pool-reserve class'),s.index('(fn2-run-page-bundle-reserve-children read0'))
  self.assertLess(s.index('(fn2-run-page-bundle-reserve-children read0'),s.index('(fn2-pool-release slot gen'))
  self.assertIn("(member-eq released '(:ok :retired))",s)
  self.assertIn('(fn2-cursor-article-query-mv :recovery-required 0 slot gen)',s)
  for tag in ('article','head','body','xfn-zarticle','hdr','xhdr','xpat'):self.assertIn('*fn2-nntp-command-'+tag+'*',s)
 def test_actual_lease_selector_moved_verbatim(self):
  def defs(s):return {sym(n.items[1]):n for f in lr.parse(s).forms for n in nodes(f) if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defun'}
  b=defs(old('books/cursor.lisp'))['fn2-cursor-lease-class-of']
  a=defs(src('books/cursor-physical-admission.lisp'))['fn2-cursor-lease-class-of']
  self.assertEqual(render(a),render(b));self.assertNotIn('fn2-cursor-lease-class-of',defs(src('books/cursor.lisp')))
 def test_no_article_capacity_wait_while_query_held(self):
  a=' '.join(render(named_lists(src('books/cursor.lisp'))['art-lease']).split())
  self.assertLess(a.index('((equal row-query-bundle *fn2-cursor-query-bundle-held*) (:goto art-refuse))'),a.index('(:park :pool'))
  self.assertIn('(storage-hold *fn2-cursor-storage-hold-held*)',a)
 def test_aggregate_rank_assignments_are_actual_resource_boundaries(self):
  d=named_lists(src('books/cursor.lisp'))
  for name in ('art-fail','art-end'):
   b=render(d[name]);self.assertLess(b.index('fn2-cursor-lease-release'),b.index('(storage-hold *fn2-cursor-storage-hold-none*)'))
  b=render(d['run-load-drain']);self.assertLess(b.index('fn2-run-page-release'),b.index('(storage-hold *fn2-cursor-storage-hold-none*)'))
  b=render(d['art-lease']);self.assertLess(b.index('fn2-cursor-lease-reserve'),b.index('(storage-hold *fn2-cursor-storage-hold-held*)'))
  self.assertIn('(equal (fn2-cursor-storage-hold slot fn2-cursor-table) *fn2-cursor-storage-hold-none*)',src('books/cursor-source-observer.lisp'))
 def test_recipe_and_prepared_fixture_output_bounds(self):
  forms=lr.parse(src('books/cursor-physical-admission.lisp')).forms
  macro=next(f for f in forms if isinstance(f,lr.Lst) and len(f.items)>2 and sym(f.items[0])=='defmacro' and sym(f.items[1])=='fn2-cursor-article-query-mv')
  self.assertEqual(len(macro.items[2].items),4)
  self.assertIsInstance(macro.items[-1],lr.Pre)
  self.assertEqual(len(macro.items[-1].node.items)-1,9)
  p=lr.parse(src('tests/nntp-physical-admission-unit.lisp'))
  c=next(f for f in p.forms if isinstance(f,lr.Lst) and len(f.items)>2 and sym(f.items[0])=='defconst' and sym(f.items[1])=='*fn2-npa-stobjs*')
  self.assertEqual(len(c.items[2].node.items),7)
  self.assertLessEqual(1+len(c.items[2].node.items),32)
if __name__=='__main__':unittest.main()
