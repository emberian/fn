"""Production-source controls for installed full Ref starts, not ACL2 admission."""
from pathlib import Path
import json,unittest
import lisp_rewrite as l
from live_fullref_starts_rewrite import project,check
ROOT=Path(__file__).resolve().parents[1]
F=json.loads((ROOT/'tools/fixtures/live-fullref/starts.json').read_text())
class FullRef(unittest.TestCase):
 def test_exact_projection(self):
  for n,s in F['before'].items():
   self.assertEqual(project(n,s),F['after'][n])
   current=(ROOT/'books'/n).read_text();check(n,current)
   # Later canonical CLOSE/view-owner changes share these source books.
   # Preserve the exact installed-start arguments in their actual definitions.
   name={'machines-c-groups.lisp':'fn2-xl-run-next','machines-c-successor.lisp':'fn2-succ-resolve-next','range.lisp':'fn2-range-advance-run'}[n]
   def call(text):
    f=l.match('(defun '+name+' ?*body)',l.parse(text).forms)[0]
    m=l.match('(fn2-run-cursor-start-installed ?*args)',[f.node])
    self.assertEqual(len(m),1)
    return l.emit(m[0].node,drop_comments=True)
   self.assertEqual(call(current),call(F['after'][n]))
 def test_duplicate_refused(self):
  for n,s in F['after'].items():
   with self.assertRaises(ValueError):project(n,s)
 def test_range_uses_existing_rb(self):
  now=l.parse(F['after']['range.lisp']).forms
  self.assertEqual(len(l.match('(fn2-run-cursor-start-installed c r (fn2-range-sources-rb s fn2-range-sources) qk qs qg fn2-run-installed fn2-run-cursors)',now)),1)
  self.assertTrue(l.match('(equal (fn2-run-installed-schema r fn2-run-installed) sid)',now))
 def test_current_query_owner_flows_to_xl(self):
  p=l.parse(F['after']['machines-c-groups.lisp']).forms
  self.assertEqual(len(l.match('(fn2-xl-run-next tx sid rb qk qs qg fn2-succ-txns fn2-run-installed fn2-run-cursors)',p)),1)
 def test_no_public_successor_owner_abi_change(self):
  def args(s):
   return {m.captures['name'].low:l.emit(m.captures['args'],drop_comments=True) for m in l.match('(defun ?name ?args ?*body)',l.parse(s).forms) if m.captures['name'].low.startswith('fn2-succ-resolve')}
  self.assertEqual(args(F['before']['machines-c-successor.lisp']),args(F['after']['machines-c-successor.lisp']))
 def test_shared_constructor_has_actual_identity(self):
  p=l.parse((ROOT/'books/runs.lisp').read_text()).forms
  n=l.match('(defun fn2-run-cursor-start-installed ?*body)',p)[0].node;s=l.emit(n,drop_comments=True)
  for field in ['physical','epoch','wire-run','run','catalog-tag']+['hash-'+str(i) for i in range(8)]:self.assertIn('fn2-run-installed-'+field,s)
  self.assertIn('*fn2-run-cursor-phase-miss*',s)
 def test_mutant_resident_start_refused(self):
  s=F['after']['range.lisp'].replace('fn2-run-cursor-start-installed c r','fn2-run-cursor-start c r',1)
  self.assertNotEqual(s,F['after']['range.lisp'])
  with self.assertRaises(ValueError):check('range.lisp',s)
 def test_physical_view_projection_is_exact(self):
  from physical_view_owner_rewrite import project as view
  for name,fn,fixture in [('range.lisp','fn2-range-advance-run','range-owner-before.lisp'),('machines-c-read.lisp','fn2-rd-lookup','read-owner-before.lisp')]:
   before=(ROOT/'tools/fixtures/live-fullref'/fixture).read_text().rstrip('\n')
   source=(ROOT/'books'/name).read_text()
   m=l.match('(defun '+fn+' ?*body)',l.parse(source).forms)[0]
   self.assertEqual(view(name,before),source[m.start:m.end])
   with self.assertRaises(ValueError):view(name,source)
 def test_physical_range_head_uses_decoded_page_owner(self):
  source=(ROOT/'books/range.lisp').read_text()
  f=l.match('(defun fn2-range-advance-run ?*body)',l.parse(source).forms)[0]
  entry=l.match('(:entry ?*body)',[f.node])[0]
  text=source[entry.start:entry.end]
  self.assertIn('(natp c) (< c (fn2-run-cursors-rows fn2-run-cursors))',text)
  self.assertIn('(equal (fn2-run-cursors-physical c fn2-run-cursors) 1)',text)
  for field in ('okind','oslot','ogen'):
   self.assertIn('('+field+' (fn2-run-cursors-'+field+' c fn2-run-cursors))',text)
  self.assertIn('(fn2-range-sources-set-state s *fn2-range-state-head* fn2-range-sources)',text)
  self.assertLess(source.index('(fn2-run-scan-step c budget'),entry.start)
 def test_xl_view_distinguishes_overlay_from_physical_cursor(self):
  source=(ROOT/'books/machines-c-read.lisp').read_text()
  f=l.match('(defun fn2-rd-lookup ?*body)',l.parse(source).forms)[0]
  text=source[f.start:f.end]
  self.assertIn('(equal erow (+ b0 *fn2-read-heads* *fn2-run-reader-entry*))',text)
  self.assertIn('(< tx (fn2-run-cursors-rows fn2-run-cursors))',text)
  for key,field,constant in [('ek','okind','kind'),('es','oslot','slot'),('eg','ogen','gen')]:
   self.assertIn('('+key+' (if physical-entry (fn2-run-cursors-'+field+' tx fn2-run-cursors) *fn2-idc-owner-'+constant+'*))',text)
if __name__=='__main__':unittest.main()
