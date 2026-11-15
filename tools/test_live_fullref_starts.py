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
   self.assertEqual(project(n,s),F['after'][n]);self.assertEqual((ROOT/'books'/n).read_text(),F['after'][n]);check(n,F['after'][n])
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
if __name__=='__main__':unittest.main()
