"""Named B geometry/source-order controls; no ACL2 execution claim."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from physical_b_loader_rewrite import DATA,project,named
class LoaderB(unittest.TestCase):
 def test_actual_projection_and_idempotence(self):
  text=(ROOT/'books/machines-b.lisp').read_text()
  self.assertEqual(project(DATA['before']),text)
  self.assertEqual(project(text),text)
 def test_existing_events_and_guards_preserved(self):
  before=DATA['before'];after=project(before)
  for n in lr.parse(before).forms:
   if not isinstance(n,lr.Lst) or len(n.items)<2:continue
   name=getattr(n.items[1],'low','')
   if not name:continue
   if name in ('fn2-b-ctl-slot','fn2-b-format-floor'):
    other=named(after,name)
    self.assertEqual(before[n.items[3].start:n.items[3].end],after[other.items[3].start:other.items[3].end])
    a=before[n.items[-1].start:n.items[-1].end];b=after[other.items[-1].start:other.items[-1].end]
    self.assertEqual(a,b.replace(' (fn2-b-run-cursor-rows profile)',''))
   else:self.assertIn(before[n.start:n.end],after,name)
 def test_dependencies_defined_before_geometry_use(self):
  s=(ROOT/'books/machines-b.lisp').read_text()
  pos=lambda n:named(s,n).start
  self.assertLess(pos('fn2-b-read-rows'),pos('fn2-b-checkpoint-source-cursor'))
  self.assertLess(pos('*fn2-b-query-read-rows*'),pos('*fn2-b-query-loader-jobs*'))
  self.assertLess(pos('fn2-b-run-cursor-rows'),pos('fn2-b-format-floor'))
  self.assertLess(pos('fn2-b-upload-windows'),pos('fn2-b-run-loader-row'))
 def test_preserves_richer_current_map_terms(self):
  # A newer source map's CNS suffix survives the additive loader projection.
  old=DATA['before'].replace('(+ 9 (fn2-b-upload-windows profile) (fn2-b-ctl-rows profile))',
    '(+ 9 (fn2-b-upload-windows profile) (fn2-b-ctl-rows profile) (fn2-b-cns-source-rows profile))')
  self.assertIn('(fn2-b-cns-source-rows profile) (fn2-b-run-cursor-rows profile)',project(old))
 def test_fixed_private_pair_is_guarded(self):
  s=(ROOT/'books/machines-b.lisp').read_text()
  for n in ('fn2-b-checkpoint-source-cursor-from-rows','fn2-b-event-archive-cursor-from-rows'):
   f=named(s,n);self.assertIn('(fn2-b-fixed-cursor-rows-p rows)',s[f.start:f.end])
  f=named(s,'fn2-b-fixed-cursor-rows-p');self.assertIn('(<= 2 rows)',s[f.start:f.end])
if __name__=='__main__':unittest.main()
