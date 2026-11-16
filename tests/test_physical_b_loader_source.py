"""Named B geometry/source-order controls; no ACL2 execution claim."""
from pathlib import Path
import sys,unittest,json
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from physical_b_loader_rewrite import DATA,project,named,project_loader_prefix
class LoaderB(unittest.TestCase):
 def test_actual_projection_and_idempotence(self):
  text=(ROOT/'books/machines-b.lisp').read_text()
  self.assertEqual(project(DATA['before']),project_loader_prefix(text))
  self.assertEqual(project(project(text)),project(text))
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
 def test_exact_paired847_projection_and_idempotence(self):
  f=json.loads((ROOT/'tools/fixtures/physical-b-loader-prefix-source.json').read_text());before=f['paired-source'];after=project(before)
  self.assertEqual(project(after),after)
  row=named(after,'fn2-b-run-loader-row')
  self.assertEqual(after[row.items[-1].start:row.items[-1].end],'(+ 1 (fn2-b-sealer-hash-row profile) (nfix cursor))')
  self.assertLess(named(after,'fn2-b-sealer-hash-row').end,row.start)
  # SAME canonical paired contexts remain the authority; no copied W formula.
  for name in ('fn2-b-upload-windows','fn2-b-upload-hash-rows','fn2-b-upload-source-hash-row','fn2-b-upload-stored-hash-row','fn2-b-sealer-hash-row'):
   a=named(before,name);b=named(after,name);self.assertEqual(before[a.start:a.end],after[b.start:b.end])
  for name in ('fn2-b-ctl-slot','fn2-b-format-floor'):
   a=named(before,name);b=named(after,name)
   self.assertEqual(before[a.items[3].start:a.items[3].end],after[b.items[3].start:b.items[3].end])
   self.assertEqual(before[a.items[-1].start:a.items[-1].end],after[b.items[-1].start:b.items[-1].end].replace(' (fn2-b-run-cursor-rows profile)',''))
 def test_paired_prefix_selector_and_source_order_mutations_are_rejected(self):
  f=json.loads((ROOT/'tools/fixtures/physical-b-loader-prefix-source.json').read_text());after=project(f['paired-source'])
  def contract(s):
   row=named(s,'fn2-b-run-loader-row');provider=named(s,'fn2-b-sealer-hash-row')
   return s[row.items[-1].start:row.items[-1].end]=='(+ 1 (fn2-b-sealer-hash-row profile) (nfix cursor))' and provider.end<row.start
  self.assertTrue(contract(after))
  self.assertFalse(contract(after.replace('(+ 1 (fn2-b-sealer-hash-row profile) (nfix cursor))','(+ 1 (+ 3 (fn2-b-upload-windows profile)) (nfix cursor))')))
  row=named(after,'fn2-b-run-loader-row');s=after[row.start:row.end];without=lr.write(after,[(row.start,row.end,'')]);provider=named(without,'fn2-b-sealer-hash-row')
  self.assertFalse(contract(lr.write(without,[(provider.start,provider.start,s+'\n')])))
 def test_legacy_fallback_is_named_and_idempotent(self):
  s=project(DATA['before']);row=named(s,'fn2-b-run-loader-row')
  self.assertEqual(s[row.items[-1].start:row.items[-1].end],'(+ 1 (+ 3 (fn2-b-upload-windows profile)) (nfix cursor))')
  self.assertEqual(project_loader_prefix(s),s)
 def test_fixed_private_pair_is_guarded(self):
  s=(ROOT/'books/machines-b.lisp').read_text()
  for n in ('fn2-b-checkpoint-source-cursor-from-rows','fn2-b-event-archive-cursor-from-rows'):
   f=named(s,n);self.assertIn('(fn2-b-fixed-cursor-rows-p rows)',s[f.start:f.end])
  f=named(s,'fn2-b-fixed-cursor-rows-p');self.assertIn('(<= 2 rows)',s[f.start:f.end])
if __name__=='__main__':unittest.main()
