"""Second exact before/after matrix and actual cold semantic composition controls."""
from pathlib import Path
import copy
import unittest
import lisp_rewrite as lr
import seal_cleanup_current_projection as p
import seal_cleanup_schema as inventory
ROOT=Path(__file__).resolve().parents[1]
class Cold(unittest.TestCase):
 def setUp(self):self.before,self.schema,self.after=p.load_case('cold')
 def test_exact_cold_before_after_projection(self):
  self.assertEqual(p.composed_project(self.before,self.schema),self.after)
 def test_exact_cold_held_fixture(self):
  self.assertEqual(p.fixture_source(self.schema,label='cold-a565'),(ROOT/'tools/fixtures/seal-release-held-cold-after.lisp').read_text())
 def test_current_fixture_covers_actual_schema(self):
  self.assertEqual(p.fixture_source(p.schema_from_current(),label='cold-a565'),(ROOT/'tests/seal-release-row-held-unit.lisp').read_text())
 def test_cold_physical_fence_before_cache_and_pool(self):
  n=p.one('(defun fn2-seal-release-row ?*args)',(ROOT/'books/sealer.lisp').read_text())
  fence=lr.match('((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) (mv :cache fn2-run-installed fn2-run-cache fn2-pool))',[n]);self.assertEqual(len(fence),1)
  for pattern in ('(fn2-run-cache-peek ?*args)','(fn2-pool-release ?*args)'):
   self.assertLess(fence[0].start,lr.match(pattern,[n])[0].start)
 def test_busy_remains_parked(self):
  source=(ROOT/'books/machines-c-sealer-events.lisp').read_text()
  self.assertTrue(lr.match('((:idle :busy) (:park ?*args))',lr.parse(source).forms))
 def test_scalar_and_column_snapshots_are_complete(self):
  schema=p.schema_from_current();source=p.fixture_source(schema,label='cold-a565')
  for carrier,short in [('fn2-run-installed','run-installed'),('fn2-run-cache','run-cache'),('fn2-overlays','overlays'),('fn2-seals','seals'),('fn2-pool','pool')]:
   row=p.one(f'(defun fn2-srh-{short}-rows ?*args)',source)
   for c in inventory.columns(schema,carrier):self.assertTrue(lr.match(f'({carrier}-{c.items[0].low} i {carrier})',[row]))
   scalars,_=inventory.extras(schema,carrier)
   if scalars:
    snapshot=p.one(f'(defun fn2-srh-{short}-snapshot ?*args)',source)
    for name in scalars:self.assertTrue(lr.match(f'({name} {carrier})',[snapshot]))
  self.assertEqual(len(lr.match('(fn2-srh-run-installed-rows 0 fn2-run-installed)',lr.parse(source).forms)),1)
 def test_wrong_schema_refuses_before_fence_projection(self):
  _,root_schema,_=p.load_case('root')
  with self.assertRaisesRegex(ValueError,'before-schema differs'):p.project(self.before,root_schema)
 def test_appended_scalar_and_version_floor_are_not_silently_removed(self):
  schema=copy.deepcopy(self.schema);text=schema['declarations']['fn2-run-installed'];n=lr.parse(text).forms[0]
  i=next(i for i,x in enumerate(n.items) if getattr(x,'low',None)==':extra-fields');extras=n.items[i+1]
  schema['declarations']['fn2-run-installed']=lr.write(text,[(extras.end-1,extras.end-1,' (fn2-run-installed-version-floor :type (unsigned-byte 60) :initially 0) (fn2-run-installed-probe :type (unsigned-byte 32) :initially 0)')])
  source=p.fixture_source(schema,label='future scalar fixture');snapshot=p.one('(defun fn2-srh-run-installed-snapshot ?*args)',source)
  for field in ('physical-count','version-floor','probe'):
   self.assertTrue(lr.match(f'(fn2-run-installed-{field} fn2-run-installed)',[snapshot]))
 def test_parent_runtime_is_read_only_to_projection(self):
  names=set(p.project(self.before,self.schema));self.assertEqual(names,set(self.before))
  self.assertNotIn('books/pool.lisp',names);self.assertNotIn('books/overlay.lisp',names)
if __name__=='__main__':unittest.main()
