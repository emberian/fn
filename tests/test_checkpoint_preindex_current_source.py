"""Actual declaration-source projection controls; world gate remains unrun."""
from pathlib import Path
import json,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from checkpoint_preindex_current_rewrite import DATA,event,src,project_index,project_sealer,project_read_work

def norm(x):
 if isinstance(x,lr.Lst):return [norm(y) for y in x.items]
 if isinstance(x,lr.Pre):return [x.prefix,norm(x.node)]
 return getattr(x,'low',getattr(x,'text',''))
class Preindex(unittest.TestCase):
 def test_named_projection_idempotent(self):
  for book,fn in (('assembly-index',project_index),('machines-c-sealer',project_sealer),('runs-assemble',project_read_work)):
   text=(ROOT/'books'/(book+'.lisp')).read_text();self.assertEqual(fn(DATA['before'][book]),text);self.assertEqual(fn(text),text)
 def test_all_existing_kind_includes_keep_order_and_new_last(self):
  def includes(t):return [m.captures['name'].text for m in lr.match('(include-book ?name)',lr.parse(t).forms,deep=False)]
  old=includes(DATA['before']['assembly-index']);actual=(ROOT/'books/assembly-index.lisp').read_text();new=includes(actual)
  self.assertEqual(new[:len(old)],old)
  self.assertEqual(new[len(old):],['"checkpoint-cbase-kind"','"boot-reader-kind"','"boot-semantic-kind"','"checkpoint-master-kind"'])
  self.assertLess(actual.index('(include-book "checkpoint-master-kind")'),actual.index('(fn2-machine-index-events)'))
  # A future existing kind after BOOT must retain its tag as well.
  later=DATA['before']['assembly-index'].replace('(fn2-machine-index-events)','(include-book "future-existing-kind")\n(fn2-machine-index-events)')
  out=project_index(later);self.assertLess(out.index('"future-existing-kind"'),out.index('"boot-reader-kind"'))
 def test_existing_runtime_functions_and_guards_untouched(self):
  for book in ('machines-c-sealer','runs-assemble'):
   old=DATA['before'][book];new=(ROOT/'books'/(book+'.lisp')).read_text()
   for m in lr.match('(defun ?name ?*body)',lr.parse(old).forms,deep=True):
    name=getattr(m.captures['name'],'low','')
    if not name or name in ('fn2-sealer-profilep','fn2-ra-dispatch-events'):continue
    n=lr.match('(defun '+name+' ?*body)',lr.parse(new).forms,deep=True)
    self.assertEqual(len(n),1,name);self.assertEqual(src(old,m.node),src(new,n[0].node),name)
  old=DATA['before']['machines-c-sealer'];new=(ROOT/'books/machines-c-sealer.lisp').read_text()
  self.assertIn(src(old,event(old,'defun','fn2-sealer-profilep').items[-1])[5:-1],src(new,event(new,'defun','fn2-sealer-profilep').items[-1]))
 def test_work_bound_generated_after_actual_schema_inventory(self):
  t=(ROOT/'books/runs-assemble.lisp').read_text();f=event(t,'defun','fn2-ra-dispatch-events')
  for name in ('*fn2-run-layout-max-entry-bytes*','*fn2-run-layout-max-key-octets*','*fn2-c-read-step-bytes*','*fn2-c-read-callback-bytes*'):
   self.assertEqual(len(lr.match('(defconst '+name+' ?*value)',[f],deep=True)),1,name)
   self.assertFalse(lr.match('(defconst '+name+' ?*value)',lr.parse(t).forms,deep=False),name)
  self.assertIn('(defconst *fn2-run-overlay-search-steps* *fn2-ov-search-steps*)',t)
 def test_harvest_extension_preserves_old_default_template(self):
  t=(ROOT/'books/machines-c-sealer.lisp').read_text();a=src(t,event(t,'defmacro','fn2-sealer-child'))
  donor=a.replace(' &key harvest','').replace(',@(and harvest (list :harvest harvest)) ','')
  old=DATA['before']['machines-c-sealer'];b=src(old,event(old,'defmacro','fn2-sealer-child'))
  self.assertEqual(norm(lr.parse(donor).forms[0]),norm(lr.parse(b).forms[0]))
  self.assertIn('(fn2-run-builds-init 3 fn2-run-builds)',t)
  self.assertIn('(+ *fn2-seal-writer-rows* (* 2 *fn2-run-max-levels*))',t)
 def test_reader_and_semantic_sole_registration(self):
  reader=(ROOT/'books/boot-reader-kind.lisp').read_text();semantic=(ROOT/'books/boot-semantic-kind.lisp').read_text()
  r=lr.match('(defcorechild ?field ?*body)',lr.parse(reader).forms,deep=False);s=lr.match('(defcorechild ?field ?*body)',lr.parse(semantic).forms,deep=False)
  self.assertEqual(len(r),5);self.assertEqual(len(s),2)
  fields=[m.captures['field'].low for m in r+s];self.assertEqual(len(fields),len(set(fields)))
  self.assertNotIn('fn2-core-checkpoints',fields)
  self.assertEqual((ROOT/'books/checkpoint-master-kind.lisp').read_text().count('include-book'),2)
  self.assertIn('(include-book "checkpoint-master-state")',(ROOT/'books/checkpoint-master-kind.lisp').read_text())
 def test_actual864_missing_imports_are_exact(self):
  j=json.loads((ROOT/'tools/fixtures/checkpoint-preindex-new-files.json').read_text());graph=json.loads((ROOT/'tools/fixtures/checkpoint-preindex-provider-map.json').read_text())
  import hashlib
  self.assertEqual(len(j['exact-imported']),30)
  for p in j['exact-imported']:self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),graph['closure'][p[:-5]]['sha256'],p)
  resources=(ROOT/'books/checkpoint-metadata-resources.lisp').read_text();self.assertIn('(fn2-run-installed-row-count',resources)
 def test_writer_table_alias_class_only_changes_metadata_fields(self):
  from checkpoint_preindex_current_rewrite import project_writer_table_references
  j=json.loads((ROOT/'tools/fixtures/checkpoint-writer-table-alias-source.json').read_text());count=0
  for book,before in j['before'].items():
   after=project_writer_table_references(before);self.assertEqual(project_writer_table_references(after),after)
   count+=after.count('fn2-checkpoint-writer-table')-before.count('fn2-checkpoint-writer-table')
   self.assertEqual(after.replace('fn2-checkpoint-writer-table','fn2-core-checkpoint-writer'),before)
   for m in lr.match('(defun ?name ?*body)',lr.parse(before).forms,deep=True):
    name=getattr(m.captures['name'],'low','')
    if not name:continue
    other=lr.match('(defun '+name+' ?*body)',lr.parse(after).forms,deep=True)
    self.assertEqual(src(before,m.node),src(after,other[0].node))
  self.assertEqual(count,j['expected-cost-occurrences'])
 def test_actual_registry_world_gate_prepared(self):
  t=(ROOT/'tests/checkpoint-preindex-world-unit.lisp').read_text()
  self.assertIn('(include-book "../books/assembly-index")',t)
  self.assertIn('(fn2-core-child-registry (w state))',t);self.assertNotIn('(fn2-core-events)',t)
if __name__=='__main__':unittest.main()
