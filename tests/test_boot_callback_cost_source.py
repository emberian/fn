"""Fixed work SOURCE controls. No ACL2, runtime/emitted face or admission proof."""
import json,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import boot_callback_cost_audit as b
from lisp_source import forms,read_sexp
class Cost(unittest.TestCase):
 def test_closed_component_inventory(self):
  artifact=json.loads((ROOT/'tests/fixtures/boot-callback-cost-components.json').read_text())
  for row in artifact['providers']:
   self.assertEqual(row['component'],dict(b.a.body(row['provider'])))
   self.assertEqual(row['expanded'],dict(b.full(row['provider'])))
  for name,row in artifact['roots'].items():self.assertEqual(row,dict(b.full(name)))
 def test_callback_components_and_no_zero_unknown_fallback(self):
  expected={'fn2-boot-bootstrap-pack':(830,12,0),'fn2-boot-bootstrap-verify':(1077,12,0),'fn2-boot-checkpoint-anchor-zero':(690,0,0),'fn2-boot-checkpoint-anchor-step':(1381,0,1),'fn2-boot-checkpoint-descriptor-check':(1955,0,1)}
  for n,(m,s,f) in expected.items():
   got=b.full(n);self.assertEqual((got['metadata'],got['spine'],got['@format-run']),(m,s,f))
  with self.assertRaises(ValueError):b.ex(['fn2-unaccounted-helper','row'])
  with self.assertRaises(ValueError):b.ex(['member-eq','x','unbounded-list'])
 def test_model_constant_formulas(self):
  constants={'*fn2-format-anchor-max-size*':247,'*fn2-format-sector-size*':4096,'*fn2-checkpoint-geometry-record-max-size*':127,'*fn2-codec-decode-fuel*':4096,'*fn2-checkpoint-geometry-domain*':'fn2/image-geometry/v1'}
  def value(x):
   if isinstance(x,str):return x if x.startswith(':') else (int(x) if x.isdigit() else constants[x])
   args=[value(v) for v in x[1:]]
   if x[0]=='+':return sum(args)
   if x[0]=='*':
    import math
    return math.prod(args)
   if x[0]=='max':return max(args)
   if x[0]=='length':return len(args[0])
   if x[0]=='fn2-fc-domain':return {':page':'fn2/physical-page/v1',':anchor':'fn2/anchor/v1'}[args[0]]
   self.fail(('unknown formula',x))
  for raw in forms((ROOT/'books/boot-callback-work.lisp').read_text()):
   f=read_sexp(raw)
   if isinstance(f,list) and f and f[0]=='defconst':constants[f[1]]=value(f[2])
  expected={'format-anchor':6181,'format-page-conditional':1069,'boot-bootstrap-pack':842,'boot-bootstrap-verify':1089,'boot-checkpoint-anchor-zero':690,'boot-checkpoint-anchor-step':7562,'boot-checkpoint-descriptor-check':3024,'pack-bytes':8468,'verify-bytes':16724,'anchor-step-bytes':8256,'descriptor-check-conditional-bytes':8480}
  for name,n in expected.items():self.assertEqual(constants['*fn2-boot-work-'+name+'*'],n)
 def test_nested_production_snapshots_are_not_deduplicated(self):
  expected={'fn2-boot-bootstrap-pack':3,'fn2-boot-bootstrap-verify':4,'fn2-boot-checkpoint-anchor-zero':5,'fn2-boot-checkpoint-anchor-step':5,'fn2-boot-checkpoint-descriptor-target':4,'fn2-boot-checkpoint-descriptor-check':4}
  report=json.loads((ROOT/'tests/fixtures/boot-callback-cost-components.json').read_text())
  for name,count in expected.items():
   calls=b.machine_call_inventory(name)
   self.assertEqual(calls['fn2-boot-snapshot-read-code'],count)
   self.assertEqual(calls['fn2-machine-generation'],1)
   self.assertEqual(report['machine_reader_uses'][name]['fn2-machine-generation']['steps'],22)
 def test_actual_generated_not_fixture_reader_template(self):
  source=(ROOT/'books/machines.lisp').read_text()
  self.assertIn('(if (eq (,code ,@call) :ok) ,value-body',source)
  self.assertIn('(let ((code (fn2-machine-phase-read-code id fn2-core)))',source)
  self.assertEqual((b.INDEX,b.FIELD,b.SNAPSHOT),(4,22,16))
  actual=b.a.D['fn2-boot-checkpoint-owner-p'][1]
  self.assertNotIn('fixture',str(actual));self.assertEqual(b.full(actual[1])['metadata'],150)
 def test_generation_dispatch_is_actual_kind_field(self):
  actual=(ROOT/'books/machines-a-access.lisp').read_text()
  self.assertIn('(fn2-machine-index-access kind 8)',actual)
  self.assertIn('(fn2-machine-index-access slot 32)',actual)
  self.assertNotIn('(fn2-machine-index-access generation',actual)
  self.assertEqual(b.COST['fn2-machine-generation'],22)
 def test_codec_completion_storage_class(self):
  source=(ROOT/'books/layout.lisp').read_text()
  self.assertIn('(old-v (fn2-fields-value i fn2-fields))',source)
  self.assertIn('(old-status (fn2-fields-status i fn2-fields))',source)
  self.assertIn('(fn2-layout-store i old-v old-slot old-gen old-off old-len old-status fn2-fields)',source)
  self.assertEqual(b.CODECS['fn2-format-checkpoint-descriptor-decode'],(26+20*(3+5*7),1))
  self.assertEqual(b.full('fn2-checkpoint-ref-clear-build')['metadata'],5)
 def test_field_schema_contracts_are_exact_actual_declarations(self):
  def declaration(path,name):
   return next(f for raw in forms((ROOT/path).read_text()) if isinstance((f:=read_sexp(raw)),list) and f[:2]==['deflayout',name])
  ref=declaration('books/format-base.lisp','fn2-format-ref')
  self.assertEqual(len(ref[2][1]),7)
  desc=declaration('books/format-storage.lisp','fn2-format-checkpoint-descriptor')
  self.assertEqual(desc[2][0],'append');self.assertEqual(len(desc[2][1][1]),3)
  self.assertEqual(len(desc[2][2:]),5)
  for prefix in desc[2][2:]:self.assertEqual(prefix[0],'fn2-format-prefix');self.assertEqual(prefix[-1],'*fn2-format-ref*')
  geom=declaration('books/checkpoint-geometry.lisp','fn2-checkpoint-geometry-record')
  self.assertEqual(len(geom[2][1]),15)
  self.assertEqual([field[1] for field in geom[2][1]],[':u8']+[':varint']*14)
 def test_page_cost_premise_is_explicit_and_not_qualified(self):
  artifact=json.loads((ROOT/'tests/fixtures/boot-format-cost-slice.json').read_text())
  self.assertIn('pad-end=len',artifact['page_canonical']['guard_gap'])
  source=(ROOT/'books/format-check.lisp').read_text()
  self.assertIn('(equal (fn2-fc-pad-end row fn2-fc) len)',source)
  self.assertIn('(fn2-fc-set-pad-end row pad-end fn2-fc)',source)
  provider=(ROOT/'books/boot-checkpoint-core.lisp').read_text()
  self.assertNotIn('(defcost fn2-boot-checkpoint-descriptor-check ',provider)
  self.assertIn(':budget (:bytes 32768 :steps 32', (ROOT/'books/boot-kind.lisp').read_text())
if __name__=='__main__':unittest.main()
