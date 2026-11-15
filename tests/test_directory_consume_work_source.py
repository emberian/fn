"""SOURCE category audit. No ACL2 execution or physical-work qualification."""
from pathlib import Path
import copy,subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import directory_consume_metadata_audit as audit
from lisp_source import forms,read_sexp

def decls(path):return [read_sexp(f) for f in forms((ROOT/path).read_text())]
def defs(path):return {f[1]:f for f in decls(path) if isinstance(f,list) and len(f)>3 and f[0] in ('defun','defun-inline')}
class ConsumeWork(unittest.TestCase):
 def test_actual_body_closure_metadata_and_literal_spines(self):
  result=audit.expanded('fn2-directory-rebase-consume')
  self.assertEqual(result,{'metadata':182,'spine':12})
  self.assertEqual(len(audit.order('fn2-directory-rebase-consume')),20)
  self.assertEqual(audit.expanded('fn2-checkpoint-slotp')['metadata'],65)
  self.assertEqual(audit.expanded('fn2-digest-rowp')['metadata'],19)
  # A missing metadata interaction changes the audited category, not AST nodes.
  with self.assertRaises(ValueError):audit.ex(['fn2-unaccounted-new-helper','x'])
  with self.assertRaises(ValueError):audit.ex(['member','x','unbounded-list'])
 def test_only_actual_body_wfp_checks_and_generator_shape_are_counted(self):
  generator=(ROOT/'books/columns.lisp').read_text()
  self.assertIn('(natp (,rows ,name)) (< (,rows ,name) ,bound)',generator)
  self.assertIn('(fn2-columns-wfp-conjuncts name cols)',generator)
  for table,count in [('fn2-checkpoints',15),('fn2-checkpoint-refs',12),('fn2-checkpoint-bytes',1),('fn2-digests',8)]:
   self.assertEqual(len(audit.COL[table]),count)
  self.assertEqual(audit.expanded('fn2-directory-rebase-transfer-bytes')['metadata'],0)
  self.assertEqual(audit.expanded('fn2-directory-rebase-base-seal')['metadata'],0)
 def test_payload_loop_providers_unchanged_from_real_source(self):
  old=subprocess.check_output(['git','show','88f7d786d:books/checkpoint-directory-consume.lisp'],cwd=ROOT,text=True)
  originals={f[1]:f for raw in forms(old) if isinstance((f:=read_sexp(raw)),list) and len(f)>3 and f[0]=='defun'}
  now=defs('books/checkpoint-directory-consume.lisp')
  for name in ('fn2-directory-rebase-transfer-bytes','fn2-directory-rebase-base-seal','fn2-directory-rebase-seal-p'):
   self.assertEqual(now[name],originals[name])
  self.assertEqual(audit.LOOPS['fn2-directory-rebase-transfer-bytes'],32+60*8+8)
  self.assertEqual(audit.LOOPS['fn2-directory-rebase-seal-p'],8)
  self.assertEqual(audit.LOOPS['fn2-directory-rebase-base-seal'],8)
  self.assertEqual(audit.LOOPS['fn2-event-catalog-subject-descriptor-p'],32)
  self.assertEqual(audit.LOOPS['fn2-checkpoint-summary-authority-descriptor-p'],32)
  self.assertEqual(audit.LOOPS['fn2-directory-rebase-descriptor-matchp'],8)
 def test_actual_representation_widths_match_payload_arithmetic(self):
  declaration=next(f for f in decls('books/checkpoint-summary-authority-state.lisp') if isinstance(f,list) and f[:2]==['defcolumns','fn2-checkpoint-summary-authority'])
  extras=declaration[declaration.index(':extra-fields')+1]
  specs={e[0]:e[e.index(':type')+1] for e in extras}
  self.assertEqual(specs['fn2-checkpoint-summary-authority-descriptor'],['array',['unsigned-byte','8'],['64']])
  self.assertEqual(specs['fn2-checkpoint-summary-authority-frontier'],['array',['unsigned-byte','32'],['960']])
  self.assertEqual(specs['fn2-checkpoint-summary-authority-cut-seal'],['array',['unsigned-byte','32'],['16']])
 def test_acl2_component_arithmetic_owns_final_charge(self):
  cs={f[1]:f[2] for f in decls('books/checkpoint-directory-consume-work.lisp') if isinstance(f,list) and f and f[0]=='defconst'}
  self.assertEqual(cs['*fn2-directory-consume-raw-metadata-steps*'],['+','83','6','*fn2-directory-consume-event-subject-steps*','28','*fn2-directory-consume-digest-row-steps*'])
  self.assertEqual(cs['*fn2-directory-consume-literal-spine-steps*'],['+',['+','2','1'],['+','4','1'],['+','3','1']])
  self.assertEqual(cs['*fn2-directory-consume-core-get-steps*'],'13')
  self.assertEqual(cs['*fn2-directory-consume-core-store-steps*'],'4')
  self.assertEqual(cs['*fn2-directory-rebase-consume-steps*'],['+','*fn2-directory-consume-raw-metadata-steps*','*fn2-directory-consume-literal-spine-steps*','*fn2-directory-consume-core-get-steps*','*fn2-directory-consume-core-store-steps*'])
  source=(ROOT/'books/checkpoint-directory-consume-work.lisp').read_text()
  self.assertIn('(assert-event (equal *fn2-directory-rebase-consume-bytes* 4288))',source)
  self.assertIn('(assert-event (equal *fn2-directory-rebase-consume-steps* 211))',source)
 def test_defcost_uses_same_acl2_charge_components_and_existing_inputs(self):
  face=next(f for f in decls('books/checkpoint-directory-consume.lisp') if isinstance(f,list) and f[:2]==['defcost','fn2-checkpoint-directory-rebase-consume-op'])
  self.assertEqual(face[face.index(':child')+1],'fn2-directory-rebase-consume')
  self.assertEqual(face[face.index(':bytes')+1],'*fn2-directory-rebase-consume-bytes*')
  self.assertEqual(face[face.index(':steps')+1],'*fn2-directory-rebase-consume-steps*')
  self.assertEqual(face[face.index(':descriptors')+1],'0')
  actual=defs('books/checkpoint-directory-consume.lisp')['fn2-directory-rebase-consume']
  outputs=actual[-1][-1][2:]
  for child in outputs:self.assertIn(child.replace('fn2-','fn2-core-',1) if child!='fn2-directory-rebase' else 'fn2-core-checkpoint-directory-rebase',face[face.index(':tables')+1])
 def test_prepared_gate_inspects_same_actual_emitter_and_actual_child(self):
  actual=defs('books/checkpoint-directory-consume.lisp')['fn2-directory-rebase-consume']
  xargs=actual[3][1];ins=xargs[xargs.index(':stobjs')+1]
  self.assertEqual(len(ins),13);self.assertEqual(len(actual[2]),17);self.assertEqual(len(actual[-1][-1])-1,5)
  gate=(ROOT/'tests/directory-consume-face-source-unit.lisp').read_text()
  self.assertIn('(fn2-arms-op-face-events',gate);self.assertIn('(getpropc child \'stobjs-out nil world)',gate)
  self.assertIn('(equal (strip-cars bindings) ins)',gate)
  self.assertNotIn('(defun fn2-checkpoint-directory-rebase-consume-op',gate)
  self.assertIn('UNEXECUTED',gate)
  self.assertIn("(fn2-machine-work-ceiling 'fn2-checkpoint-master world)",gate)
  self.assertIn('(fn2-run-quantitiesp *fn2-directory-rebase-consume-bytes* *fn2-directory-rebase-consume-steps* 0 0 ceiling)',gate)
  self.assertIn('(fn2-arm-get :bytes budget)',gate);self.assertIn('(fn2-arm-get :steps budget)',gate)
if __name__=='__main__':unittest.main()
