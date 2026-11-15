"""Actual two-pass prefix source/materialization route; source-only controls."""
from pathlib import Path
import sys,copy,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def op(text,name):return next(f for r in forms(text) if len(f:=read_sexp(r))>1 and f[0] in ('fn2-checkpoint-release-inventory-definition','fn2-checkpoint-release-inventory-operation') and f[1]==name)
def calls(x,name):return [n for n in walk(x) if n and n[0]==name]
def branch(text,name):
 f=op(text,'fn2-checkpoint-release-inventory-step');cond=f[3][2]
 return next(row for row in cond[1:] if name in str(row[0]))
def guarded_free(row):
 bindings=row[1][1]
 gates=[i for i,b in enumerate(bindings) if 'unless' in str(b[0]) and 'fn2-checkpoint-restore-release-inventory-materialized' in str(b)]
 frees=[i for i,b in enumerate(bindings) if calls(b,'fn2-release-target-settlement-current-progress')]
 return bool(gates and frees and max(gates)<min(frees))
class PrefixApply(unittest.TestCase):
 def setUp(self):self.text=(ROOT/'books/checkpoint-release-inventory-apply.lisp').read_text()
 def test_actual_source_joins_all_three_real_authorities(self):
  source=op(self.text,'fn2-checkpoint-release-inventory-source-p')
  for name in ('fn2-checkpoint-restore-release-inventory-complete-p','fn2-checkpoint-suffix-source-p','fn2-checkpoint-bank-protection-complete-p'):
   self.assertTrue(calls(source,name),name)
  mutant=self.text.replace('(fn2-checkpoint-bank-protection-complete-p ','(unrelated ',1)
  self.assertFalse(calls(op(mutant,'fn2-checkpoint-release-inventory-source-p'),'fn2-checkpoint-bank-protection-complete-p'))
  self.assertNotIn('fn2-checkpoint-projection-projected-p',str(source))
  self.assertNotIn('fn2-alloc-snapshot-activep',self.text)
 def test_all_claims_dominate_any_target_free(self):
  install=branch(self.text,'phase-installing')
  self.assertTrue(calls(install,'fn2-checkpoint-release-inventory-call'))
  self.assertFalse(calls(install,'fn2-release-target-settlement-current-progress'))
  applying=branch(self.text,'phase-applying')
  self.assertTrue(guarded_free(applying))
  bad=copy.deepcopy(applying)
  bad[1][1]=[b for b in bad[1][1] if not ('unless' in str(b[0]) and 'fn2-checkpoint-restore-release-inventory-materialized' in str(b))]
  self.assertFalse(guarded_free(bad))
  installed=branch(self.text,'phase-installed')
  for marker in ('fn2-checkpoint-restore-release-inventory-materialized','fn2-checkpoint-restore-release-inventory-settled','*fn2-alloc-none*','*fn2-alloc-identity-phase-idle*'):
   self.assertIn(marker,str(installed))
 def test_cursor_and_all_setter_bounds_precede_free(self):
  row=branch(self.text,'phase-applying');bindings=row[1][1]
  free=next(i for i,b in enumerate(bindings) if calls(b,'fn2-release-target-settlement-current-progress'))
  next_at=next(i for i,b in enumerate(bindings) if b[0]=='next')
  self.assertLess(next_at,free)
  tail=bindings[free+1:]
  self.assertIn('settled',str(tail));self.assertIn('cursor',str(tail))
  self.assertNotIn('fn2-alloc-edge-drop',self.text)
  self.assertNotIn('(fn2-alloc-free ',self.text)
  entry=op(self.text,'fn2-checkpoint-release-inventory-entry-p')
  for name in ('fn2-alloc-handle-code','fn2-extents-retirement','fn2-checkpoint-restore-release-entries-target-generation'):
   self.assertTrue(calls(entry,name))
 def test_terminal_is_current_source_and_actual_counts_not_boot_ownership(self):
  terminal=op(self.text,'fn2-checkpoint-release-inventory-applied-p')
  self.assertIn('fn2-checkpoint-release-inventory-source-p',str(terminal))
  for name in ('materialized','settled','total','cursor'):
   self.assertIn('fn2-checkpoint-restore-release-inventory-'+name,str(terminal))
  self.assertNotIn('fn2-alloc-identity-owner-p',str(terminal))
  self.assertNotIn('fn2-allocation-release-phase',str(terminal))
 def test_actual_boot_face_uses_registered_lenses_and_current_actor(self):
  generator=next(read_sexp(r) for r in forms(self.text) if read_sexp(r)[:2]==['defun','fn2-checkpoint-release-inventory-operation-events'])
  self.assertTrue(calls(generator,'fn2-arms-core-stobj-lets'))
  face=next(n for n in walk(generator) if n[:2]==['defun','fn2-boot-checkpoint-release-inventory-apply'])
  for name in ('fn2-boot-snapshot-read-code','fn2-machine-kind','fn2-machine-generation','fn2-machine-pending','fn2-machine-phase'):
   self.assertTrue(calls(face,name),name)
  self.assertIn('*fn2-boot-kind*',str(face));self.assertIn('*fn2-boot-state-checkpoint-release-inventory-apply*',str(face))
  self.assertEqual(face[2],['id','ogen','fn2-core'])
  self.assertTrue(calls(face,'fn2-checkpoint-selected-source-owner-kind'))
  self.assertTrue(calls(face,'fn2-checkpoint-selected-source-owner-slot'))
  self.assertTrue(calls(face,'fn2-checkpoint-selected-source-owner-gen'))
 def test_source_to_control_map_keeps_namespace_and_physical_domains(self):
  table=next(read_sexp(r) for r in forms(self.text) if read_sexp(r)[:2]==['defconst','*fn2-checkpoint-release-inventory-control-bindings*'])[2][1]
  for pair in (['journal-history','journal-history'],['history','history'],['installation-history','installation-history'],
               ['installation-position','installation-extent'],['physical-unit','descriptor-physical-unit'],
               ['journal','journal-extent'],['epoch','writer-epoch']):self.assertIn(pair,table)
  put=next(read_sexp(r) for r in forms(self.text) if read_sexp(r)[:2]==['defmacro','fn2-checkpoint-release-inventory-control-put'])
  for field in ('replay-roff','replay-rend','replay-next','checker-stage'):self.assertIn([field,'0'],list(walk(put)))
  self.assertIn('fn2-checkpoint-release-inventory-copy-hash',self.text)
 def test_factory_output_bundle_is_bounded_by_actual_declarations(self):
  const={f[1]:f[2][1] for r in forms(self.text) if (f:=read_sexp(r))[0]=='defconst'}
  self.assertEqual(len(const['*fn2-checkpoint-release-inventory-apply-children*']),25)
  self.assertEqual(len(set(const['*fn2-checkpoint-release-inventory-apply-children*'])),25)
  self.assertLessEqual(1+len(const['*fn2-checkpoint-release-inventory-apply-outputs*']),32)
  self.assertLessEqual(1+len(const['*fn2-checkpoint-release-inventory-apply-children*']),32)
  self.assertIn('fn2-checkpoint-release-reader-operation',self.text)
  self.assertNotIn('(defun fn2-checkpoint-release-inventory-preservation-specs',self.text)
 def test_phase_values_are_appended_and_real_factory_resets_count(self):
  state=(ROOT/'books/checkpoint-restore-release-inventory-state.lisp').read_text()
  self.assertIn('(:idle :captured :pages :complete :installing :installed :uncertain :applying :applied)',state)
  source=(ROOT/'books/checkpoint-restore-release-inventory-source.lisp').read_text()
  complete=next(n for r in forms(source) for n in walk(read_sexp(r)) if n[:2]==['fn2-checkpoint-release-source-definition','fn2-checkpoint-restore-release-inventory-complete-p'])
  self.assertIn('*fn2-checkpoint-restore-release-inventory-phase-applying*',str(complete))
  self.assertIn('*fn2-checkpoint-restore-release-inventory-phase-applied*',str(complete))
  reader=(ROOT/'books/checkpoint-restore-release-inventory-reader.lisp').read_text()
  self.assertEqual(reader.count('(materialized 0) (settled 0)'),2)
if __name__=='__main__':unittest.main()
