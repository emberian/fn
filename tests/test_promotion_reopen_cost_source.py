"""Readonly SOURCE consistency controls; no emitted/runtime/physical proof."""
from pathlib import Path
import json,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import directory_consume_metadata_audit as a
from lisp_source import forms,read_sexp
class PromotionAudit(unittest.TestCase):
 def test_same_literal_finish_macro_is_source_not_a_new_runtime_implementation(self):
  for name in ('fn2-checkpoint-live-replace-finish','fn2-checkpoint-live-replace-reopen'):
   self.assertEqual(a.LITERAL_PROVIDERS[name],(Path('books/checkpoint-live-finish.lisp'),'fn2-checkpoint-live-finish-events'))
  literal=['defmacro','events',[],['quote',['progn',['defun','actual',['x'],['mv','x']]]]]
  self.assertEqual(a.literal_definitions(literal),[['defun','actual',['x'],['mv','x']]])
  for bad in (['defmacro','events',['body'],literal[-1]],['defmacro','events',[],['quasiquote',literal[-1][1]]],['defun','outer',['x'],['quote',['defun','fake',[],'nil']]]):
   found=a.literal_definitions(bad)
   self.assertFalse(any(f[1] in ('fake','actual') for f in found))
 def test_fail_closed_unknown_traversal_and_callee(self):
  with self.assertRaises(ValueError):a.ex(['fn2-unknown-adoption-helper','x'])
  with self.assertRaises(ValueError):a.ex(['member','x','arbitrary-source-list'])
  with self.assertRaises(ValueError):a.ex(['unbounded-recur','x'],'unbounded-recur')
  with self.assertRaises(ValueError):a.body('fn2-absent-literal-root')
 def test_model_category_sums_and_full_provider_coverage(self):
  expected={'fn2-checkpoint-live-replace-finish':(601,17,42,2,662,257,1),
            'fn2-checkpoint-live-replace-reopen':(660,17,43,4,724,320,0)}
  report=json.loads((ROOT/'tests/fixtures/promotion-reopen-carried-cost-audit.json').read_text())
  for name,(meta,spine,inputs,stores,total,read,write) in expected.items():
   self.assertEqual(a.expanded(name),{'metadata':meta,'spine':spine})
   byte=a.payload_footprint(name);self.assertEqual((byte['payload-read'],byte['payload-write']),(read,write))
   self.assertEqual(len(a.order(name)),46)
   f=a.D[name][1];x=f[3][1];ins=x[x.index(':stobjs')+1];self.assertEqual(len(ins),inputs)
   self.assertEqual(meta+spine+inputs+stores,total)
   row=report['roots'][name]
   self.assertEqual(row['face_structural_sum_upper'],total);self.assertEqual(row['payload_sum'],read+write)
   self.assertEqual({p['provider'] for p in row['components']},set(a.order(name)))
 def test_acl2_component_formulas_and_actual_cost_faces(self):
  constants={}
  def value(x):
   if isinstance(x,str):return int(x) if x.isdigit() else constants[x]
   args=[value(v) for v in x[1:]]
   if x[0]=='+':return sum(args)
   if x[0]=='*':
    import math
    return math.prod(args)
   if x[0]=='ceiling':return -(-args[0]//args[1])
   self.fail(('unaccounted constant operator',x))
  for path in ('books/checkpoint-directory-consume-work.lisp','books/checkpoint-live-finish-work.lisp'):
   for raw in forms((ROOT/path).read_text()):
    f=read_sexp(raw)
    if isinstance(f,list) and f and f[0]=='defconst':constants[f[1]]=value(f[2])
  for name,n in [('*fn2-directory-rebase-consume-steps*',211),('*fn2-checkpoint-live-promotion-steps*',662),('*fn2-checkpoint-live-reopen-steps*',724)]:self.assertEqual(constants[name],n)
  faces={f[1]:f for raw in forms((ROOT/'books/checkpoint-live-finish.lisp').read_text()) if isinstance((f:=read_sexp(raw)),list) and f and f[0]=='defcost'}
  for op,component in [('finish','promotion'),('reopen','reopen')]:
   face=faces['fn2-checkpoint-live-replace-'+op+'-op']
   self.assertEqual(face[face.index(':steps')+1],'*fn2-checkpoint-live-'+component+'-steps*')
 def test_checked_predicates_remain_full_and_historical_150_comparison(self):
  self.assertEqual(a.expanded('fn2-run-buildp')['metadata'],91)
  self.assertEqual(a.expanded('fn2-checkpoint-slotp')['metadata'],65)
  self.assertGreater(91+65,150)
  build=a.D['fn2-run-buildp'][1][-1]
  self.assertEqual(build[0],'and');self.assertIn(['fn2-run-builds-wfp','fn2-run-builds'],build)
  self.assertIn(['fn2-run-writers-wfp','fn2-run-writers'],build)
  slot=a.D['fn2-checkpoint-slotp'][1][-1]
  self.assertEqual(slot[0],'and');self.assertIn(['fn2-checkpoints-wfp','fn2-checkpoints'],slot)
 def test_source_machine_and_directory_folding_matches_actual_generators(self):
  machinery=(ROOT/'books/machines.lisp').read_text()
  self.assertIn('(cols (append `((phase (:enum ,enum ,states))) *fn2-machine-common-fields* fields))',machinery)
  self.assertIn('(tcols (fn2-machine-table-columns cols))',machinery)
  self.assertEqual(len(a.COL['fn2-checkpoint-writer']),22)
  self.assertEqual([f[0] for f in a.COL['fn2-machines']],['kind','slot','ready-prev','ready-next','wait-reason'])
 def test_recursion_dimensions_and_terminal_split_are_explicit(self):
  expected={'fn2-event-producer-roots-p':2,'fn2-checkpoint-production-roots-p':6,
            'fn2-checkpoint-summary-live-published-hash-p':8,'fn2-checkpoint-live-catalog-descriptor-p':32,
            'fn2-checkpoint-cbase-row-hash-p':8,'fn2-checkpoint-live-query-descriptor-p':32}
  for name,bound in expected.items():self.assertEqual(a.LOOPS[name],bound)
  self.assertEqual(a.expanded('fn2-event-producer-roots-p'),{'metadata':18,'spine':9})
  self.assertEqual(a.expanded('fn2-checkpoint-production-roots-p')['metadata'],42)
 def test_payload_selector_uses_one_native_word_not_eight_alternatives(self):
  self.assertEqual(a.payload_footprint('fn2-checkpoint-cbase-word')['payload-read'],4)
  self.assertEqual(a.payload_footprint('fn2-checkpoint-publication-base-word')['payload-read'],4)
  self.assertEqual(a.payload_footprint('fn2-checkpoint-cbase-row-hash-p')['payload-read'],64)
 def test_prepared_gate_calls_same_emitter_and_no_handwritten_face(self):
  gate=(ROOT/'tests/promotion-reopen-face-source-unit.lisp').read_text()
  self.assertEqual(gate.count('(fn2-arms-op-face-events '),2)
  self.assertIn('(equal (len pins) 42)',gate);self.assertIn('(equal (len rins) 43)',gate)
  self.assertIn('(fn2-arms-stobjs-of pouts)',gate);self.assertIn('(fn2-arms-stobjs-of routs)',gate)
  self.assertNotIn('(defun fn2-checkpoint-live-replace-',gate);self.assertIn('UNEXECUTED',gate)
 def test_canonical_consume_audit_regression_is_unchanged(self):
  self.assertEqual(a.expanded('fn2-directory-rebase-consume'),{'metadata':182,'spine':12})
if __name__=='__main__':unittest.main()
