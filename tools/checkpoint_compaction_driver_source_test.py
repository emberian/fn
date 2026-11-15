"""Actual ROOT1 source projection/ABI/write controls; no runtime qualification."""
from pathlib import Path
import unittest
import lisp_source as ls
import lisp_rewrite as lr
import checkpoint_compaction_driver_port as port
ROOT=Path(__file__).resolve().parents[1]
TEXT=(ROOT/'books/checkpoint-metadata-driver.lisp').read_text()

def sexps(text):return [ls.read_sexp(f) for f in ls.forms(text)]
def walk(x):
 if not isinstance(x,list) or not x:return
 if x[0]=='quote':return
 yield x
 for y in x:yield from walk(y)
def operations():return {x[1]:x for x in sexps(TEXT) if isinstance(x,list) and x and x[0]=='fn2-checkpoint-root1-operation'}
def assigned(tree):
 result=set()
 for n in walk(tree):
  if n[0]=='b*':
   for binding in n[1]:
    lhs=binding[0]
    if isinstance(lhs,str) and lhs.startswith('fn2-'):result.add(lhs)
    if isinstance(lhs,list) and lhs and lhs[0]=='mv':
     result.update(x for x in lhs[1:] if isinstance(x,str) and x.startswith('fn2-'))
  if n[0]=='fn2-checkpoint-root1-call':result.update(port.rows[n[1]])
 return result

class Driver(unittest.TestCase):
 def test_actual_is_named_frozen_source_projection(self):port.validate(TEXT)
 def test_all_assigned_lower_carriers_are_retained(self):
  for name,body in operations().items():
   self.assertFalse(assigned(body)-set(port.rows[name]),(name,assigned(body)-set(port.rows[name])))
 def test_actual_output_limits_and_readonly_inputs(self):
  self.assertEqual(port.COUNTS['fn2-checkpoint-root1-step'],32)
  self.assertEqual(port.COUNTS['fn2-checkpoint-root1-read'],19)
  self.assertTrue(all(n<=32 for n in port.COUNTS.values()))
  self.assertIn('fn2-checkpoint-predecessor-control',port.EXPECTED)
  self.assertNotIn('fn2-checkpoint-predecessor-control',port.rows['fn2-checkpoint-root1-step'])
  self.assertNotIn('fn2-checkpoint-bank-admission',port.rows['fn2-checkpoint-root1-step'])
 def test_actual_defun_scalar_arities(self):
  defs={}
  for p in (ROOT/'books').glob('*.lisp'):
   for f in lr.match('(defun ?name ?*body)',lr.parse(p.read_text()).forms,deep=True):
    n=f.node
    if not hasattr(n.items[2],'items'):continue
    defs.setdefault(lr.emit(n.items[1],drop_comments=True),set()).add(len(n.items[2].items))
  calls=0
  for op in operations().values():
   for n in walk(op[3:]):
    if isinstance(n[0],str) and n[0] in defs:
     self.assertIn(len(n)-1,defs[n[0]],n[0]);calls+=1
  self.assertGreater(calls,65)
 def test_all_originals_hooks_and_empty_actual_reader_connected(self):
  for name in ('source-key','source-end','empty-end'):
   self.assertIn('fn2-checkpoint-predecessor-'+name,TEXT)
  for name in ('capture-step','empty-next','complete-step'):
   self.assertIn('fn2-checkpoint-predecessor-'+name,TEXT)
  self.assertIn('fn2-checkpoint-compaction-empty-step',TEXT)
  self.assertIn('fn2-checkpoint-compaction-reader-issue',TEXT)
  self.assertNotIn('(fn2-checkpoint-source-step ',TEXT)
  self.assertNotIn('(fn2-checkpoint-source-begin ',TEXT)
  self.assertNotIn('fn2-checkpoint-source-selectedp',TEXT)
 def test_finish_reuses_actual_detach_recipe(self):
  text=(ROOT/'books/checkpoint-compaction-reader-finish.lisp').read_text()
  self.assertIn('(fn2-checkpoint-source-reader-detach-owned-body)',text)
  self.assertIn('fn2-checkpoint-compaction-produced-p',text)
  self.assertNotIn('fn2-checkpoint-source-phase-done',text)
 def test_negative_guard_hook_projection_and_read_changes_refused(self):
  for a,b in [('fn2-checkpoint-bank-admission-ready-p','fn2-checkpoint-bank-admission-wfp'),
              ('fn2-checkpoint-predecessor-source-key','fn2-checkpoint-predecessor-source-end'),
              ('fn2-checkpoint-compaction-reader-issue','fn2-checkpoint-source-reader-issue'),
              ('(schema-open','(schema')]:
   if a not in TEXT:continue
   with self.assertRaises(ValueError):port.validate(TEXT.replace(a,b,1))
  with self.assertRaises(ValueError):port.validate(TEXT.replace('fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control fn2-checkpoint-bank-admission))','fn2-checkpoint-predecessor-control fn2-checkpoint-bank-admission))',1))
if __name__=='__main__':unittest.main()
