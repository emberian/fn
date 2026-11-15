"""Narrow source controls for the actual historical recovery adapters."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
PATH=ROOT/'books/recovery-machine.lisp'

def retained_pair_errors(text):
 errors=[]
 for adapter,callee,slots in [('fn2-recovery-seal-fields','fn2-rec-seal-check',(5,6)),
                              ('fn2-recovery-context','fn2-rec-context',(10,11))]:
  form=lr.match('(defun ?name ?*body)',lr.parse(text).forms,name=adapter)[0]
  calls=lr.match('(?*xs)',[form.node],head=callee)
  if len(calls)!=1:errors.append(adapter);continue
  for slot,field in zip(slots,['history','history-incarnation']):
   node=calls[0].node.items[slot]
   if text[node.start:node.end]!=f'(fn2-rec-cand-{field} p fn2-rec-cand)':errors.append((adapter,field))
 return errors

class RecoveryHistorySource(unittest.TestCase):
 def test_actual_adapters_use_retained_candidate_pair(self):
  self.assertEqual(retained_pair_errors(PATH.read_text()),[])
 def test_old_current_configuration_substitution_is_rejected(self):
  text=PATH.read_text().replace('(fn2-rec-cand-history p fn2-rec-cand)', '(fn2-origin-history fn2-origin)')
  self.assertEqual(len(retained_pair_errors(text)),2)
 def test_actual_header_callers_retain_sixth_core_output(self):
  count=0
  for path in [PATH,ROOT/'tests/recovery-history-unit.lisp']:
   text=path.read_text()
   for call in lr.match('(?*xs)',lr.parse(text).forms,head='fn2-recovery-header'):
    # The lexical binder directly preceding the actual call must retain core.
    prefix=text[max(0,call.start-100):call.start]
    self.assertIn('payload fn2-core)',prefix)
    count+=1
  self.assertEqual(count,2)
if __name__=='__main__':unittest.main()
