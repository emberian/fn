"""Actual boot/replay routing controls; not ACL2 execution or crash qualification."""
from pathlib import Path
import unittest,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp

def walk(x):
 if isinstance(x,list):
  yield x
  for child in x:yield from walk(child)
def calls(x,name):return [n for n in walk(x) if n and n[0]==name]
def tree(path):return [read_sexp(x) for x in forms((ROOT/path).read_text())]
def named(t,head,name):return next(n for n in walk(t) if len(n)>2 and n[:2]==[head,name])
def suffix_guarded(t):
 f=named(t,'defun','fn2-rp-release-settle')
 return all(calls(f,n) for n in ('fn2-rp-release-current-p','fn2-rp-release-read-target-p','fn2-checkpoint-release-inventory-applied-p','fn2-release-replay-settlement-progress')) and not calls(f,'fn2-alloc-free')
class RecoveryJoin(unittest.TestCase):
 def test_actual_stage8_requires_applied_inventory_and_original_source(self):
  t=tree('books/recovery-release.lisp')
  self.assertTrue(suffix_guarded(t))
  import copy
  bad=copy.deepcopy(t)
  for n in calls(bad,'fn2-checkpoint-release-inventory-applied-p'):n[0]='unrelated'
  self.assertFalse(suffix_guarded(bad))
  step=named(t,'defun','fn2-recovery-release-step')
  self.assertTrue(calls(step,'fn2-rp-release-settle'))
  self.assertFalse(any(n[:2]==['mv',':blocked'] for n in walk(step)))
 def test_replay_advances_only_kernel_returned_original_next(self):
  text=(ROOT/'books/recovery-machine.lisp').read_text()
  start=text.index('  (replay-release-check ');end=text.index('  (replay-record ',start)
  row=read_sexp(text[start:end])
  sets=calls(row,':set')
  self.assertEqual(sets,[[ ':set',['rc-stage','11'] ],[':set',['rc-roff','next'],['rc-stage','0']]])
  self.assertIn([':settled'],list(walk(row)))
  self.assertIn([':otherwise',[':stop',':recovery-replay']],list(walk(row)))
 def test_boot_materializes_after_bank_protection_before_index_handoff(self):
  text=(ROOT/'books/boot.lisp').read_text()
  self.assertIn('(include-book "checkpoint-release-inventory-apply")',text)
  self.assertIn('(fn2-checkpoint-release-inventory-apply-operations)',text)
  start=text.index('  (:checkpoint-bank-protect\n');end=text.index('  (:checkpoint-release-inventory-apply ',start)
  self.assertIn(':checkpoint-release-inventory-apply',text[start:end])
  start=end;end=text.index('\n  (:',start+4)
  row=read_sexp(text[start:end])
  self.assertTrue(calls(row,'fn2-boot-checkpoint-release-inventory-apply'))
  self.assertIn([':applied'],list(walk(row)))
  self.assertIn([':next',':recover'],list(walk(row)))
 def test_apply_arm_pays_its_actual_public_face(self):
  provider=tree('books/checkpoint-release-inventory-apply.lisp')
  face=named(provider,'defcost','fn2-boot-checkpoint-release-inventory-apply')
  cost=int(face[face.index(':bytes')+1])
  text=(ROOT/'books/boot.lisp').read_text()
  start=text.index('  (:checkpoint-release-inventory-apply :on-refusal')
  end=text.index('  (:recover :on-refusal',start)
  row=read_sexp(text[start:end])
  charges=calls(row,':charge')
  self.assertEqual(len(charges),2)
  self.assertTrue(all(int(c[c.index(':bytes')+1])>=cost for c in charges))
  old=read_sexp(text[start:end].replace(':bytes 4096',':bytes 256'))
  self.assertFalse(all(int(c[c.index(':bytes')+1])>=cost for c in calls(old,':charge')))
 def test_no_early_event_complete_before_inventory_terminal(self):
  text=(ROOT/'books/checkpoint-restore-events.lisp').read_text()
  finish=named(tree('books/checkpoint-restore-events.lisp'),'fn2-checkpoint-release-reader-operation','fn2-checkpoint-restore-events-inventory-finish')
  self.assertTrue(calls(finish,'fn2-checkpoint-restore-release-inventory-complete-p'))
  self.assertIn('*fn2-checkpoint-restore-events-phase-complete*',str(finish))
  self.assertIn(':inventory-ready',text)
if __name__=='__main__':unittest.main()
