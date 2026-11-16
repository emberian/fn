"""Connected BOOT wrapper controls; no ACL2 or device execution."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
SOURCE=(ROOT/'books/boot-checkpoint-core.lisp').read_text()
def head(n):return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Pre):yield from walk(n.node)
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
NODES=[n for f in lr.parse(SOURCE).forms for n in walk(f)]
DEFS={n.items[1].low:n for n in NODES if head(n)=='defun'}
def body(name):n=DEFS[name];return SOURCE[n.start:n.end]
class BootCore(unittest.TestCase):
 def test_live_owner_and_actual_genesis_exhaustion(self):
  text=body('fn2-boot-checkpoint-owner-p')
  for required in ('fn2-boot-snapshot-read-code','fn2-machine-generation','fn2-machine-kind','row-pending 0','row-stage 0','(null (fn2-boot-config-groups','row-index (fn2-boot-config-count','row-total (fn2-boot-config-count'):self.assertIn(required,text)
  self.assertNotIn('(+ 1 (fn2-boot-config-count',text)
 def test_full_receipt_and_read_completion_are_not_ready_flags(self):
  text=body('fn2-boot-bootstrap-current-p')
  self.assertIn('fn2-boot-bootstrap-receipt-p',text)
  self.assertIn('fn2-boot-config-image-size',text)
  self.assertIn('fn2-boot-checkpoint-descriptor-target-pool',text)
  for field in ('offset','pending','event-ready','outcome','count'):self.assertIn('fn2-machine-'+field,body('fn2-boot-checkpoint-read-complete-p'))
  self.assertNotIn('update-fn2-boot-config',SOURCE)
 def test_no_parent_core_access_under_borrowed_children(self):
  for n in NODES:
   if head(n)=='stobj-let':
    # Body after bindings/outputs; final CORE reassembly is deliberately outside.
    for x in walk(n.items[3]):
     if isinstance(x,lr.Atom):self.assertNotEqual(x.low,'fn2-core')
 def test_bounded_resumable_verify_and_canonical_only(self):
  text=body('fn2-boot-bootstrap-verify')
  self.assertIn('(<= 24576 budget)',text);self.assertIn('(mv :more fn2-core)',text)
  self.assertEqual(text.count('(fn2-boot-bootstrap-verify-pool '),1)
  self.assertIn('fn2-checkpoint-bootstrap-unit',text)
  self.assertNotIn('fn2-boot-save-geometry',SOURCE)
  self.assertNotIn('fn2-format-anchor-decode',SOURCE)
 def test_create_anchor_uses_actual_owned_bytes(self):
  text=body('fn2-boot-checkpoint-anchor-zero')
  for required in ('fn2-boot-bootstrap-current-p','row-create 1','fn2-pool-reset','fn2-boot-pad *fn2-format-sector-size* 0'):self.assertIn(required,text)
  text=body('fn2-boot-checkpoint-anchor-step')
  for required in ('fn2-boot-anchor-admit-pool','row-checkpoint-length','row-rx-slot','row-rx-gen'):self.assertIn(required,text)
 def test_descriptor_has_one_existing_emitter(self):
  self.assertEqual(SOURCE.count('(fn2-boot-descriptor-operations)'),1)
  self.assertNotIn('(defun fn2-boot-checkpoint-descriptor-check',SOURCE)
 def test_no_wide_results_or_duplicate_formals(self):
  for n in NODES:
   if head(n)=='mv':self.assertLessEqual(len(n.items)-1,32)
  for name,n in DEFS.items():
   args=[x.low for x in n.items[2].items];self.assertEqual(len(args),len(set(args)),name)
if __name__=='__main__':unittest.main()
