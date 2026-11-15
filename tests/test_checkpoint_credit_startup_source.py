"""Actual startup source routing; ACL2 execution is a separate gate."""
from pathlib import Path
import sys, unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
class CreditStartup(unittest.TestCase):
 def test_actual_init_uses_same_profile_and_refuses_before_genesis(self):
  s=(ROOT/'books/executor.lisp').read_text()
  f=next(f for f in lr.parse(s).forms if hasattr(f,'items') and len(f.items)>1 and getattr(f.items[1],'low','')=='fn2-init-executor')
  text=s[f.start:f.end]; body=text[text.index('  (b* '):]
  positions=[body.index(x) for x in ['(fn2-core-init profile fn2-core)',
   '(fn2-checkpoint-working-credit-init profile fn2-core)',
   '((unless (eq credit :ok))','(fn2-init-engine profile fn2-core)',
   '(fn2-exec-genesis (fn2-exec-rows fn2-core) 0 fn2-core)']]
  self.assertEqual(positions,sorted(positions))
  self.assertIn('(if (fn2-profile-get :image-boot profile)',body)
  self.assertIn('(mv :ok fn2-core)',body)
  self.assertIn('(fn2-core-stop *fn2-stop-reason-engine-genesis* fn2-core)',body)
 def test_materialized_wrapper_uses_actual_initialized_children(self):
  s=(ROOT/'books/checkpoint-working-credit-init.lisp').read_text()
  for x in ['(profile fn2-core)','(fn2-commit-table fn2-core)',
   '(fn2-core-commit-io fn2-core)','profile (fn2-commit-rows fn2-commit) (fn2-commit-io-rows fn2-commit-io)',
   '(fn2-core-preserves fn2-checkpoint-working-credit-init']:
   self.assertIn(x,s)
  exe=(ROOT/'books/executor.lisp').read_text()
  self.assertIn('(fn2-checkpoint-working-credit-init-events)',exe)
if __name__=='__main__': unittest.main()
