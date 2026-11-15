"""Census lowering preserves actual forms and removes the boot include cycle."""
from pathlib import Path
import hashlib,json,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import certify_books as cb
class CensusDependency(unittest.TestCase):
 def test_all_decision_guard_and_statement_forms_unchanged(self):
  s=(ROOT/'books/checkpoint-recovery-census.lisp').read_text()
  actual=[hashlib.sha256(s[f.start:f.end].encode()).hexdigest() for f in lr.parse(s).forms
          if not(hasattr(f,'items') and f.items and getattr(f.items[0],'low','')=='include-book')]
  self.assertEqual(actual,json.loads((ROOT/'tools/fixtures/checkpoint-census-lower-forms.json').read_text()))
 def test_actual_executor_dependency_graph_has_no_cycle(self):
  self.assertIsNone(cb.cycle_through(cb.local_closure(['books/executor'])))
 def test_only_lower_state_and_checkpoint_are_direct_dependencies(self):
  s=(ROOT/'books/checkpoint-recovery-census.lisp').read_text()
  self.assertNotIn('(include-book "boot-kind")',s)
  self.assertIn('(include-book "boot-config-state")',s)
  self.assertIn('(include-book "checkpoint")',s)
if __name__=='__main__':unittest.main()
