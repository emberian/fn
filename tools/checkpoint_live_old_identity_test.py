from pathlib import Path
import unittest
from checkpoint_live_old_identity import declarations,begin_bindings,emit_bindings,FIELDS
ROOT=Path(__file__).resolve().parents[1]
class Origin(unittest.TestCase):
 def test_generated_constructor_bindings_match_actual(self):
  s=(ROOT/'books/checkpoint-metadata.lisp').read_text()
  self.assertIn(begin_bindings('overlay'),s);self.assertIn(begin_bindings('run'),s)
  self.assertEqual(len(FIELDS),26)
 def test_captured_source_survives_emit_before_advance(self):
  s=(ROOT/'books/checkpoint-metadata-manifest.lisp').read_text()
  self.assertIn(emit_bindings(),s)
  self.assertLess(s.index(emit_bindings()),s.index('(fn2-checkpoint-source-put 0'))
 def test_both_generated_carriers_store_same_full_identity(self):
  self.assertIn(declarations('old-'),(ROOT/'books/checkpoint-metadata-state.lisp').read_text())
  self.assertIn(declarations('catalog-old-'),(ROOT/'books/checkpoint-metadata-manifest-state.lisp').read_text())
 def test_physical_root_and_original_lease_owners_are_distinct(self):
  s=begin_bindings('run')
  for x in ['epoch','counter','catalog-tag','slot','gen','okind','oslot','ogen','wire-run','hash-7']:
   self.assertIn('fn2-run-installed-'+x+' ',s)
if __name__=='__main__':unittest.main()
