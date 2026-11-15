"""Scope and actual lower-call closure for authored encoded-reader controls."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk
TEXT=(ROOT/'tests/release-inventory-encoded-reader-unit.lisp').read_text()
NODES=[read_sexp(s) for s in forms(TEXT)]
def definition(name):return next(n for n in NODES if n[:2]==['defun',name])
class EncodedReaderControls(unittest.TestCase):
    def test_actual_factory_real_seal_and_check_and_shared_decoder(self):
        body=definition('fn2-rier-body');calls=list(walk(body))
        self.assertTrue(any(n and n[0]=='fn2-ripu-body' for n in calls))
        lower=definition('fn2-rier-format')
        self.assertIn('fn2-format-drive',str(lower));self.assertIn(':page',str(lower))
        self.assertTrue(any(n[:3]==['fn2-rier-format','t','len'] for n in calls))
        self.assertTrue(any(n[:3]==['fn2-rier-format','nil','len'] for n in calls))
        self.assertTrue(any(n[:2]==['fn2-checkpoint-restore-header','6'] for n in calls))
        self.assertTrue(any(n[:2]==['fn2-checkpoint-restore-entry','6'] for n in calls))
    def test_whole_antecedent_is_asserted_not_skipped(self):
        body=definition('fn2-rier-body');calls=list(walk(body))
        self.assertIn(['fn2-fc-guard'],calls)
        self.assertTrue(any(n and n[0]=='and' and 'whole-antecedent' in n and 'tuple' in n for n in calls))
        self.assertTrue(any(n[:2]==['unless','whole-antecedent'] for n in calls))
        self.assertNotIn('set-phase',TEXT)
        self.assertNotIn('(phase ',TEXT)
        self.assertNotIn('*fn2-release-inventory-build-phase-done*',TEXT)
        self.assertNotIn('*fn2-checkpoint-restore-events-phase-complete*',TEXT)
    def test_real_same_length_namespace_and_count_wire_mutations(self):
        calls=list(walk(definition('fn2-rier-body')))
        self.assertTrue(any(n and n[0]=='fn2-checkpoint-map-header-encode' for n in calls))
        self.assertTrue(any(n[:3]==['fn2-fields-set-value','*fn2-checkpoint-map-header-field-entry-count*','2'] for n in calls))
        self.assertTrue(any(n and n[0]=='fn2-release-inventory-entry-encode' for n in calls))
        self.assertIn(['=','next','actual-end'],calls)
        self.assertIn(['eq','final-check',':bad-hash'],calls)
        self.assertIn(['eq','rejected',':coverage'],calls)
    def test_truncation_uses_actual_encoded_end_and_complete_page_extent(self):
        calls=list(walk(definition('fn2-rier-body')))
        self.assertIn(['-','actual-end','1'],calls)
        self.assertIn(['-','len','1'],calls)
        self.assertIn(['eq','short-page',':wrong-length'],calls)
        self.assertIn(['eq','truncated',':truncated'],calls)
        self.assertTrue(any(n and n[0]=='fn2-pool-logical-octets' and n[1]=='len' for n in calls))
    def test_scope_keeps_physical_source_incomplete(self):
        calls=list(walk(definition('fn2-rier-body')))
        self.assertTrue(any(n and n[0]=='not' and 'fn2-release-inventory-complete-p' in str(n) for n in calls))
        self.assertIn('SYNTHETIC',TEXT);self.assertIn('SECOND checkpoint',TEXT)
        self.assertIn('fn2-rrc-producer',TEXT);self.assertIn('fn2-ccp-restart',TEXT)
        tests=[n for n in NODES if n and n[0]=='assert-event']
        self.assertEqual(tests,[['assert-event',['fn2-rier-test',':clean']],['assert-event',['fn2-rier-test',':count']],['assert-event',['fn2-rier-test',':namespace']]])
if __name__=='__main__':unittest.main()
