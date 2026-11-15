"""Source and canonical boundary extraction controls; no prover or cache use."""
from pathlib import Path
from unittest import mock
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import assurance_dependencies as dependency


class DependencyBoundaries(unittest.TestCase):
    def test_current_named_assumptions_have_explicit_local_witnesses(self):
        rows = dependency.named_assumptions(ROOT)
        self.assertEqual({r['name'] for r in rows},
                         {'FN2-A-CRASH-IMAGE', 'FN2-A-INTEGRITY-EVIDENCE',
                          'FN2-A-CRYPTO-NATIVE', 'FN2-A-NATIVE-SPAN'})
        self.assertTrue(all(r['local_witness_sha256'] and not r['declaration_problems'] for r in rows))

    def test_missing_witness_and_changed_constraint_remain_explicit(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'books').mkdir()
            source = root / 'books/assumptions-test.lisp'
            source.write_text('(encapsulate (((assumption * *) => *)) (defthm boundary (equal x x)))')
            before = dependency.named_assumptions(root)[0]
            self.assertIsNone(before['local_witness_sha256'])
            self.assertTrue(before['declaration_problems'])
            source.write_text('(encapsulate (((assumption * *) => *)) (defthm boundary (equal x y)))')
            after = dependency.named_assumptions(root)[0]
            self.assertNotEqual(before['constraints'][0]['formula_sha256'], after['constraints'][0]['formula_sha256'])

    def test_symbol_and_string_identity_are_distinct(self):
        self.assertNotEqual(dependency.form_digest(dependency.ledger.Sym('x')), dependency.form_digest('x'))

    def test_selected_pair_and_missing_caller_do_not_become_proof_closure(self):
        semantic = {'selected_attachment': 'SELECTED', 'fields': {':ATTACHMENT': 'exact-field'}}
        inventory = {'roots': [{'name': 'ARM', 'function_records': [{'name': 'STUB'}]}]}
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'books').mkdir()
            packet = root / 'packet'
            packet.write_text('canonical fixture')
            with mock.patch.object(dependency.completion, 'canonical', return_value=({}, [('STUB', [], {})], ['ARM'], [])), \
                 mock.patch('served_semantic_inventory.function_semantics', return_value=semantic), \
                 mock.patch('served_semantic_inventory.semantic_inventory', return_value=inventory):
                report = dependency.boundary_report(root, packet)
            self.assertTrue(report['missing_actual_caller'])
            self.assertEqual(report['actual_theorem_constraint_dependency_closure'], 'unresolved')
            selected = report['selected_attachments'][0]
            self.assertEqual((selected['subject'], selected['selected']), ('STUB', 'SELECTED'))
            self.assertIsNone(selected['selected_record_sha256'])
            self.assertEqual(selected['required_obligation'], 'attachment_refinement:STUB')


if __name__ == '__main__':
    unittest.main()
