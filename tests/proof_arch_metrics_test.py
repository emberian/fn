"""Timing fixtures catch double counting of enclosing ACL2 summaries."""
import sys
import tempfile
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from proof_arch_metrics import book_metrics, collect, compare


class MetricsTests(unittest.TestCase):
    def test_wrappers_are_not_primitive_events(self):
        text = '''Summary
Form: ( DEFTHM LOCALITY ...)
Time:  2.00 seconds (prove: 1.80, print: 0.00, other: 0.20)
Summary
Form: ( DEFTHM TRANSPORT ...)
Time:  1.00 seconds (prove: 0.90, print: 0.00, other: 0.10)
Summary
Form: ( MAKE-EVENT (VALUE ...))
Time:  3.00 seconds (prove: 2.70, print: 0.00, other: 0.30)
Summary
Form: ( INCLUDE-BOOK "dependency" ...)
Time:  4.00 seconds (prove: 0.00, print: 0.00, other: 4.00)
Summary
Form: (CERTIFY-BOOK "consumer" ...)
Time:  7.00 seconds (prove: 2.70, print: 0.00, other: 4.30)
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'book.cert.out'
            path.write_text(text)
            result = book_metrics(path)
        self.assertEqual(result['primitive_event_count'], 2)
        self.assertEqual(result['primitive_event_time_s'], 3)
        self.assertEqual(result['include_time_s'], 4)
        self.assertEqual(result['certify']['total_s'], 7)
        self.assertEqual(result['max_event']['name'], 'LOCALITY')

    def test_closure_is_scoped_by_built_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / 'run.log'
            log.write_text('Built /home/build/fn2-example/books/a.cert (1.234s)\n'
                           'Built /home/build/fn2-example/tests/a-unit.cert (2.345s)\n'
                           'certify summary: 2 built, 0 failed\n')
            result = collect(root, log)
        self.assertEqual(set(result['books']), {'books/a', 'tests/a-unit'})
        self.assertEqual(result['sum_cert_pl_wall_s'], 3.579)
        self.assertEqual(result['built_count'], 2)

    def test_comparison_does_not_compare_cold_and_warm_scopes(self):
        before = {'books': {'unchanged': {'cert_pl_wall_s': 90},
                            'changed': {'cert_pl_wall_s': 10}}}
        after = {'books': {'changed': {'cert_pl_wall_s': 7},
                           'new': {'cert_pl_wall_s': 2}}}
        result = compare(before, after)
        self.assertEqual(result['common_paths'], ['changed'])
        self.assertEqual(result['before_common']['sum_cert_pl_wall_s'], 10)
        self.assertEqual(result['after_common']['sum_cert_pl_wall_s'], 7)
        self.assertEqual(result['after_added']['sum_cert_pl_wall_s'], 2)
        self.assertFalse(result['after_common']['event_data_complete'])
        self.assertIsNone(result['after_common']['primitive_event_count'])


if __name__ == '__main__':
    unittest.main()
