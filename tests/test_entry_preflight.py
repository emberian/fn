"""Negative controls for the selected-entry interface preflight."""
import json
from pathlib import Path
import tempfile
import unittest
from tools.extract.entry_preflight import inspect


class EntryPreflight(unittest.TestCase):
    def report(self, native, functions=(), counterparts=()):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, ir, inv = (root / n for n in ('native.lisp', 'core.json', 'inventory.json'))
            source.write_text(native)
            ir.write_text(json.dumps({'functions': list(functions)}))
            inv.write_text(json.dumps({'star1_names': list(counterparts)}))
            return inspect([source], ir, inv, ['fnn-entry'])

    def test_transitive_missing_counterpart_not_hidden_by_definition(self):
        source = "(defun fnn-entry () (fnn-child)) (defun fnn-child () (fnn-core 'fn-real 3))"
        functions = [{'name': 'ACL2::FN-REAL', 'kind': 'defun'}]
        r = self.report(source, functions)
        self.assertEqual(r['missing_demands'][0]['status'], 'missing-counterpart')
        self.assertEqual(r['missing_demands'][0]['route'], ['fnn-entry', 'fnn-child'])
        self.assertEqual(self.report(source, functions, ['ACL2::FN-REAL'])['status'],
                         'static-selection-present')

    def test_strings_comments_and_quoted_data_are_not_calls(self):
        r = self.report('''(defun fnn-entry () "(fnn-core 'fn-string)"
        ; (fnn-core 'fn-comment)
        '(fnn-core 'fn-data))''')
        self.assertEqual(r['demands'], [])
        self.assertEqual(r['unresolved'], [])

    def test_dynamic_dispatch_cannot_turn_green(self):
        r = self.report('(defun fnn-entry (operation) (fnn-core operation))')
        self.assertEqual(r['status'], 'incomplete')
        self.assertEqual(r['unresolved'][0]['kind'], 'dynamic-core-dispatch')

    def test_real_callback_and_apply_are_followed(self):
        r = self.report("""(defun fnn-entry () (register #'fnn-callback))
        (defun fnn-callback () (apply #'fnn-core 'fn-needed nil))""")
        self.assertEqual(r['missing_demands'][0]['subject'], 'fn-needed')

    def test_macro_expansion_stays_unresolved(self):
        r = self.report("(defmacro fnn-m () `(fnn-core 'fn-needed)) (defun fnn-entry () (fnn-m))")
        self.assertEqual(r['status'], 'incomplete')
        self.assertEqual(r['unresolved'][0]['kind'], 'macro-expansion-required')

    def test_unrelated_function_does_not_expand_selection(self):
        r = self.report("(defun fnn-entry () nil) (defun fnn-unused () (fnn-core 'fn-other))")
        self.assertEqual(r['native_functions_visited'], ['fnn-entry'])
        self.assertEqual(r['demands'], [])

    def test_external_hole_not_provided_by_counterpart_name(self):
        r = self.report("(defun fnn-entry () (fnn-core 'fn-hole))",
                        [{'name': 'ACL2::FN-HOLE', 'kind': 'host-defined'}], ['ACL2::FN-HOLE'])
        self.assertEqual(r['missing_demands'][0]['status'], 'external-implementation-required')

    def test_counterpart_package_does_not_alias_native_definition(self):
        r = self.report("(defun fnn-entry () nil) (defun acl2_*1*_acl2::fnn-entry () nil)")
        self.assertEqual(r['native_functions_visited'], ['fnn-entry'])

    def test_duplicate_definition_refused(self):
        with self.assertRaisesRegex(ValueError, 'duplicate native'):
            self.report('(defun fnn-entry () nil) (defun fnn-entry () t)')


if __name__ == '__main__':
    unittest.main()
