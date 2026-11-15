"""Structural controls for actual ACL2 macro result shapes, not admission."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).parents[1] / 'tools'))
import lisp_rewrite as lr


class TranslationEventResults(unittest.TestCase):
    def test_all_live_check_macros_return_uniform_error_triples(self):
        source = lr.parse(Path(__file__).parents[1] / 'books/translation-validation.lisp')
        names = {'fn2-tv-check-function', 'fn2-tv-check-manifest',
                 'fn2-tv-check-arm-inventory', 'fn2-tv-check-functions',
                 'fn2-tv-check-packed-functions', 'fn2-tv-check-served-closure'}
        macros = [m.node for m in lr.match('(defmacro ?name ?*body)', source.forms, deep=False)
                  if m.captures['name'].low in names]
        self.assertEqual(len(macros), 6)
        for macro in macros:
            success = lr.match("(if ?test (value '(value-triple ?tag)) (er soft ?*args))", [macro])
            self.assertEqual(len(success), 1, lr.flat(macro.items[1]))
            self.assertFalse(lr.match("(if ?test '(value-triple ?tag) (er soft ?*args))", [macro]))

    def test_old_mixed_result_shape_is_detected(self):
        bad = lr.parse("(make-event (if t '(value-triple :ok) (er soft 'bad \"no\")))")
        self.assertEqual(len(lr.match("(if ?test '(value-triple ?tag) (er soft ?*args))", bad.forms)), 1)


if __name__ == '__main__':
    unittest.main()
