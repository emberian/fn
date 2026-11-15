"""Lossless canonical symbol-data controls; no ACL2/Lean admission claim."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).parents[1] / 'meta/emit'))
import emit_certificate as c


def symbol(package, name):
    return c.List([c.Atom(':SYMBOL'), c.List(map(c.Atom, map(str, map(ord, package)))),
                   c.List(map(c.Atom, map(str, map(ord, name))))])


class CanonicalSymbolValues(unittest.TestCase):
    def test_package_and_numeric_name_identity(self):
        for package, name, expected in [
            ('KEYWORD', 'SIZE', '(Val.sym ":SIZE")'),
            ('ACL2', ':SIZE', '(Val.sym "ACL2:::SIZE")'),
            ('COMMON-LISP', 'NIL', 'Val.nil'),
            ('ACL2', 'NIL', '(Val.sym "ACL2::NIL")'),
            ('KEYWORD', 'NIL', '(Val.sym ":NIL")'),
            ('COMMON-LISP', 'T', 'Val.t'),
            ('ACL2', '123', '(Val.sym "ACL2::123")'),
            ('ACL2', 'COMMON-LISP::T', '(Val.sym "ACL2::COMMON-LISP::T")'),
        ]:
            self.assertEqual(c.val(c.decode(symbol(package, name))), expected)

    def test_acl2_nil_is_not_a_list_terminator(self):
        improper = c.List([c.Atom(':CONS'), symbol('KEYWORD', 'OK'), symbol('ACL2', 'NIL')])
        decoded = c.decode(improper)
        self.assertEqual(str(decoded[1]), '.')
        self.assertIn('ACL2::NIL', c.val(decoded))
        with self.assertRaisesRegex(ValueError, 'improper canonical list'):
            c.object_list(improper)
        proper = c.List([c.Atom(':CONS'), symbol('KEYWORD', 'OK'), symbol('COMMON-LISP', 'NIL')])
        self.assertEqual(len(c.object_list(proper)), 1)

    def test_unknown_package_fails_closed(self):
        with self.assertRaisesRegex(ValueError, 'unsupported package'):
            c.decode(symbol('UNKNOWN', 'SIZE'))


if __name__ == '__main__':
    unittest.main()
