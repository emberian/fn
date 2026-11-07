"""Canonical transport controls, in addition to the two kernel controls."""
import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('certificate', Path(__file__).parents[1]/'meta/emit/emit_certificate.py')
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)

class CanonicalExport(unittest.TestCase):
    def test_exact_crlf_and_integer(self):
        self.assertEqual(c.decode(c.read_canonical('(:STRING (13 10))')), '\r\n')
        self.assertEqual(str(c.decode(c.read_canonical('(:INTEGER -9007199254740993)'))), '-9007199254740993')

    def test_rational_is_not_coerced(self):
        with self.assertRaises(ValueError):
            c.decode(c.read_canonical('(:RATIONAL 3 2)'))

    def test_no_reader_or_ambiguous_atom(self):
        for text in ['#.(danger)', '(:INTEGER 1.0)', '(NIL) (NIL)', '(:STRING (256))']:
            with self.assertRaises(ValueError):
                c.decode(c.read_canonical(text))

    def test_duplicate_field_rejected(self):
        with self.assertRaises(ValueError):
            c.fields(c.read_canonical('(:VERSION 1 :VERSION 2)'))

if __name__ == '__main__': unittest.main()
