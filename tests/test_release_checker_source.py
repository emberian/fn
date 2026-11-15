import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import release_checker_source as r
from lisp_rewrite import parse
class Checker(unittest.TestCase):
    def test_exact_checker_receipt(self):
        for text in [r.columns(),r.capture(),r.matches()]:
            self.assertEqual(len(parse(text).forms),7)
        for f in r.FIELDS:
            self.assertIn('checker-'+f,r.capture())
            self.assertIn('fn2-fc-'+f,r.matches())
        self.assertIn('(checker-phase :u8)',r.columns())
        self.assertIn('(checker-pos :u32)',r.columns())
    def test_actual_context_constructor_is_the_record(self):
        text=r.context_matches((Path(__file__).resolve().parents[1]/'books/recovery.lisp').read_text())
        self.assertEqual(len(parse(text).forms),14)
        self.assertIn('fn2-fc-context-previous-commit',text)
        self.assertIn('(if (zp commit) 0 (- commit 1))',text)
        with self.assertRaises(ValueError):r.context_matches('(unrelated)')
if __name__=='__main__':unittest.main()
