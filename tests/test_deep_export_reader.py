"""The canonical export stays one book regardless of term nesting depth."""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).parents[1]/'tools'))
import ledger
import certs
import certify_books

class DeepExportReader(unittest.TestCase):
    def test_record_runner_accepts_generated_certificate_roots(self):
        for n in ['meta/emit/served-export','tests/translation-inventory-unit','tests/acl2/example-tests','books/reference']:
            self.assertIsNotNone(certify_books.BOOK_NAME.fullmatch(n))
        for n in ['../books/reference','meta/emit/../../x','host/native/node','/books/reference']:
            self.assertIsNone(certify_books.BOOK_NAME.fullmatch(n))

    def test_deep_data_preserves_include_closure(self):
        depth=3000
        with tempfile.TemporaryDirectory() as td, patch.dict(os.environ,{'FN_LEDGER_FORMS_CACHE':td+'/cache'}):
            root=Path(td)
            (root/'dep.lisp').write_text('(in-package "ACL2")')
            (root/'export.lisp').write_text('(include-book "dep")\n(check \' '+ '('*depth+'42'+')'*depth+')')
            found=certs.closure(root,'export')
            self.assertEqual(set(found),{'export','dep'})
            forms=ledger.Reader((root/'export.lisp').read_text()).top_level()
            datum=forms[1][0][1][1]
            for _ in range(depth):
                self.assertEqual(len(datum),1);datum=datum[0]
            self.assertEqual(datum,42)

    def test_mixed_reader_macros_and_delimiters(self):
        source='(a \'(b "(x)" #\\) #(1 (2))) `(,x ,@ys) . tail)'
        result=ledger.Reader(source).top_level()[0][0]
        self.assertEqual(ledger.head(result),'a')
        self.assertEqual(result[1][0],ledger.Sym('quote'))
        self.assertEqual(result[1][1][1],'(x)')
        self.assertEqual(result[-2:], [ledger.Sym('.'),ledger.Sym('tail')])
        with self.assertRaises(ledger.ReadError):ledger.Reader('((x)').top_level()
        with self.assertRaises(ledger.ReadError):ledger.Reader('(x))').top_level()

if __name__=='__main__':unittest.main()
