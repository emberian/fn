"""Single-row schema reset boundary; source controls, no ACL2 execution."""
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[1]
class RowReset(unittest.TestCase):
    def test_schema_drives_fields_and_private_extras_are_not_reset(self):
        s=(ROOT/'books/columns-row-reset.lisp').read_text()
        self.assertIn('(fn2-columns-put-bindings',s)
        self.assertIn('(fn2-columns-row-reset-fields cols)',s)
        self.assertIn('(fn2-decl-get :columns schema)',s)
        self.assertNotIn(':extra-fields',s)
        self.assertNotIn('resize-',s)
        self.assertIn('(natp row) (< row (,rows ,name))',s)
        self.assertIn('(eq (cadar cols) :link)',s)
    def test_no_global_init_or_public_mutation_face(self):
        s=(ROOT/'books/columns-row-reset.lisp').read_text()
        self.assertNotIn('(defcost',s)
        self.assertNotIn('COLUMNS-INIT',s.upper())
        self.assertIn(':guard (and (,p ,name) (,wfp ,name))',s)
if __name__=='__main__':unittest.main()
