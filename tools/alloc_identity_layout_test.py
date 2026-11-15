from pathlib import Path
import unittest
import lisp_rewrite as lr
from alloc_identity_layout import rewrite, specs
ROOT=Path(__file__).resolve().parents[1]

class Layout(unittest.TestCase):
    def setUp(self):
        self.before=(ROOT/'tools/fixtures/alloc-identity-layout-before.lisp').read_text()
    def test_frozen_actual_allocator_shape_transforms_idempotently(self):
        after=rewrite(self.before)
        self.assertEqual(rewrite(after),after)
        forms=lr.parse(after).forms
        for spec in specs(): self.assertEqual(len(lr.match(spec,forms)),1)
    def test_changed_existing_field_refuses(self):
        after=rewrite(self.before).replace('fn2-alloc-identity-active :type (unsigned-byte 1)',
                                          'fn2-alloc-identity-active :type (unsigned-byte 2)',1)
        with self.assertRaises(ValueError): rewrite(after)
    def test_actual_source_uses_exact_generated_schema(self):
        actual=(ROOT/'books/alloc.lisp').read_text()
        self.assertEqual(rewrite(actual),actual)
        forms=lr.parse(actual).forms
        self.assertTrue(lr.match('(equal (fn2-alloc-identity-active fn2-extents) 1)',forms))
        for name in ('states','epochs','counters','extents'):
            self.assertTrue(lr.match(f'(resize-fn2-alloc-identity-{name} n fn2-extents)',forms))
    def test_old_extra_fields_have_no_unrelated_rewrite(self):
        before=lr.match('(defcolumns fn2-extents ?*body)',lr.parse(self.before).forms)[0].node
        after=lr.match('(defcolumns fn2-extents ?*body)',lr.parse(rewrite(self.before)).forms)[0].node
        pos=next(i for i,x in enumerate(before.items) if isinstance(x,lr.Atom) and x.low==':extra-fields')
        for field in before.items[pos+1].items:
            self.assertEqual(len(lr.match(lr.flat(field),[after])),1)

if __name__=='__main__': unittest.main()
