import unittest
from explicit_bstar_import import rewrite

class ExplicitBstarImportTests(unittest.TestCase):
    def test_add_once_preserves_existing_text(self):
        src = '; lead\n(in-package "ACL2")\n(defun f (x) (b* ((y x)) y)) ; tail\n'
        updated = rewrite(src)
        self.assertIn('(include-book "std/util/bstar" :dir :system)', updated)
        self.assertTrue(updated.endswith('(defun f (x) (b* ((y x)) y)) ; tail\n'))
        self.assertEqual(rewrite(updated), updated)

    def test_comments_and_strings_do_not_need_macro(self):
        src = '(in-package "ACL2")\n; (b* ((x 1)) x)\n(defconst *s* "(b* ((x 1)) x)")\n'
        self.assertEqual(rewrite(src), src)

    def test_other_include_does_not_supply_ambient_dependency(self):
        src = '(in-package "ACL2")\n(include-book "alloc-unit")\n(defun f () (B* ((x 1)) x))\n'
        self.assertNotEqual(rewrite(src), src)

    def test_missing_package_refuses(self):
        with self.assertRaises(ValueError):
            rewrite('(defun f () (b* ((x 1)) x))')

if __name__ == '__main__':
    unittest.main()
