"""tools/attach_order_check.py: red and green on a fixture tree, green on this one."""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import attach_order_check as aoc  # noqa: E402


def tree(host_includes):
    d = Path(tempfile.mkdtemp())
    (d / "books").mkdir()
    (d / "host/native").mkdir(parents=True)
    w = lambda p, s: (d / p).write_text(s)
    w("books/impl.lisp", "(in-package \"ACL2\")\n")
    w("books/gen.lisp", "(in-package \"ACL2\")\n(defabsstobj fn-x\n  :attachable t)\n")
    w("books/gen-attach.lisp", "(in-package \"ACL2\")\n(include-book \"impl\")\n"
      "(attach-stobj fn-x fn-x-impl)\n(include-book \"gen\")\n")
    w("books/above.lisp", "(in-package \"ACL2\")\n(include-book \"gen\")\n")
    w("host/native/build.lisp", "(include-book \"books/gen-attach\")\n")
    w("host/h-host.lisp", "(in-package \"ACL2\")\n" + host_includes)
    w("books/image-world.lisp", "(in-package \"ACL2\")\n(include-book \"../host/h-host\")\n")
    return d


class AttachOrder(unittest.TestCase):
    def test_red_generic_without_attach(self):
        f = aoc.check(tree('(include-book "../books/above")\n'))
        self.assertEqual(len(f), 1)
        self.assertIn("host/h-host.lisp", f[0])

    def test_red_attach_after_generic(self):
        f = aoc.check(tree('(include-book "../books/above")\n(include-book "../books/gen-attach")\n'))
        self.assertEqual(len(f), 1)

    def test_green_attach_first(self):
        self.assertEqual(aoc.check(tree('(include-book "../books/gen-attach")\n'
                                        '(include-book "../books/above")\n')), [])

    def test_green_without_generic(self):
        self.assertEqual(aoc.check(tree("")), [])

    def test_red_when_an_attachable_impl_name_extends_the_generic(self):
        # fn-cat and fn-cat-paged are both :attachable; the generic match must not
        # take fn-x-impl's defabsstobj as a second fn-x and drop the pair.
        d = tree('(include-book "../books/above")\n')
        (d / "books/impl.lisp").write_text("(in-package \"ACL2\")\n(defabsstobj fn-x-impl\n  :attachable t)\n")
        self.assertEqual(len(aoc.check(d)), 1)

    def test_ambiguous_generic_is_a_finding(self):
        # Two books both declare :attachable fn-x: the pair is reported, not dropped.
        d = tree('(include-book "../books/gen-attach")\n')
        (d / "books/gen2.lisp").write_text("(in-package \"ACL2\")\n(defabsstobj fn-x\n  :attachable t)\n")
        f = aoc.check(d)
        self.assertEqual(len(f), 1)
        self.assertIn("books/gen.lisp", f[0])
        self.assertIn("books/gen2.lisp", f[0])

    def test_attach_without_generic_is_a_finding(self):
        d = tree("")
        (d / "books/gen.lisp").write_text("(in-package \"ACL2\")\n")
        f = aoc.check(d)
        self.assertEqual(len(f), 1)
        self.assertIn("books/gen-attach.lisp", f[0])

    def test_this_tree_is_clean(self):
        self.assertEqual(aoc.check(ROOT), [])


if __name__ == "__main__":
    unittest.main()
