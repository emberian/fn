import sys, unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import seam_ratchet as S


def counts(src):
    total = {o: 0 for o in S.OPS}
    for f in S.census_text(src, "books/x.lisp"):
        for o, k in f["ops"].items():
            total[o] += k
    return total


def summ(coerce, lst, get=0):
    c = S.summarize([])
    c["occurrences"] = {"coerce": coerce, "fn-octets-list": lst, "fn-octets-get": get}
    return c


class Census(unittest.TestCase):
    def test_defun_counts(self):
        self.assertEqual(counts("(defun f (x) (coerce x 'list))")["coerce"], 1)

    def test_all_operators_and_define(self):
        t = counts("(defun f (x) (fn-octets-get 0 x))"
                   "(define g ((x)) :returns (r) (fn-octets-list x))"
                   "(defun-inline h (x) (coerce (coerce x 'list) 'string))")
        self.assertEqual((t["fn-octets-get"], t["fn-octets-list"], t["coerce"]), (1, 1, 2))

    def test_function_counted_once(self):
        fs = S.census_text("(defun f (x) (list (coerce x 'list) (coerce x 'list)))", "books/x.lisp")
        self.assertEqual(len(fs), 1)
        self.assertEqual(fs[0]["ops"], {"coerce": 2})

    def test_defthm_not_counted(self):
        self.assertEqual(counts("(defthm t1 (equal (coerce x 'list) y))")["coerce"], 0)

    def test_comments_not_counted(self):
        src = "(defun f (x) ; (coerce x 'list)\n #| (coerce y 'list) |# x)"
        self.assertEqual(counts(src)["coerce"], 0)

    def test_strings_and_chars_not_counted(self):
        src = '(defun f (x) (list "(coerce x)" #\\( #\\) x))'
        self.assertEqual(counts(src)["coerce"], 0)

    def test_quoted_data_not_counted(self):
        self.assertEqual(counts("(defun f (x) (cons '(coerce a b) x))")["coerce"], 0)

    def test_mbe_logic_arm_not_counted(self):
        src = "(defun f (x) (mbe :logic (coerce x 'list) :exec (g x)))"
        self.assertEqual(counts(src)["coerce"], 0)

    def test_mbe_exec_arm_counted(self):
        src = "(defun f (x) (mbe :logic (g x) :exec (coerce x 'list)))"
        self.assertEqual(counts(src)["coerce"], 1)

    def test_local_lemma_not_counted(self):
        src = "(local (defun aux (x) (coerce x 'list))) (encapsulate () (local (defthm l (coerce x 'list))))"
        self.assertEqual(counts(src)["coerce"], 0)

    def test_nested_in_progn_counted(self):
        self.assertEqual(counts("(progn (defun f (x) (coerce x 'list)))")["coerce"], 1)

    def test_define_events_after_marker_not_counted(self):
        src = "(define f ((x)) (g x) /// (defthm l (equal (coerce x 'list) y)))"
        self.assertEqual(counts(src)["coerce"], 0)

    def test_package_prefix_and_case(self):
        self.assertEqual(counts("(defun f (x) (ACL2::COERCE x 'list))")["coerce"], 1)

    def test_generator_not_counted(self):
        self.assertFalse(S.wanted("books/def-span-scan.lisp", False))
        self.assertTrue(S.wanted("books/def-loop.lisp", False))
        self.assertFalse(S.wanted("books/def-span-scan.lisp", True))

    def test_backquoted_template_counts_as_code(self):
        self.assertEqual(counts("(defun f (x) `(g ,(coerce x 'list)))")["coerce"], 1)

    def test_family(self):
        self.assertEqual(S.family("host/native/foo.lisp"), "native")
        self.assertEqual(S.family("books/bp-wire.lisp"), "bp")
        self.assertEqual(S.family("books/wire-scan.lisp"), "wire")
        self.assertEqual(S.family("books/web-page.lisp"), "web")
        self.assertEqual(S.family("books/store-x.lisp"), "store")
        self.assertEqual(S.family("books/owner.lisp"), "other")


class Ratchet(unittest.TestCase):
    def test_growth_fails(self):
        self.assertEqual(S.check(summ(5, 2), summ(4, 2)), ["coerce"])
        self.assertEqual(S.check(summ(4, 3), summ(4, 2)), ["fn-octets-list"])

    def test_equality_passes(self):
        self.assertEqual(S.check(summ(4, 2), summ(4, 2)), [])

    def test_shrink_passes_and_get_unratcheted(self):
        self.assertEqual(S.check(summ(3, 1, get=99), summ(4, 2, get=1)), [])


if __name__ == "__main__":
    unittest.main()
