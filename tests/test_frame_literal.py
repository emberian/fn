"""tools/frame_literal.py: the form it sends and the literal it prints (no ACL2)."""
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import frame_literal as fl                                    # noqa: E402


class FormTests(unittest.TestCase):
    def test_values_become_the_encoders_list(self):
        self.assertEqual(fl.value_form(["*fn-bs-meta-format-8*", "4096", "(expt 2 32)"]),
                         "(fn-spo-saved-frame (list *fn-bs-meta-format-8* 4096 (expt 2 32)))")

    def test_unsafe_or_unbalanced_values_are_refused(self):
        for bad in ["#.(sb-ext:quit)", "(list 1", "1)", "1 2", "x ; c", ""]:
            with self.assertRaises(fl.LiteralError, msg=bad):
                fl.value_form([bad])
        with self.assertRaises(fl.LiteralError):
            fl.value_form(["1"], encoder="(evil)")

    def test_the_sent_form_prints_between_markers(self):
        self.assertEqual(fl.print_form("(f x)"),
                         '(cw "FNLIT[~*0]FNLIT~%" (list "" "~x*" "~x* " "~x* " (f x)))')


class ParseTests(unittest.TestCase):
    def test_wrapped_output_is_read(self):
        out = "NIL\nACL2 !>FNLIT[70 78 83\n77 1 1]FNLIT\nNIL\n"
        self.assertEqual(fl.parse_octets(out), [70, 78, 83, 77, 1, 1])

    def test_no_marker_or_a_non_octet_is_an_error(self):
        with self.assertRaises(fl.LiteralError):
            fl.parse_octets("ACL2 Error in ( CW ...)")
        with self.assertRaises(fl.LiteralError):
            fl.parse_octets("FNLIT[1 256]FNLIT")
        with self.assertRaises(fl.LiteralError):
            fl.parse_octets("FNLIT[1 :X]FNLIT")

    def test_leading_forms_stop_at_the_first_event(self):
        listing = "#1 in-package\n#2 include-book\n#3 include-book\n#4 defconst *x*\n#5 include-book\n"
        self.assertEqual(fl.leading_forms(listing), "#3")


class LayoutTests(unittest.TestCase):
    def test_the_test_books_layout(self):
        text = fl.lisp_literal(list(range(20)), "*x-octets*")
        self.assertEqual(text, "(defconst *x-octets*\n  '(\n"
                         "    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15\n"
                         "    16 17 18 19))\n\n"
                         "(assert-event (equal (len *x-octets*) 20))")

    def test_a_committed_literal_round_trips(self):
        """The layout is the one tests/acl2/store-profile-open-tests.lisp uses."""
        book = (ROOT / "tests/acl2/store-profile-open-tests.lisp").read_text()
        match = re.search(r"\(defconst \*spot-window-octets\*\n  '\(\n(.*?)\)\)", book, re.S)
        octets = [int(w) for w in match.group(1).split()]
        self.assertIn(fl.lisp_literal(octets, "*spot-window-octets*").split("\n\n")[0], book)

    def test_python_bytes(self):
        self.assertEqual(fl.python_literal([1, 2]), "bytes([\n    1, 2,\n])  # 2 octets")


if __name__ == "__main__":
    unittest.main()
