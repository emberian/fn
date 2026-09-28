"""tools/retake_pins.py: emit rewrites asserts; apply moves only digits."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "retake_pins.py"

BOOK = """(in-package "ACL2")
; (assert! (equal 1 2)) in a comment is kept
(assert! (equal (+ 1 2) 4))
(assert! (equal (list :heap (* 2 5) "small") '(:heap 9 "small")))
(assert! (equal (car '(a)) 'b))
(assert! (< 1 2))
"""
LOG = """PIN 1 NIL 3
 NIL
PIN 2 NIL (:HEAP 10 "small")
 NIL
PIN 3 NIL A
 NIL
HOLD 4 T
 NIL
"""


class RetakePinsTests(unittest.TestCase):
    def test_emit_prints_every_assert_and_apply_moves_only_digits(self):
        with tempfile.TemporaryDirectory() as d:
            book, out, log = Path(d) / "b.lisp", Path(d) / "o.lisp", Path(d) / "log"
            book.write_text(BOOK)
            subprocess.run([sys.executable, str(TOOL), "emit", str(book), str(out)], check=True,
                           capture_output=True)
            emitted = out.read_text()
            self.assertIn('"PIN 1 ~x0 ~x1~%"', emitted)
            self.assertIn('"HOLD 4 ~x0~%"', emitted)
            self.assertIn("; (assert! (equal 1 2)) in a comment is kept", emitted)
            log.write_text(LOG)
            done = subprocess.run([sys.executable, str(TOOL), "apply", str(book), str(log)],
                                  capture_output=True, text=True)
            self.assertEqual(done.returncode, 1)          # assert 3 needs a person
            self.assertIn("DECIDE assert 3", done.stdout)
            text = book.read_text()
            self.assertIn("(assert! (equal (+ 1 2) 3))", text)
            self.assertIn("'(:heap 10 \"small\")", text)
            self.assertIn("(assert! (equal (car '(a)) 'b))", text)


if __name__ == "__main__":
    unittest.main()
