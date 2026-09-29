"""tools/retake_pins.py: emit rewrites asserts; apply moves only digits."""
import contextlib
import io
import os
import subprocess
import sys
from unittest import mock
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
            self.assertIn("FLIP assert 3 (line 5): pinned 'b", done.stdout)
            text = book.read_text()
            self.assertIn("(assert! (equal (+ 1 2) 3))", text)
            self.assertIn("'(:heap 10 \"small\")", text)
            self.assertIn("(assert! (equal (car '(a)) 'b))", text)

    def test_flip_ok_moves_a_flipped_decision_and_names_it_for_the_commit(self):
        sys.path.insert(0, str(ROOT / "tools"))
        import retake_pins
        book_text = ("(assert-event (equal (decide 5) :refused))\n"
                     "(must-fail (assert! (equal 1 2)))\n"
                     "(assert! (equal (f 2) '(1 2)))\n")
        log_text = "PIN 1 NIL :HEAP\n NIL\nPIN 2 NIL (A 3)\n NIL\n"
        with tempfile.TemporaryDirectory() as d:
            book, log = Path(d) / "b.lisp", Path(d) / "log"
            book.write_text(book_text)
            self.assertEqual([n for _, _, n in retake_pins.asserts(book_text)], [1, 2])
            log.write_text(log_text)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(retake_pins.apply(str(book), str(log), "boundary moved"), 0)
            text = book.read_text()
            self.assertIn("(assert-event (equal (decide 5) :heap))", text)
            self.assertIn("(assert! (equal (f 2) '(a 3)))", text)
            self.assertIn("(must-fail (assert! (equal 1 2)))", text)
            said = out.getvalue()
            self.assertIn("assert 1 (line 1): :refused -> :heap: boundary moved", said)

    def test_run_takes_the_boxs_acl2_and_applies(self):
        sys.path.insert(0, str(ROOT / "tools"))
        import retake_pins
        ran = []

        def fake(command, **kwargs):
            ran.append((command, kwargs["input"], kwargs["cwd"]))
            kwargs["stdout"].write("PIN 1 NIL 3\n NIL\n")
            return subprocess.CompletedProcess(command, 0)
        with tempfile.TemporaryDirectory() as d:
            book = Path(d) / "b.lisp"
            book.write_text("(assert! (equal (+ 1 2) 4))\n")
            with mock.patch.dict(os.environ, {}, clear=False), \
                    mock.patch("socket.gethostname", return_value="persvati"), \
                    contextlib.redirect_stdout(io.StringIO()):
                os.environ.pop("FN_ACL2", None)
                os.environ.pop("FN_CERT_CACHE", None)
                self.assertEqual(retake_pins.run(str(book), runner=fake), 0)
            self.assertEqual(book.read_text(), "(assert! (equal (+ 1 2) 3))\n")
            self.assertIn("acl2", ran[0][0][0])
            self.assertNotEqual(ran[0][0][0], "acl2")
            self.assertIn('(ld "b.retake-pins.lisp"', ran[0][1])
            self.assertEqual(Path(ran[0][2]), book.parent.resolve())
            self.assertFalse((Path(d) / "b.retake-pins.lisp").exists())


if __name__ == "__main__":
    unittest.main()
