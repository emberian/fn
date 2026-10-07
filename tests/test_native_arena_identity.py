"""Owner start-time arena identity (CONVERGE-1 red 1): host/native/owner.lisp
fnn-owner-arena-identity-check refuses, by name, when the owner's compiled ACL2
path and the host read different arena counts.

The raw function is cut out of the source and run in SBCL against a stubbed
dispatcher, red when the two counts disagree and green when they agree; the
startup path is asserted to run it before any hook."""
import re
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OWNER = ROOT / "host/native/owner.lisp"


def form(text: str, name: str) -> str:
    start = text.index("(defun %s " % name)
    depth, i, in_str, esc = 0, start, False, False
    while True:
        c = text[i]
        if in_str:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
        elif c == '"':
            in_str = True
        elif c == ";":
            i = text.index("\n", i)
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
        i += 1


def run(owner_count: int, host_count: int) -> tuple[int, str]:
    source = OWNER.read_text()
    program = """
(define-condition fnn-store-error (error) ((message :initarg :message :reader m)))
(defun fnn-refuse (control &rest args)
  (error 'fnn-store-error :message (apply #'format nil control args)))
(defun fnn-live-arena () :arena)
(defun fnn-call (name &rest args)
  (declare (ignore args))
  (ecase name (fn-owner-arena-count (list %d)) (fn-arena-count (list %d))))
%s
(handler-case (progn (fnn-owner-arena-identity-check) (format t "ACCEPTED~%%"))
  (fnn-store-error (c) (format t "REFUSED ~a~%%" (m c))))
""" % (owner_count, host_count, form(source, "fnn-owner-arena-identity-check"))
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "t.lisp"
        path.write_text(program)
        r = subprocess.run(["sbcl", "--script", str(path)], capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


@unittest.skipUnless(shutil.which("sbcl"), "sbcl not installed")
class ArenaIdentity(unittest.TestCase):
    def test_red_when_the_counts_disagree(self):
        rc, out = run(0, 1)
        self.assertEqual(rc, 0, out)
        self.assertIn("REFUSED owner startup refused: arena identity", out)
        self.assertIn("count 0", out)

    def test_green_when_they_agree(self):
        rc, out = run(1, 1)
        self.assertEqual(rc, 0, out)
        self.assertIn("ACCEPTED", out)


class Wiring(unittest.TestCase):
    def test_startup_runs_the_check_before_any_hook(self):
        body = form(OWNER.read_text(), "fnn-owner-run-startup-hooks")
        self.assertLess(body.index("fnn-owner-arena-identity-check"), body.index("dolist"))

    def test_the_owner_entry_exists_in_the_host_book(self):
        text = (ROOT / "host/owner-host.lisp").read_text()
        self.assertRegex(text, r"\(defun fn-owner-arena-count \(fn-arena\)")


if __name__ == "__main__":
    unittest.main()
