"""tools/host_defun_check.py: a defstruct's accessors, read as a form.

2026-10-03 (check-lane CL18): the regex ended a defstruct at the next blank
line, so a struct with none under it took the following forms' words as
slots, and host/native/snapshot-producer.lisp "defined" fnn-snapshot-job-and
twice at one line.  A real collision must still be found.
"""
from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import host_defun_check  # noqa: E402

TEXT = '''(in-package "ACL2")
(defstruct (fnn-job (:constructor %make-fnn-job))
  service ; a comment, and that
  (lock (sb-thread:make-mutex :name "job lock"))
  "not a slot"
  (phase :source))
(defun fnn-other (x) (and x that))
(defstruct (fnn-row (:conc-name fnn-r-)) a b)
'''


class DefstructTests(unittest.TestCase):
    def names(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "x.lisp"
            path.write_text(text)
            return sorted(n for n, _, _ in host_defun_check.definitions(path))

    def test_slots_are_the_forms_elements_only(self):
        self.assertEqual(self.names(TEXT), ["fnn-job-lock", "fnn-job-phase", "fnn-job-service",
                                            "fnn-other", "fnn-r-a", "fnn-r-b"])

    def test_a_real_collision_is_found(self):
        with tempfile.TemporaryDirectory() as directory:
            a, b = Path(directory) / "a.lisp", Path(directory) / "b.lisp"
            a.write_text(TEXT)
            b.write_text("(defun fnn-job-phase (j) j)\n")
            self.assertEqual(host_defun_check.main([str(a), str(b)]), 1)

    def test_the_host_is_clean(self):
        from unittest import mock
        with mock.patch.object(sys, "argv", ["host_defun_check.py"]):
            self.assertEqual(host_defun_check.main(), 0)


if __name__ == "__main__":
    unittest.main()
