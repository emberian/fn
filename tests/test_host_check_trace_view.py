"""DT-4 (observability program): `host_check --trace-view` flags a host file
that lets a decision depend on a trace, passes a clean one, and finds nothing
in today's host/ (lane obs-decision-trace)."""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import host_check  # noqa: E402

BRANCHING = """(in-package "ACL2")
(defun fnn-serve (x)
  (if (fnn-dtrace-enabled-p) (fnn-do-more x) (fnn-do x)))
"""
CLEAN = """(in-package "ACL2")
(defun fnn-serve (x)
  (fnn-trace-reset)
  (fnn-trace-span (:serve :cid 1) (fnn-do x)))
(defun fnn-call-like (name args)
  (fnn-dtrace-around (name args) (fnn-run name args)))
(fnn-operator-register-action :trace #'fnn-trace-execute)
"""


class TraceView(unittest.TestCase):
    def findings(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.lisp"
            path.write_text(text)
            return host_check.trace_view_findings([path])

    def test_a_host_file_that_branches_on_the_trace_is_flagged(self):
        found = self.findings(BRANCHING)
        self.assertTrue(any("fnn-dtrace-enabled-p" in f for f in found), found)

    def test_a_clean_host_file_passes(self):
        self.assertEqual(self.findings(CLEAN), [])

    def test_a_result_that_is_bound_branched_on_or_returned_is_flagged(self):
        for text, word in (
                ("(defun f () (let ((s (fnn-trace-now))) (g s)))", "bound"),
                ("(defun f () (when (fnn-trace-now) (g)))", "branched on"),
                ("(defun f () (cond ((fnn-trace-now) 1) (t 2)))", "branched on"),
                ("(defun f () (and (g) (fnn-trace-now)))", "branched on"),
                ("(defun f () (setq *x* (fnn-dtrace-report)))", "bound"),
                ("(defun f () (g) (fnn-trace-now))", "returned"),
                ("(defun f () (multiple-value-bind (a) (fnn-trace-now) a))", "bound")):
            found = self.findings(text)
            self.assertTrue(any(word in f for f in found), (text, found))

    def test_rows_are_made_only_inside_the_tracing_module(self):
        for name in ("fnn-dtrace-note", "fnn-dtrace-store", "fnn-dtrace-lookup"):
            found = self.findings("(defun f (p) (%s p))" % name)
            self.assertTrue(any(name in f for f in found), (name, found))

    def test_effects_and_arguments_are_allowed(self):
        self.assertEqual(self.findings(
            "(defun f () (fnn-trace-reset) (fnn-dtrace-report) (g (fnn-trace-now)) 1)"), [])

    def test_todays_host_has_no_finding(self):
        result = subprocess.run([sys.executable, "tools/host_check.py", "--trace-view"],
                                cwd=ROOT, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("0 finding(s)", result.stdout)


if __name__ == "__main__":
    unittest.main()
