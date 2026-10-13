"""M22 gate/zero-bound runtime wiring and committed reclaim refresh."""
import pathlib
import shutil
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent

@unittest.skipUnless(shutil.which("sbcl"), "SBCL is not installed")
class MemoryRunSourceTests(unittest.TestCase):
    def test_held_connections_zero_capacity_and_reclaim_refresh(self):
        result = subprocess.run([shutil.which("sbcl"), "--script",
                                 "tests/native_memory_run_source-mock.lisp"],
                                cwd=ROOT, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SOURCE MEMORY RUN PASSED", result.stdout)
        self.assertIn("SOURCE HELD ADMISSION PASSED", result.stdout)
        self.assertIn("SOURCE WEB/PULL TRANSFER PASSED", result.stdout)

    def test_refresh_is_in_the_committed_swap_quantum(self):
        source = (ROOT / "host/native/owner.lisp").read_text()
        start = source.index("(defun fnn-owner-reclaim-pass ")
        end = source.index("\n(defun ", start + 1)
        body = source[start:end]
        subject = "(fnn-owner-core 'fn-owner-memory-reclaim-complete)"
        self.assertEqual(body.count(subject), 1)
        position = body.index(subject)
        self.assertLess(body.index("(fnn-state-checkpoint-install store stage)"), position)
        self.assertLess(body.index("(fnn-owner-history-root-install-held history-candidate)"), position)
        self.assertLess(body.index("(fnn-owner-reclaim-barriers store)"), position)
        self.assertLess(position, body.index("(fnn-dev-held-verdicts-dump \"reclaim\")"))
