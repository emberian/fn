"""The budget install observes machine and core figures off the owner section."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parent.parent


class NativeMuxBudgetObserveTests(unittest.TestCase):
    def test_observations_precede_the_section(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script", "tests/native_mux_budget_observe_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=60, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output[-4000:])
        self.assertIn("native mux budget observe: PASS", output)
