"""Run the shipped BP profile parser and its cached selector caller."""
from pathlib import Path
import shutil
import subprocess
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpProfileTests(unittest.TestCase):
    def test_profile_grammar_and_cached_refusal(self):
        sbcl = shutil.which("sbcl")
        if sbcl is None:
            raise unittest.SkipTest("sbcl is not on PATH")
        result = subprocess.run(
            [sbcl, "--noinform", "--script", "tests/native_bp_profile_raw.lisp"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=60, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native BP profile parser passed", output)
