"""A refused state checkpoint gives the served octet buffer back (sweep S071)."""
import shutil
import subprocess
import unittest


class LoadReleaseTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_refused_checkpoint_gives_the_buffer_back(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_checkpoint_load_release-mock.lisp"],
            text=True, capture_output=True, timeout=60)
        out = result.stdout + result.stderr
        if "left a file-sized array" in out:
            self.fail("a refused state checkpoint left a file-sized array in the served octet buffer")
        self.assertEqual(result.returncode, 0, out)
        self.assertIn("native_checkpoint_load_release passed (5 paths)", result.stdout)
