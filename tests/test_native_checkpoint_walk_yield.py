"""The checkpoint walk's yield names its batch by a counter (ledger r72-F9)."""
import shutil
import subprocess
import unittest


class WalkYieldTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_walk_yield_is_a_batch_counter_not_a_list_length(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_checkpoint_walk_yield-mock.lisp"],
            text=True, capture_output=True, timeout=60)
        out = result.stdout + result.stderr
        if "named its position by the accumulated row count" in out:
            self.fail("the walk's yield named its position by the accumulated row count, not the batch ordinal")
        self.assertEqual(result.returncode, 0, out)
        self.assertIn("native_checkpoint_walk_yield passed (2 paths)", result.stdout)
