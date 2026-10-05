"""RL-02: a publication that ended before its NEXT existed settles its slot.

Runs tests/native_checkpoint_abandon_raw-mock.lisp: the deployed publication
thread, owner entries and ACL2 decisions over stubbed store I/O (a MOCK,
cited by no claim; the native witness is tests/test_native_checkpoint_abandon.py).
"""
import shutil
import subprocess
import unittest


class CheckpointAbandonRawTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_an_abandoned_publication_releases_and_classifies_its_slot(self):
        result = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_checkpoint_abandon_raw-mock.lisp"],
            text=True, capture_output=True, timeout=60)
        failed = [line for line in result.stdout.splitlines()
                  if line.startswith("CHECKPOINT_ABANDON_ASSERTION:")]
        self.assertEqual(failed, [], result.stdout[-2000:] + result.stderr[-2000:])
        self.assertEqual(result.returncode, 0, result.stdout[-2000:] + result.stderr[-2000:])
        self.assertIn("checkpoint abandon passed (5 cases)", result.stdout)


if __name__ == "__main__":
    unittest.main()
