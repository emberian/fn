"""The raw-SBCL loader expands a def-loop form with books/def-loop.lisp's own generator."""
import shutil, subprocess, unittest


class RawDefLoopTests(unittest.TestCase):
    def test_scheduler_peers_put_is_generated_not_copied(self):
        result = subprocess.run(
            [shutil.which("sbcl") or "sbcl", "--noinform", "--script", "tests/raw_def_loop_check.lisp"],
            capture_output=True, text=True, timeout=120)
        self.assertIn("RAW_DEF_LOOP_PASS", result.stdout, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
