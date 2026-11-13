"""Exercise real raw startup plumbing without opening a socket or image."""
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class NativeKillStartupTests(unittest.TestCase):
    def test_disabled_enabled_and_malformed(self):
        for value in (None, "17", "bad"):
            with self.subTest(value=value):
                env = dict(os.environ, FN2_IMAGE="test-only.img",
                           FN2_IMAGE_MODE="init", FN2_IMAGE_BYTES="4096")
                env.pop("FN2_KILL_AT", None)
                env.pop("FN2_TEST_BOUNDARY", None)
                if value is not None:
                    env["FN2_KILL_AT"] = value
                result = subprocess.run(
                    ["sbcl", "--script", "tests/native-kill-startup.lsp"],
                    cwd=ROOT, env=env, capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("Native death injection startup controls passed.", result.stdout)

    def test_actual_boundary_exits_at_selected_count(self):
        env = dict(os.environ, FN2_IMAGE="test-only.img", FN2_IMAGE_MODE="init",
                   FN2_IMAGE_BYTES="4096", FN2_KILL_AT="2", FN2_TEST_BOUNDARY="1")
        result = subprocess.run(
            ["sbcl", "--script", "tests/native-kill-startup.lsp"],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 86, result.stdout + result.stderr)
        self.assertIn("FN2 KILL boundary=2 label=ack", result.stdout)
        self.assertNotIn("Death boundary returned", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
