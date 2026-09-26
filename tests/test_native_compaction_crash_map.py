"""Source-level map from native reclaim boundaries to byte crash transitions."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parent.parent


class NativeCompactionCrashMapTests(unittest.TestCase):
    def test_saved_image_loads_reclaim_plan_definition(self):
        build = (ROOT / "host/native/build.lisp").read_text()
        self.assertIn('(include-book "books/byte-store-compaction-correspondence")',
                      build)

    def test_actual_reclaim_calls_logical_plan_subject(self):
        source = (ROOT / "host/native/checkpoint.lisp").read_text()
        start = source.index("(defun fnn-pack-prefix-reclaim")
        end = source.index("\n(defun fnn-pack-selected-raw-and-coverage", start)
        body = source[start:end]
        self.assertIn("(fnn-core 'fn-bs-pack-reclaim-plan observed limit lower)", body)
        self.assertIn('(fnn-checkpoint-test-stop "pack-reclaim-unlink")', body)
        self.assertIn('(fnn-checkpoint-test-stop "pack-reclaim-directory")', body)

    def test_each_native_cut_is_a_model_program_cut(self):
        source = (ROOT / "books/byte-store-compaction-correspondence.lisp").read_text()
        start = source.index("(defun fn-bs-pack-reclaim-steps")
        end = source.index("\n(defun fn-bs-pack-reclaim-program", start)
        cuts = re.findall(r'\(list :cut "([^"]+)"\)', source[start:end])
        self.assertEqual(cuts, ["pack-reclaim-unlink", "pack-reclaim-directory"])

    def test_recovery_calls_exact_observation_subject(self):
        source = (ROOT / "host/native/checkpoint.lisp").read_text()
        start = source.index("(defun fnn-pack-recover-records")
        end = source.index("\n(defun ", start + 1)
        body = source[start:end]
        self.assertIn("(fnn-core 'fn-store-checkpoint-chain-observe", body)


if __name__ == "__main__":
    unittest.main()
