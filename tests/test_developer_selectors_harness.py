"""The control fixture must see classification/admission mutations, not mask them."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
HARNESS = ROOT / "tests/native_developer_selectors_raw.lisp"


class DeveloperSelectorsHarnessTests(unittest.TestCase):
    def run_harness(self, mutation=None):
        sbcl = shutil.which("sbcl")
        if not sbcl:
            self.skipTest("no SBCL runtime on PATH")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").symlink_to(ROOT / "books", target_is_directory=True)
            shutil.copytree(ROOT / "host", root / "host")
            if mutation:
                before, after = mutation
                control = root / "host/native/control.lisp"
                text = control.read_text()
                self.assertEqual(text.count(before), 1)
                control.write_text(text.replace(before, after))
            r = subprocess.run([sbcl, "--noinform", "--script", str(HARNESS)], cwd=root,
                               capture_output=True, text=True, timeout=30)
            return r.returncode, r.stdout + r.stderr

    def test_recorded_classification_preserves_real_reply_and_stop(self):
        code, output = self.run_harness()
        self.assertEqual(code, 0, output)
        self.assertIn("native developer selectors passed", output)

    def test_unclassified_handler_guard_removal_is_seen(self):
        code, output = self.run_harness((
            "((and handler *fnn-hybrid-control-handler*", "((and *fnn-hybrid-control-handler*"))
        self.assertNotEqual(code, 0)
        self.assertTrue("FAIL: unclassified frame never reaches the handler chain" in output,
                        "classifier mutation must fail its named classification check")

    def test_mutating_handler_admission_removal_is_seen(self):
        code, output = self.run_harness((("(eq handler :store)", "nil")))
        self.assertNotEqual(code, 0)
        self.assertIn("FAIL: mutation shed happens before the handler chain", output)


if __name__ == "__main__":
    unittest.main()
