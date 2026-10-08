"""tools/extract/image_run.py: core.sh accepts an extraction-world phase only on exit status 0 plus this
invocation's completion evidence.  Each tooth is a child behaviour that must be refused."""
import hashlib
import importlib.util
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("image_run", ROOT / "tools/extract/image_run.py")
image_run = importlib.util.module_from_spec(spec)
spec.loader.exec_module(image_run)

NONCE = "0f" * 16


class ImageRunTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)
        (self.out / "defs.lisp").write_bytes(b"(DEFUN F (X) X)\n")
        (self.out / "in.lsp").write_text("")
        self.sha = hashlib.sha256(b"(DEFUN F (X) X)\n").hexdigest()

    def tearDown(self):
        self.tmp.cleanup()

    def child(self, script, timeout=30):
        return image_run.run("VERIFY", str(self.out), NONCE, str(self.out / "in.lsp"), str(self.out / "log"),
                             timeout, str(self.out), ["sh", "-c", script])

    def evidence(self, nonce=NONCE, sha=None):
        return "printf 'XT-VERIFY-DONE %s %s\\n' > %s" % (nonce, sha or self.sha, self.out / "verify.done")

    def test_status_zero_with_this_invocations_evidence_is_accepted(self):
        self.assertEqual(self.child(self.evidence() + "; echo XT-VERIFY-DEFS OK; exit 0"), (True, "ok"))

    def test_ok_line_and_evidence_then_nonzero_exit_is_refused(self):
        ok, reason = self.child("echo XT-VERIFY-DEFS OK; " + self.evidence() + "; exit 1")
        self.assertFalse(ok)
        self.assertIn("status 1", reason)

    def test_ok_line_without_evidence_is_refused(self):
        ok, reason = self.child("echo XT-VERIFY-DEFS OK; exit 0")
        self.assertFalse(ok)
        self.assertIn("no completion evidence", reason)

    def test_stale_evidence_from_an_earlier_run_is_removed_and_refused(self):
        (self.out / "verify.done").write_text("XT-VERIFY-DONE %s %s\n" % (NONCE, self.sha))
        ok, reason = self.child("exit 0")
        self.assertFalse(ok)
        self.assertIn("no completion evidence", reason)

    def test_evidence_of_another_invocation_is_refused(self):
        ok, reason = self.child(self.evidence(nonce="aa" * 16) + "; exit 0")
        self.assertFalse(ok)
        self.assertIn("not this invocation", reason)

    def test_evidence_naming_other_defs_bytes_is_refused(self):
        ok, reason = self.child(self.evidence(sha="0" * 64) + "; exit 0")
        self.assertFalse(ok)
        self.assertIn("not this invocation", reason)

    def test_signal_death_after_ok_is_refused(self):
        ok, reason = self.child("echo XT-VERIFY-DEFS OK; " + self.evidence() + "; kill -9 $$")
        self.assertFalse(ok)
        self.assertIn("status -9", reason)

    def test_timeout_is_refused(self):
        ok, reason = self.child(self.evidence() + "; sleep 5", timeout=1)
        self.assertFalse(ok)
        self.assertIn("timeout", reason)


if __name__ == "__main__":
    unittest.main()
