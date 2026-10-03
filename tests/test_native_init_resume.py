"""STO-10005 matching developer-image consumer for resumable init."""
from pathlib import Path
import unittest
from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, EXIT_FAULT, environment, native_image, requires,
    run, scratch)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(DEVELOPER)
class NativeInitResumeTests(unittest.TestCase):
    def setUp(self):
        self.base = scratch(self, "fn-init-resume-")
        self.store = self.base / "store"
        made = self.invoke("--profile", "development", "fn.test")
        self.assertEqual(made.returncode, EXIT_OK, made.stdout + made.stderr)

    def invoke(self, *words):
        return run([DEVELOPER, "--fn", "store", self.store, "init", *words],
                   timeout=60, env=environment({}))

    def snapshot(self):
        return {str(p.relative_to(self.store)): p.read_bytes()
                for p in self.store.rglob("*") if p.is_file()}

    def assert_unchanged_failure(self, words, code, reason):
        before = self.snapshot()
        result = self.invoke(*words)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        self.assertIn(reason, result.stdout + result.stderr)
        self.assertNotIn(b"initialized", result.stdout)
        self.assertEqual(self.snapshot(), before)

    def test_profile_mismatch_refuses_before_resume_publication(self):
        self.assert_unchanged_failure(("--profile", "scale", "fn.test"),
                                      EXIT_REFUSED, b"profile-mismatch")

    def test_initial_group_mismatch_refuses_before_resume_publication(self):
        self.assert_unchanged_failure(("--profile", "development", "fn.other"),
                                      EXIT_REFUSED, b"initial-groups-mismatch")

    def test_matching_intent_resumes_and_keeps_initial_record(self):
        record = self.store / "config" / "00000001.cfg"
        before = record.read_bytes()
        result = self.invoke("--profile", "development", "fn.test")
        self.assertEqual(result.returncode, EXIT_OK, result.stdout + result.stderr)
        self.assertIn(b"initialized", result.stdout)
        self.assertEqual(record.read_bytes(), before)

    def test_corrupt_initial_evidence_faults_before_resume_publication(self):
        record = self.store / "config" / "00000001.cfg"
        record.write_bytes(b"invalid configuration record")
        self.assert_unchanged_failure(("--profile", "development", "fn.test"),
                                      EXIT_FAULT, b"fault")


if __name__ == "__main__":
    unittest.main()
