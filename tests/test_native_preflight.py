"""Receipts cannot turn changed, failed or incomplete checks into success."""
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tools import native_preflight as preflight


class NativePreflightTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "source"
        self.root.mkdir()
        (self.root / "subject.lisp").write_text("old bytes")
        self.cache = self.base / "cache"
        self.calls = []

    def runner(self, command, **kwargs):
        self.calls.append((command, kwargs["cwd"]))
        return subprocess.CompletedProcess(command, 0, stdout=b"checked\n")

    def run_gate(self, root=None, runner=None, **kwargs):
        output = io.BytesIO()
        code = preflight.run_gate(root or self.root, self.cache, "interfaces-check",
                                  runner=runner or self.runner, output=output, **kwargs)
        return code, output.getvalue()

    def test_identical_bytes_reuse_across_scratch_roots(self):
        self.assertEqual(self.run_gate()[0], 0)
        other = self.base / "other"
        shutil.copytree(self.root, other)
        code, output = self.run_gate(other)
        self.assertEqual(code, 0)
        self.assertIn(b"REUSED", output)
        self.assertEqual(len(self.calls), 1)

    def test_changed_added_deleted_source_and_tools_each_invalidate(self):
        self.run_gate()
        (self.root / "subject.lisp").write_text("new bytes")
        self.run_gate()
        (self.root / "untracked.lisp").write_text("new declaration")
        self.run_gate()
        (self.root / "untracked.lisp").unlink()
        (self.root / "subject.lisp").unlink()
        self.run_gate()
        (self.root / "tools").mkdir()
        (self.root / "tools/check.py").write_text("changed scanner")
        self.run_gate()
        self.assertEqual(len(self.calls), 5)

    def test_evidence_index_is_input_but_build_artifacts_are_not(self):
        self.run_gate()
        (self.root / "build").mkdir()
        (self.root / "build/image").write_text("unrelated image")
        self.assertIn(b"REUSED", self.run_gate()[1])
        (self.root / "planning").mkdir()
        (self.root / "planning/evidence-index.tsv").write_text("new index")
        self.run_gate()
        self.assertEqual(len(self.calls), 2)

    def test_failure_is_never_filed(self):
        def failed(command, **kwargs):
            self.calls.append(command)
            return subprocess.CompletedProcess(command, 7, stdout=b"bad declaration")
        self.assertEqual(self.run_gate(runner=failed)[0], 7)
        self.assertEqual(self.run_gate()[0], 0)
        self.assertEqual(len(self.calls), 2)

    def test_source_changes_during_check_refuse_to_file_success(self):
        def moving(command, **kwargs):
            (self.root / "subject.lisp").write_text("changed during check")
            return self.runner(command, **kwargs)
        self.assertEqual(self.run_gate(runner=moving)[0], 2)
        self.assertEqual(list(self.cache.glob("*.json")), [])

    def test_bad_receipt_or_log_is_rechecked(self):
        self.run_gate()
        log = next(self.cache.glob("*.log"))
        log.write_bytes(b"tampered")
        self.assertNotIn(b"REUSED", self.run_gate()[1])
        receipt = next(self.cache.glob("*.json"))
        data = json.loads(receipt.read_text())
        data["exit_code"] = 1
        receipt.write_text(json.dumps(data))
        self.assertNotIn(b"REUSED", self.run_gate()[1])
        self.assertEqual(len(self.calls), 3)

    def test_external_symlink_input_runs_without_reuse(self):
        outside = self.base / "outside.lisp"
        outside.write_text("external input")
        (self.root / "link.lisp").symlink_to(outside)
        self.assertEqual(self.run_gate()[0], 0)
        self.assertEqual(self.run_gate()[0], 0)
        self.assertEqual(len(self.calls), 2)
        self.assertFalse(self.cache.exists())

    def test_broken_or_looping_symlink_runs_without_reuse(self):
        link = self.root / "link.lisp"
        for target in ("absent.lisp", "link.lisp"):
            link.symlink_to(target)
            self.assertEqual(self.run_gate()[0], 0)
            self.assertFalse(self.cache.exists())
            link.unlink()

    def test_checker_uses_isolated_python_without_site_hooks(self):
        self.run_gate()
        self.assertEqual(self.calls[0][0][1:3], ["-I", "-S"])

    def test_internal_file_symlink_is_hashed_and_retargeting_invalidates(self):
        link = self.root / "link.lisp"
        link.symlink_to("subject.lisp")
        self.run_gate()
        self.assertIn(b"REUSED", self.run_gate()[1])
        (self.root / "other.lisp").write_text("other bytes")
        link.unlink()
        link.symlink_to("other.lisp")
        self.assertNotIn(b"REUSED", self.run_gate()[1])
        self.assertEqual(len(self.calls), 2)

    def test_changed_python_import_environment_invalidates(self):
        self.run_gate()
        with patch.dict("os.environ", {"PYTHONPATH": "/a/different/import/path"}):
            self.assertNotIn(b"REUSED", self.run_gate()[1])
        self.assertEqual(len(self.calls), 2)

    def test_force_runs_and_refiles(self):
        self.run_gate()
        self.assertNotIn(b"REUSED", self.run_gate(force=True)[1])
        self.assertEqual(len(self.calls), 2)


if __name__ == "__main__":
    unittest.main()
