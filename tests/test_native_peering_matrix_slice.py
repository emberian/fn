"""The selected peering runner must keep hybrid startup inputs and failures visible."""
import json
import io
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import native_peering_matrix_slice as slice_runner


ROOT = Path(__file__).resolve().parent.parent


class NativePeeringMatrixSliceTests(unittest.TestCase):
    def test_hybrid_prefix_reaches_probe_and_startup_failure_names_rows(self):
        base = slice_runner.v0_matrix.V0Matrix

        class FailedProbe(base):
            def probe_native_subject(self):
                self_test.assertEqual(self.native_openssl_prefix, "/pinned/openssl")
                raise slice_runner.v0_matrix.GateError("hybrid provider unavailable")

            def native_peering_suite(self):
                self_test.fail("peering must not run after failed image probe")

        self_test = self
        with tempfile.TemporaryDirectory() as home:
            target = Path(home) / "matrix.json"
            with patch.object(slice_runner.v0_matrix, "V0Matrix", FailedProbe):
                with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                    rc = slice_runner.main([
                        "--worktree", str(ROOT), "--image", "/unused/fn-host",
                        "--runtime", "/unused/sbcl", "--native-openssl-prefix",
                        "/pinned/openssl", "--source", "source-commit=test",
                        "--commit", "a" * 40, "--json", str(target),
                    ])
            self.assertEqual(rc, 2)
            rows = json.loads(target.read_text())["rows"]
            selected = [row for row in rows
                        if row["feature"] in ("F-TRANSIT", "F-FEED")]
            self.assertTrue(selected)
            self.assertTrue(all("hybrid provider unavailable" in row["blocker"]
                                for row in selected))


if __name__ == "__main__":
    unittest.main()
