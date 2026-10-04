"""SCN-1098: actual diagnostic bodies, closed ACL2 outcome vocabulary."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
SBCL = os.environ.get("FN_SBCL") or shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL is required for the actual-source diagnostic fixture")
class OperatorDiagnosticsSourceTests(unittest.TestCase):
    def test_faults_never_print_accepting_heap_or_refused_model_result(self):
        result = subprocess.run(
            [SBCL, "--script", str(ROOT / "tests/native_operator_diagnostics_source-mock.lisp")],
            cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SOURCE OPERATOR DIAGNOSTICS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
