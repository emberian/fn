"""SCN-1136: actual heap consumers and ACL2 DEFAULT reservation calculation."""
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
SBCL = os.environ.get("FN_SBCL") or shutil.which("sbcl")


@unittest.skipUnless(SBCL, "SBCL is required for the actual-source heap fixture")
class DefaultHeapSourceTests(unittest.TestCase):
    def test_default_backing_root_scope_order_machine_fit_and_status(self):
        result = subprocess.run(
            [SBCL, "--script", str(ROOT / "tests/native_heap_default_source.lisp")],
            cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SOURCE DEFAULT HEAP PASSED", result.stdout)

    def test_peer_policy_real_files_and_native_custody(self):
        for fixture, marker in [
            ("native_peer_policy_source.lisp", "SOURCE PEER POLICY PASSED"),
            ("native_peer_bank_startup_source.lisp", "SOURCE PEER BANK STARTUP PASSED"),
            ("native_owner_terminal_cohorts_source.lisp", "SOURCE OWNER TERMINAL COHORTS PASSED"),
        ]:
            result = subprocess.run([SBCL, "--script", str(ROOT / "tests" / fixture)],
                                    cwd=ROOT, text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(marker, result.stdout)

    def test_status_and_health_preserve_configured_resource_policies(self):
        result = subprocess.run(
            [SBCL, "--script", str(ROOT / "tests/native_heap_diagnostic_policy_source.lisp")],
            cwd=ROOT, text=True, capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("SOURCE NEXT-RUN POLICY DIAGNOSTICS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
