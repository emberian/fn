"""Credential admission through actual feed/pull source; no saved-image claim."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CredentialAdmissionTests(unittest.TestCase):
    def run_schedule(self, mode, path, intended=None):
        args = [shutil.which("sbcl") or "sbcl", "--noinform", "--script",
                "tests/native_feed_credential_raw.lisp", str(path), mode]
        try:
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=5)
        except subprocess.TimeoutExpired as error:
            output = error.stdout or b""
            if isinstance(output, bytes):
                output = output.decode()
            if mode == "fifo" and "CREDENTIAL_FIFO_BEGIN" in output:
                self.fail("credential FIFO must refuse without blocking")
            raise
        marker = "CREDENTIAL_ASSERTION:" + intended if intended else None
        if marker and marker in result.stdout:
            self.fail(intended)
        # Loader/import/undefined function failures are infrastructure errors,
        # never the defect assertion identity we designate for base/head.
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, args,
                                                result.stdout, result.stderr)
        self.assertIn("CREDENTIAL_", result.stdout)
        return result

    def profile(self, root, data=b"FNAUTH1\nn\np\n", mode=0o600):
        path = root / "profile"
        path.write_bytes(data)
        path.chmod(mode)
        return path

    def test_fifo_refuses_without_blocking(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fifo"
            os.mkfifo(path, 0o600)
            result = self.run_schedule("fifo", path)
            self.assertIn("CREDENTIAL_FIFO_REFUSED", result.stdout)

    def test_invalid_profile_refuses_before_any_connect(self):
        with tempfile.TemporaryDirectory() as directory:
            path = self.profile(Path(directory), b"invalid profile")
            self.run_schedule("invalid", path, "credential admitted before any TCP connect")

    def test_missing_nonprivate_directory_and_symlink_are_credentials(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = self.profile(root, mode=0o644)
            link = root / "symlink"
            link.symlink_to(target)
            large = root / "large"
            large.write_bytes(b"x" * 2048)
            large.chmod(0o600)
            for path in (target, link, root, root / "missing", large):
                with self.subTest(path=path):
                    self.run_schedule("invalid", path, "credential admitted before any TCP connect")

    def test_valid_acl2_profile_admits_push_and_pull(self):
        with tempfile.TemporaryDirectory() as directory:
            self.run_schedule("good", self.profile(Path(directory)))

    def test_exact_read_and_core_faults_propagate_while_stopping(self):
        with tempfile.TemporaryDirectory() as directory:
            self.run_schedule("faults", self.profile(Path(directory)), "read fault retains exact class")

    def test_cleanup_os_error_preserves_primary_core_fault(self):
        with tempfile.TemporaryDirectory() as directory:
            self.run_schedule("cleanup-fault", self.profile(Path(directory)),
                              "cleanup OS error must preserve primary store fault")
