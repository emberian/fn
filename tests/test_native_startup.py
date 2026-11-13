"""A failed native build must not start ACL2 or create node state."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("fn_admin", ROOT / "tools/fn_admin.py")
admin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(admin)


class NativeStartupTests(unittest.TestCase):
    def test_init_build_failure_leaves_no_image(self):
        with tempfile.TemporaryDirectory() as directory:
            image = Path(directory) / "node.img"
            with patch.object(admin.subprocess, "run", side_effect=subprocess.CalledProcessError(1, "cc")), \
                 patch.object(admin.subprocess, "call") as launch:
                self.assertEqual(admin.main(["init", str(image)], root=ROOT), 2)
                launch.assert_not_called()
                self.assertFalse(image.exists())
                self.assertEqual(list(Path(directory).iterdir()), [])

    def test_serve_build_timeout_preserves_image_and_socket_state(self):
        with tempfile.TemporaryDirectory() as directory:
            image = Path(directory) / "node.img"
            image.write_bytes(b"existing-store")
            sock = Path(directory) / "control.sock"
            with patch.object(admin.subprocess, "run", side_effect=subprocess.TimeoutExpired("cc", 120)), \
                 patch.object(admin.os, "execve") as launch:
                self.assertEqual(admin.main(["serve", str(image), "--control-sock", str(sock)], root=ROOT), 2)
                launch.assert_not_called()
                self.assertEqual(image.read_bytes(), b"existing-store")
                self.assertEqual(list(Path(directory).iterdir()), [image])


if __name__ == "__main__":
    unittest.main()
