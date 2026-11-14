"""Exercise actual init/serve dependency preparation without starting a node."""
import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import fn_admin as admin


class TlsStartup(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "tools").mkdir()
        (self.root / "tools/image-node.lsp").write_text("; mocked startup\n")
        self.args = argparse.Namespace(
            image=self.root / "node.img", size_mb=None, size=1048576,
            group=[], storage_fault_model=None, port=119, host=None,
            tls_certificate=None, tls_key=None, tls_handshakes=None,
            tls_window=None, tls_handshake_turns=None, tls_handshake_ms=None,
            peering=False, control_sock=None)

    def test_init_builds_inherited_tls_before_startup(self):
        for variable in ("FN2_TLS_CERTIFICATE", "FN2_TLS_KEY"):
            with self.subTest(variable=variable), mock.patch.dict(os.environ, {variable: "local.pem"}, clear=True), \
                 mock.patch.object(admin, "prepare_native_crypto"), \
                 mock.patch.object(admin.subprocess, "run") as build, \
                 mock.patch.object(admin.subprocess, "call") as start:
                def observe(*args, **kwargs):
                    self.assertEqual(build.call_count, 1)
                    self.assertEqual(build.call_args.args[0][1], str(self.root / "host/build-tls.sh"))
                    self.assertEqual(kwargs["env"][variable], "local.pem")
                    self.assertEqual(kwargs["env"]["FN2_IMAGE_MODE"], "init")
                    return 1
                start.side_effect = observe
                self.assertEqual(admin.cmd_init(self.args, self.root), 1)

    def test_init_build_failure_never_starts_node(self):
        for error in (subprocess.CalledProcessError(1, "build"),
                      subprocess.TimeoutExpired("build", 120)):
            with self.subTest(error=type(error).__name__), \
                 mock.patch.dict(os.environ, {"FN2_TLS_KEY": "local.pem"}, clear=True), \
                 mock.patch.object(admin, "prepare_native_crypto"), \
                 mock.patch.object(admin.subprocess, "run", side_effect=error), \
                 mock.patch.object(admin.subprocess, "call") as start:
                with self.assertRaisesRegex(OSError, "native TLS build failed"):
                    admin.cmd_init(self.args, self.root)
                start.assert_not_called()
                self.assertFalse(self.args.image.exists())

    def test_plain_init_does_not_build_tls(self):
        with mock.patch.dict(os.environ, {}, clear=True), \
             mock.patch.object(admin, "prepare_native_crypto"), \
             mock.patch.object(admin.subprocess, "run") as build, \
             mock.patch.object(admin.subprocess, "call", return_value=1):
            self.assertEqual(admin.cmd_init(self.args, self.root), 1)
            build.assert_not_called()

    def test_serve_builds_cli_tls_before_exec(self):
        self.args.image.touch()
        self.args.tls_certificate = "cli.pem"
        with mock.patch.dict(os.environ, {}, clear=True), \
             mock.patch.object(admin, "prepare_native_crypto"), \
             mock.patch.object(admin.subprocess, "run") as build, \
             mock.patch.object(admin.os, "chdir"), mock.patch.object(admin.os, "dup2"), \
             mock.patch.object(admin.os, "execve") as start:
            def observe(path, argv, env):
                build.assert_called_once()
                self.assertEqual(env["FN2_TLS_CERTIFICATE"], "cli.pem")
                self.assertEqual(env["FN2_IMAGE_MODE"], "serve")
            start.side_effect = observe
            admin.cmd_serve(self.args, self.root)
            start.assert_called_once()


if __name__ == "__main__":
    unittest.main()
