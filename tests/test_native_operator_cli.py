#!/usr/bin/env python3
"""Executable boundary checks for the installed native operator image."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def invoke(config, *words):
    return subprocess.run(
        [str(IMAGE), "--fn", "operator", str(config), *words],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=30, check=False,
    )


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeOperatorCliTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-operator-")
        self.root = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def test_help_does_not_open_missing_config(self):
        result = invoke(self.root / "missing.toml", "help", "run")
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout.decode(), "usage: fn operator CONFIG run [--once]\n")

    def test_missing_directory_and_oversize_config_are_usage(self):
        missing = invoke(self.root / "missing.toml", "status")
        directory = self.root / "directory"
        directory.mkdir()
        nonregular = invoke(directory, "status")
        large = self.root / "large.toml"
        large.write_bytes(b"x" * 16385)
        oversize = invoke(large, "status")
        for result in (missing, nonregular, oversize):
            self.assertEqual(result.returncode, 5, result.stderr.decode())

    def test_unreadable_config_is_fault(self):
        config = self.root / "private.toml"
        config.write_text('[store]\npath = "/tmp/fn"\n', encoding="ascii")
        config.chmod(0)
        try:
            result = invoke(config, "status")
        finally:
            config.chmod(0o600)
        self.assertEqual(result.returncode, 4, result.stderr.decode())


if __name__ == "__main__":
    unittest.main()
