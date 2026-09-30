"""Packaging shape and shell argument safety for the extracted SBCL launcher."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("core_launcher", ROOT / "tools/extract/core_launcher.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class CoreLauncherTests(unittest.TestCase):
    def test_runtime_overrides_and_product_arguments_survive(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = root / "sbcl"
            runtime.write_text('#!/bin/sh\nprintf "%s\\n" "$SBCL_HOME" "$@"\n')
            runtime.chmod(0o755)
            launcher = root / "fn-core"
            launcher.write_text(module.launcher(str(runtime), str(root), str(root / "fn-core.core"),
                                                "32000", "1024KB", "65536"))
            result = subprocess.run(["sh", str(launcher), "--fn", "store", "path with spaces", "status"],
                                    env={"SBCL_USER_ARGS": "--dynamic-space-size 2048"},
                                    capture_output=True, text=True, check=True)
            words = result.stdout.splitlines()
            self.assertEqual(words[0], str(root))
            self.assertEqual(words[-4:], ["--fn", "store", "path with spaces", "status"])
            self.assertIn("(cl-user::xl-toplevel)", words)
            self.assertNotIn("(acl2::sbcl-restart)", words)
            self.assertEqual(words.count("--dynamic-space-size"), 2)
            self.assertLess(words.index("32000"), words.index("2048"))

    def test_frozen_product_fingerprint_resolves_only_the_known_here_prefix(self):
        import sys
        sys.path.insert(0, str(ROOT / "tools/extract"))
        from owner import fingerprint
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "runtime").mkdir()
            (root / "runtime/sbcl").write_bytes(b"runtime")
            (root / "fn-host.core").write_bytes(b"core")
            image = root / "fn-host"
            image.write_text('#!/bin/sh\nexec "$here/runtime/sbcl" --core "$here/fn-host.core" "$@"\n')
            result = fingerprint(image)
            self.assertEqual(set(result["artifacts"]),
                             {str(image), str(root / "runtime/sbcl"), str(root / "fn-host.core")})
            self.assertEqual(result["source_provenance"], "unknown")

    def test_refuses_paths_the_packaging_parser_cannot_relocate(self):
        for bad in ('/tmp/with space', '/tmp/$(touch bad)', '/tmp/a"b', '/tmp/a\nb'):
            with self.subTest(path=bad), self.assertRaises(ValueError):
                module.launcher(bad, "/home", "/core", "2048", "1024KB")

    def test_refuses_shell_syntax_in_runtime_options(self):
        with self.assertRaises(ValueError):
            module.launcher("/runtime", "/home", "/core", "2048;touch", "1024KB")
