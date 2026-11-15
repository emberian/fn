"""Atomic selected-artifact startup controls; no compiler/node is launched."""
import contextlib
import hashlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import fn_admin as admin


class DeflateStartup(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        (self.root / "host").mkdir()
        self.source = self.root / "host/fn2-deflate.c"
        self.source.write_text("selected source")
        (self.root / "host/build-deflate.sh").write_text("selected recipe")
        self.output = self.root / "custom artifacts/carrier.so"
        self.output.parent.mkdir()
        self.output.write_bytes(b"prior valid library")

    def compiler(self, argv, **kwargs):
        self.assertEqual(argv[0], "sh")
        recipe = Path(argv[1])
        self.assertNotEqual(recipe, self.root / "host/build-deflate.sh")
        self.assertEqual(recipe.name, "build-deflate.sh")
        self.assertEqual(recipe.read_text(), "selected recipe")
        self.assertEqual((recipe.parent / "fn2-deflate.c").read_text(), "selected source")
        self.assertEqual(kwargs, dict(cwd=self.root, check=True, timeout=120))
        self.assertNotEqual(Path(argv[2]), self.output)
        self.assertEqual(self.output.read_bytes(), b"prior valid library")
        Path(argv[2]).write_bytes(b"fresh library")

    def test_exact_custom_path_atomically_replaced_with_current_receipt(self):
        with mock.patch.object(admin.subprocess, "run", side_effect=self.compiler):
            receipt = admin.prepare_native_deflate(self.root, Path("custom artifacts/carrier.so"))
        self.assertEqual(self.output.read_bytes(), b"fresh library")
        self.assertEqual(receipt["path"], str(self.output))
        self.assertEqual(receipt["source_sha256"], hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.assertEqual(receipt["library_sha256"], hashlib.sha256(b"fresh library").hexdigest())

    def test_selected_basename_cannot_collide_with_build_workspace(self):
        for name in ("inputs", "artifacts"):
            with self.subTest(name=name):
                self.output = self.root / "custom artifacts" / name
                self.output.write_bytes(b"prior valid library")
                with mock.patch.object(admin.subprocess, "run", side_effect=self.compiler):
                    receipt = admin.prepare_native_deflate(self.root, self.output)
                self.assertEqual(self.output.read_bytes(), b"fresh library")
                self.assertEqual(receipt["path"], str(self.output))

    def test_failed_or_timed_out_build_keeps_selected_artifact(self):
        for error in (subprocess.CalledProcessError(1, "compiler"), subprocess.TimeoutExpired("compiler", 120)):
            with self.subTest(error=type(error).__name__), \
                 mock.patch.object(admin.subprocess, "run", side_effect=error):
                with self.assertRaisesRegex(OSError, "was not replaced"):
                    admin.prepare_native_deflate(self.root, self.output)
                self.assertEqual(self.output.read_bytes(), b"prior valid library")

    def test_changed_source_or_empty_output_refused(self):
        def changing(argv, **kwargs):
            self.compiler(argv, **kwargs)
            self.source.write_text("different source")
        with mock.patch.object(admin.subprocess, "run", side_effect=changing):
            with self.assertRaisesRegex(OSError, "source changed"):
                admin.prepare_native_deflate(self.root, self.output)
        def empty(argv, **kwargs):
            Path(argv[2]).write_bytes(b"")
        with mock.patch.object(admin.subprocess, "run", side_effect=empty):
            with self.assertRaisesRegex(OSError, "empty library"):
                admin.prepare_native_deflate(self.root, self.output)
        self.assertEqual(self.output.read_bytes(), b"prior valid library")

    def test_private_entry_has_only_artifact_argument(self):
        with mock.patch.object(admin, "prepare_native_deflate", return_value={"path": str(self.output)}) as prepare, \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(admin.main(["__prepare-native-deflate", str(self.output)], self.root), 0)
            prepare.assert_called_once_with(self.root, self.output)
        with mock.patch.object(admin, "prepare_native_deflate") as prepare, contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(admin.main(["__prepare-native-deflate"], self.root), admin.EXIT_ERROR)
            self.assertEqual(admin.main(["__prepare-native-deflate", "path", "profile"], self.root), admin.EXIT_ERROR)
            prepare.assert_not_called()

    def test_compiler_reads_snapshot_even_if_live_input_changes_and_returns(self):
        def changing(argv, **kwargs):
            self.source.write_text("transient live source")
            self.compiler(argv, **kwargs)
            self.source.write_text("selected source")
        with mock.patch.object(admin.subprocess, "run", side_effect=changing):
            receipt = admin.prepare_native_deflate(self.root, self.output)
        self.assertEqual(receipt["source_sha256"], hashlib.sha256(b"selected source").hexdigest())
        self.assertEqual(self.output.read_bytes(), b"fresh library")


if __name__ == "__main__":
    unittest.main()
