"""The primitive gate must use the selected artifact, without recompilation."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import deflate_primitive_check as check
import fn_admin


class PrimitiveSelection(unittest.TestCase):
    def test_explicit_artifact_never_builds(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library = root / "selected library.so"
            library.write_bytes(b"selected")
            with mock.patch.object(fn_admin, "prepare_native_deflate", side_effect=AssertionError("unexpected build")):
                self.assertEqual(check.selected_library(root, library, root / "unused"), library.resolve())
                with self.assertRaises(FileNotFoundError):
                    check.selected_library(root, root / "missing", root / "unused")

    def test_default_uses_shared_preparation_recipe(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with mock.patch.object(fn_admin, "prepare_native_deflate") as prepare:
                selected = check.selected_library(root, None, root)
                prepare.assert_called_once_with(root, selected)


if __name__ == "__main__":
    unittest.main()
