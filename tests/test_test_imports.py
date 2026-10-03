"""Every test module's `tests.*` imports name a module that exists.

2026-10-03 (coordinator, from RECLAIM-RETENTION): tests/test_native_ion_receipt_
recovery.py imported tests.test_native_ion_workflow, a module that never
reached dev (it lived on codex/sol-ltp-completion), so ION had no live native
coverage and nothing said so: the native module only runs on a box with an
image, where a load failure is one error line among many.  This check needs
no image and runs everywhere: a test module whose import of another tests
module cannot resolve is a failure here, never a silent skip there.
"""
from __future__ import annotations

import ast
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent


def module_exists(dotted: str) -> bool:
    path = ROOT.joinpath(*dotted.split("."))
    return path.with_suffix(".py").is_file() or (path / "__init__.py").is_file()


def unresolved_imports(root: Path = ROOT) -> list[str]:
    missing = []
    for path in sorted((root / "tests").rglob("*.py")):
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"))
        except SyntaxError as error:
            missing.append(f"{path.relative_to(root)}: does not parse: {error}")
            continue
        for node in ast.walk(tree):
            names = []
            if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                names = [node.module]
                # `from tests import foo` names the module tests/foo.py.
                if node.module == "tests":
                    names = [f"tests.{alias.name}" for alias in node.names]
            elif isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            for name in names:
                if name.split(".")[0] == "tests" and not module_exists(name):
                    missing.append(f"{path.relative_to(root)}:{node.lineno}: "
                                   f"imports {name}, which does not exist")
    return missing


class TestImportsTests(unittest.TestCase):
    def test_every_tests_import_resolves(self):
        self.assertEqual(unresolved_imports(), [])

    def test_a_missing_module_is_reported(self):
        import tempfile
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tests").mkdir()
            (root / "tests" / "__init__.py").write_text("")
            (root / "tests" / "test_a.py").write_text(
                "from tests.test_gone import Thing\nfrom tests import native_gone\n")
            found = unresolved_imports(root)
        self.assertEqual(len(found), 2, found)
        self.assertIn("tests.test_gone", found[0])


if __name__ == "__main__":
    unittest.main()
