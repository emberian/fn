"""tools/native_source_check.py: an image-free run tells the truth about each module."""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import native_source_check as nsc                               # noqa: E402


class VerdictTests(unittest.TestCase):
    def test_a_green_module_counts_its_skips(self):
        out = "....ss\n------\nRan 6 tests in 0.1s\n\nOK (skipped=2)\n"
        ok, line = nsc.verdict("tests.test_native_x", 0, out, 1.0)
        self.assertTrue(ok)
        self.assertIn("4 run, 2 NOT RUN", line)

    def test_a_failing_source_check_is_named(self):
        out = ("FAIL: test_calls_keystone (tests.test_native_x.SourceTests.test_calls_keystone)\n"
               "------\nRan 3 tests in 0.1s\n\nFAILED (failures=1)\n")
        ok, line = nsc.verdict("tests.test_native_x", 1, out, 1.0)
        self.assertFalse(ok)
        self.assertIn("SourceTests.test_calls_keystone", line)

    def test_no_result_no_tests_and_a_timeout_are_failures(self):
        self.assertFalse(nsc.verdict("m", 1, "ImportError: no module\n", 0.1)[0])
        ok, line = nsc.verdict("m", 0, "\nRan 0 tests in 0.0s\n\nOK\n", 0.1)
        self.assertFalse(ok)
        self.assertIn("collected no test", line)
        ok, line = nsc.verdict("m", None, "", 181)
        self.assertFalse(ok)
        self.assertIn("timed out", line)

    def test_every_skip_is_ok(self):
        ok, _ = nsc.verdict("m", 0, "ss\nRan 2 tests in 0.0s\n\nOK (skipped=2)\n", 0.1)
        self.assertTrue(ok)


class ImageFreeTests(unittest.TestCase):
    def test_a_skip_at_setup_is_ok_and_names_its_reason(self):
        out = ("setUpClass (tests.test_native_x.T) ... skipped 'developer native image missing: x'\n"
               "\nRan 0 tests in 0.0s\n\nOK (skipped=1)\n")
        ok, line = nsc.verdict("tests.test_native_x", 0, out, 0.1)
        self.assertTrue(ok, line)
        self.assertIn("skipped whole at setup: developer native image missing: x", line)
        # Nothing collected and nothing skipped stays red.
        self.assertFalse(nsc.verdict("m", 0, "\nRan 0 tests in 0.0s\n\nOK\n", 0.1)[0])

    def test_the_scratch_root_has_no_build_and_no_fn_variables(self):
        with tempfile.TemporaryDirectory() as src, tempfile.TemporaryDirectory() as dst:
            src, dst = Path(src), Path(dst)
            for d in ("tests", "tools", "books", "build"):
                (src / d).mkdir()
            (src / "build" / "fn-host").write_text("image")
            (src / "tests" / "test_native_a.py").write_text("")
            (src / "books" / "b.lisp").write_text("")
            root = nsc.image_free_root(src, dst)
            self.assertFalse((root / "build").exists())
            self.assertTrue((root / "tests").is_dir() and not (root / "tests").is_symlink())
            self.assertTrue((root / "books").is_symlink())
            self.assertEqual(nsc.modules(root), ["tests.test_native_a"])
        env = nsc.scrubbed_env({"FN_NATIVE_HOST": "x", "FN_RUN_E2E": "1", "PATH": "/bin"})
        self.assertEqual(sorted(env), ["PATH", "PYTHONDONTWRITEBYTECODE"])

    def test_the_toolchain_sbcl_survives_the_scrub(self):
        # It names the toolchain, not an image (PKT-614: a system SBCL
        # cannot read the host).
        with tempfile.TemporaryDirectory() as tmp:
            sbcl = Path(tmp) / "sbcl" / "bin" / "sbcl"
            sbcl.parent.mkdir(parents=True)
            sbcl.write_text("#!/bin/sh\n")
            sbcl.chmod(0o755)
            launcher = Path(tmp) / "acl2"
            launcher.write_text(f'#!/bin/sh\nexec "{sbcl}" --core x "$@"\n')
            env = nsc.scrubbed_env({"FN_ACL2": str(launcher), "FN_NATIVE_HOST": "x"})
            self.assertEqual(env["FN_SBCL"], str(sbcl))
            self.assertNotIn("FN_ACL2", env)
            self.assertEqual(nsc.scrubbed_env({"FN_SBCL": "/x/sbcl"})["FN_SBCL"], "/x/sbcl")


if __name__ == "__main__":
    unittest.main()
