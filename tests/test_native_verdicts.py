"""tools/native_verdicts.py: a module verdict keyed by exactly its inputs, stored and replayed."""
from __future__ import annotations

import json
import os
import pathlib
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import native_verdicts  # noqa: E402
import test_budget  # noqa: E402

PY = sys.executable


class KeyTests(unittest.TestCase):
    def test_the_key_covers_the_module_its_helpers_the_harness_the_runner_and_the_images(self):
        inputs = native_verdicts.key_inputs("tests.test_native_owner", {"FN_NATIVE_HOST": "build/fn-host"})
        self.assertIn("tests/test_native_owner.py", inputs["files"])
        for fixed in native_verdicts.FIXED_INPUTS:
            self.assertIn(fixed, inputs["files"])
        self.assertIn("FN_NATIVE_HOST", inputs["env"])
        self.assertIn("FN_NATIVE_DEVELOPER_HOST", inputs["env"])  # always keyed, read or not
        self.assertEqual(inputs["env"]["FN_NATIVE_HOST"], {"absent": "build/fn-host"})
        self.assertEqual(inputs["python"][0], sys.executable)

    def test_an_image_is_keyed_by_its_launcher_core_runtime_and_overlay_record(self):
        with tempfile.TemporaryDirectory() as directory:
            base = pathlib.Path(directory)
            runtime = base / "sbcl"
            runtime.write_text("#!/bin/sh\n")
            image = base / "fn-host"
            image.write_text(f'#!/bin/sh\nexec "{runtime}" --core "{image}.core" "$@"\n')
            (base / "fn-host.core").write_bytes(b"core-one")
            first = native_verdicts.image_inputs(str(image))
            self.assertEqual(set(first), {"FN_NATIVE_LAUNCHER_SHA256", "FN_NATIVE_RUNTIME_SHA256",
                                          "FN_NATIVE_CORE_SHA256"})
            (base / "fn-host.core").write_bytes(b"core-two")
            second = native_verdicts.image_inputs(str(image))
            self.assertNotEqual(first["FN_NATIVE_CORE_SHA256"], second["FN_NATIVE_CORE_SHA256"])
            (base / "OVERLAY.json").write_text('{"plan": "abc"}')
            third = native_verdicts.image_inputs(str(image))
            self.assertIn("overlay", third)
            env = {"FN_NATIVE_HOST": str(image)}
            a = native_verdicts.key_of(native_verdicts.key_inputs("tests.test_native_owner", env))
            (base / "OVERLAY.json").write_text('{"plan": "abd"}')
            b = native_verdicts.key_of(native_verdicts.key_inputs("tests.test_native_owner", env))
            self.assertNotEqual(a, b)

    def test_a_read_variable_moves_the_key_and_an_unread_one_does_not(self):
        base = native_verdicts.key_of(native_verdicts.key_inputs("tests.test_native_owner", {}))
        read = native_verdicts.key_of(native_verdicts.key_inputs(
            "tests.test_native_owner", {"FN_RUN_SLOW": "1"}))
        unread = native_verdicts.key_of(native_verdicts.key_inputs(
            "tests.test_native_owner", {"FN_SOMETHING_NOBODY_READS": "1"}))
        self.assertNotEqual(base, read)
        self.assertEqual(base, unread)


MODULE = textwrap.dedent('''
    import os, unittest

    class T(unittest.TestCase):
        def test_ok(self):
            pass

        def test_red(self):
            self.assertEqual(os.environ.get("FN_VERDICT_TEST_FLIP", ""), "green")

        def test_skipped(self):
            self.skipTest("no image")
    ''')


class StoreTests(unittest.TestCase):
    """A module run through tools/test_budget.py --one stores its verdict;
    lookup replays it; a red-cases-only re-run carries the rest forward."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(dir=ROOT / "tests", prefix="verdictcases_")
        self.package = pathlib.Path(self.temporary.name)
        (self.package / "__init__.py").write_text("")
        (self.package / "test_mod.py").write_text(MODULE)
        self.module = f"tests.{self.package.name}.test_mod"
        self.store = tempfile.TemporaryDirectory()
        self.env = dict(os.environ, FN_VERDICT_STORE=self.store.name)
        self.env.pop("FN_VERDICT_TEST_FLIP", None)

    def tearDown(self):
        self.temporary.cleanup()
        self.store.cleanup()

    def one(self, *extra: str, flip: str = "") -> subprocess.CompletedProcess:
        env = dict(self.env)
        if flip:
            env["FN_VERDICT_TEST_FLIP"] = flip
        return subprocess.run([PY, str(ROOT / "tools/test_budget.py"), "--one", self.module, *extra],
                              cwd=ROOT, capture_output=True, text=True, env=env)

    def lookup(self, *extra: str, flip: str = "") -> subprocess.CompletedProcess:
        env = dict(self.env)
        if flip:
            env["FN_VERDICT_TEST_FLIP"] = flip
        return subprocess.run([PY, str(ROOT / "tools/native_verdicts.py"), "lookup", self.module, *extra],
                              cwd=ROOT, capture_output=True, text=True, env=env)

    def test_a_run_stores_its_cases_and_lookup_replays_the_line_with_its_run(self):
        self.assertEqual(self.lookup().returncode, 1)  # nothing stored yet
        done = self.one()
        self.assertEqual(done.returncode, 1)
        self.assertIn("verdict stored", done.stdout)
        found = self.lookup()
        self.assertEqual(found.returncode, 0, found.stderr)
        self.assertIn(f"{self.module}: FAILED (1 failures, 0 errors, 2 ran, 1 skipped) [cached verdict",
                      found.stdout)
        self.assertIn("run on ", found.stdout)
        reds = self.lookup("--red-cases")
        self.assertEqual(reds.stdout.split(), [f"{self.module}.T.test_red"])
        entry = json.loads(self.lookup("--json").stdout)
        self.assertEqual(dict(entry["cases"]), {f"{self.module}.T.test_ok": "ok",
                                                f"{self.module}.T.test_red": "FAIL",
                                                f"{self.module}.T.test_skipped": "skip"})

    def test_a_changed_input_is_a_new_key_and_the_old_verdict_is_not_replayed(self):
        self.one()
        self.assertEqual(self.lookup().returncode, 0)
        self.assertEqual(self.lookup(flip="green").returncode, 1)  # a read variable moved
        (self.package / "test_mod.py").write_text(MODULE + "\n# edited\n")
        self.assertEqual(self.lookup().returncode, 1)

    def test_a_red_cases_only_rerun_carries_the_green_cases_forward(self):
        self.one()
        done = self.one("--cases", f"{self.module}.T.test_red")
        self.assertEqual(done.returncode, 1)
        record = test_budget.read_result(pathlib.Path(self.store.name) / "x") if False else None
        entry = json.loads(self.lookup("--json").stdout)
        self.assertEqual(sorted(entry["carried"]), [f"{self.module}.T.test_ok",
                                                    f"{self.module}.T.test_skipped"])
        self.assertEqual(entry["red"], [f"{self.module}.T.test_red"])
        self.assertIn("2 carried", self.lookup().stdout)
        self.assertIsNone(record)

    def test_an_empty_store_variable_stores_nothing(self):
        env = dict(self.env, FN_VERDICT_STORE="")
        done = subprocess.run([PY, str(ROOT / "tools/test_budget.py"), "--one", self.module],
                              cwd=ROOT, capture_output=True, text=True, env=env)
        self.assertNotIn("verdict stored", done.stdout)
        self.assertEqual(list(pathlib.Path(self.store.name).glob("*")), [])


if __name__ == "__main__":
    unittest.main()
