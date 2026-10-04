"""tools/reds.py: the red set, its selectors, which reds a diff reaches, the delta."""
from __future__ import annotations

import io
import json
import os
import pathlib
import shlex
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_steps  # noqa: E402
import reds  # noqa: E402

PY = sys.executable

NATIVE_LOG = """\
test_a_full_store_defers (tests.test_native_peering.NativePeeringTests.test_a_full_store_defers)
PKT-711 (the stranger rehearsal, 2026-09-27): a receiver whose ... FAIL
test_feed_distribution_filter (tests.test_native_peering.NativePeeringTests.test_feed_distribution_filter)
PRF-237 / SCN-163 (RFC 5537 section 3.6 paragraph 2): with `peer ... ok
test_live_peer_configuration (tests.test_native_peering.NativePeeringTests.test_live_peer_configuration) ... ok
test_cancel_retire (tests.test_native_page_io.PageIOTests.test_cancel_retire) ...
  test_cancel_retire (tests.test_native_page_io.PageIOTests.test_cancel_retire) (completion='success') ... FAIL
  test_cancel_retire (tests.test_native_page_io.PageIOTests.test_cancel_retire) (completion='stale') ... FAIL
test_large_article (tests.test_native_over_pins.NativeOverPinsTests.test_large_article)
The same for an ordinary reply: a 12 MiB ARTICLE (larger than the ... ERROR
Ran 5 tests in 1.0s
FAILED (failures=2, errors=1)
"""


class NativeLogTests(unittest.TestCase):
    def test_red_cases_are_read_from_a_module_log_once_each(self):
        with tempfile.TemporaryDirectory() as directory:
            log = pathlib.Path(directory) / "test-tests.test_native_peering.log"
            log.write_text(NATIVE_LOG)
            found = reds.native_red_cases(log)
        self.assertEqual(found, [
            ("tests.test_native_peering.NativePeeringTests.test_a_full_store_defers", "FAIL"),
            ("tests.test_native_page_io.PageIOTests.test_cancel_retire", "FAIL"),
            ("tests.test_native_over_pins.NativeOverPinsTests.test_large_article", "ERROR")])

    def test_a_module_selector_names_the_module_the_harness_and_the_paths_it_cites(self):
        selector = reds.module_selector("tests.test_native_owner")
        self.assertIn("tests/test_native_owner.py", selector["paths"])
        self.assertIn(reds.HARNESS, selector["paths"])
        self.assertFalse(selector["untraced"])
        for path in selector["paths"]:
            self.assertTrue((ROOT / path).is_file(), path)

    def test_module_logs_from_a_directory_or_files(self):
        with tempfile.TemporaryDirectory() as directory:
            base = pathlib.Path(directory)
            (base / "test-tests.test_native_a.log").write_text("")
            (base / "test-tests.test_native_b.log").write_text("")
            (base / "run.log").write_text("")
            self.assertEqual([p.name for p in reds.module_logs([directory])],
                             ["test-tests.test_native_a.log", "test-tests.test_native_b.log"])
            self.assertEqual(reds.module_logs([str(base / "run.log")]), [base / "run.log"])


class CollectAndAffectTests(unittest.TestCase):
    """A red check step collected from a real `execute` with its scope record,
    then reached (or not) by a diff."""

    def setUp(self):
        (ROOT / "build").mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=ROOT / "build", prefix="test-reds-")
        self.base = pathlib.Path(self.temporary.name)
        self.steps, self.cache, self.data = self.base / "steps", self.base / "cache", self.base / "data"
        self.data.mkdir()
        (self.data / "a").write_text("alpha\n")
        self.red = [PY, "-c", f"print(open({str(self.data / 'a')!r}).read(), 'FAIL: 1 findings'); "
                              "raise SystemExit(1)"]
        self.green = [PY, "-c", "print('fine')"]
        check_steps.begin(self.steps)
        for command in (self.red, self.green):
            check_steps.add(self.steps, command)
        with redirect_stdout(io.StringIO()):
            check_steps.execute(self.steps, 2, True, self.cache)

    def tearDown(self):
        self.temporary.cleanup()

    def rel(self, name: str) -> str:
        return str((self.data / name).relative_to(ROOT))

    def test_the_red_step_is_collected_with_its_traced_inputs(self):
        found = reds.check_step_reds(self.steps, self.cache)
        self.assertEqual(len(found), 1)
        red = found[0]
        self.assertEqual((red["kind"], red["exit"], red["command"]), ("check-step", 1, shlex.join(self.red)))
        self.assertIn("FAIL: 1 findings", red["finding"])
        self.assertIn(self.rel("a"), red["selector"]["paths"])
        self.assertFalse(red["selector"]["untraced"])

    def test_a_diff_reaches_the_red_by_its_inputs_and_nothing_else(self):
        collected = reds.collect(self.steps, self.cache, [], [])
        self.assertEqual(len(collected["reds"]), 1)
        changed = check_steps.Changes({self.rel("a"): "M"})
        self.assertEqual(reds.reached(collected["reds"][0], changed), f"{self.rel('a')} changed")
        self.assertEqual(reds.reached(collected["reds"][0], check_steps.Changes({"docs/x.md": "M"})), "")
        untraced = dict(collected["reds"][0], selector={"paths": [], "listed": [], "git": [],
                                                        "untraced": True, "why": "child process acl2"})
        self.assertTrue(reds.reached(untraced, check_steps.Changes({"books/x.lisp": "M"})))

    def test_a_scoped_run_carries_the_stored_red_and_the_record_is_found_by_command(self):
        """`make check-lane CHECK_CHANGED_SINCE` skips an untouched step; the
        store's red is carried on the row (`last`) and collected as a red,
        and the scope record is found by command even when the step key
        differs (FN_* set by make, unset here)."""
        changed = check_steps.Changes({"docs/x.md": "M"})
        with redirect_stdout(io.StringIO()):
            check_steps.execute(self.steps, 2, True, self.cache, since="HEAD", changed=changed)
        rows = check_steps.read_results(self.steps)
        self.assertTrue(rows[0]["skipped"] and rows[0]["exit"] == 0)
        self.assertEqual(rows[0]["last"]["exit"], 1)
        self.assertIn("last verdict exit 1: FAIL: 1 findings", rows[0]["skipped"])
        self.assertNotIn("last", rows[1])  # the green one carries nothing
        found = reds.check_step_reds(self.steps, self.cache)
        self.assertEqual([r["subject"] for r in found], [rows[0]["step"]])
        self.assertIn(self.rel("a"), found[0]["selector"]["paths"])
        os.environ["FN_REDS_TEST_OTHER_KEY"] = "1"  # a different step key: still found
        try:
            self.assertIn(self.rel("a"), reds.check_step_reds(self.steps, self.cache)[0]["selector"]["paths"])
        finally:
            del os.environ["FN_REDS_TEST_OTHER_KEY"]

    def test_a_replayed_red_names_its_run(self):
        with redirect_stdout(io.StringIO()):
            check_steps.execute(self.steps, 2, True, self.cache)  # replayed from the store
        red = reds.check_step_reds(self.steps, self.cache)[0]
        self.assertTrue(red["source"]["box"] and red["source"]["log"].endswith(".log"))


class OtherKindsTests(unittest.TestCase):
    def test_a_test_case_red_is_reached_by_its_module_or_the_harness(self):
        red = {"kind": "test-case", "subject": "tests.test_native_owner.T.test_x",
               "module": "tests.test_native_owner", "command": "x", "exit": 1, "finding": "FAIL",
               "source": {}, "selector": reds.module_selector("tests.test_native_owner")}
        self.assertEqual(reds.reached(red, check_steps.Changes({reds.HARNESS: "M"})),
                         f"{reds.HARNESS} changed")
        self.assertEqual(reds.reached(red, check_steps.Changes({"docs/x.md": "M"})), "")
        self.assertIn("--overlay . tests.test_native_owner", reds.narrowest(red, "abc123"))
        self.assertIn("--image-set abc123", reds.narrowest(red, "abc123"))

    def test_a_book_red_is_reached_through_its_include_closure(self):
        selector = reds.book_selector("books/acceptance")
        self.assertIn("books/acceptance.lisp", selector["paths"])
        self.assertGreater(len(selector["paths"]), 1)  # it includes something
        red = {"kind": "book", "subject": "books/acceptance", "command": "farm", "exit": 1,
               "finding": "", "source": {}, "selector": selector}
        dependency = next(p for p in selector["paths"] if p != "books/acceptance.lisp")
        self.assertEqual(reds.reached(red, check_steps.Changes({dependency: "M"})), f"{dependency} changed")

    def test_delta_matches_by_kind_and_subject(self):
        def red(kind, subject):
            return {"kind": kind, "subject": subject, "finding": "", "command": "", "exit": 1,
                    "source": {}, "selector": {}}
        old = {"head": "a", "reds": [red("check-step", "x"), red("book", "books/y")]}
        new = {"head": "b", "reds": [red("check-step", "x"), red("test-case", "t.T.z")]}
        appeared, fixed, same = reds.delta(old, new)
        self.assertEqual(([r["subject"] for r in appeared], [r["subject"] for r in fixed], same),
                         (["t.T.z"], ["books/y"], 1))

    def test_the_command_line_round_trips(self):
        with tempfile.TemporaryDirectory() as directory:
            out = pathlib.Path(directory) / "reds.json"
            log = pathlib.Path(directory) / "test-tests.test_native_peering.log"
            log.write_text(NATIVE_LOG)
            text = io.StringIO()
            with redirect_stdout(text):
                code = reds.main(["collect", "--check-steps", directory, "--native", directory,
                                  "--out", str(out)])
            self.assertEqual(code, 0)
            self.assertIn("test-case 3", text.getvalue())
            data = json.loads(out.read_text())
            self.assertEqual([r["module"] for r in data["reds"]],
                             ["tests.test_native_peering", "tests.test_native_page_io",
                              "tests.test_native_over_pins"])
            text = io.StringIO()
            with redirect_stdout(text):
                self.assertEqual(reds.main(["table", "--reds", str(out)]), 0)
            self.assertIn("test-case  tests.test_native_page_io.PageIOTests.test_cancel_retire", text.getvalue())


if __name__ == "__main__":
    unittest.main()
