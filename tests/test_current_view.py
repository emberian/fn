"""tools/current_view.py: the host-call locator and the generated view."""

from pathlib import Path
import tempfile
import json
import unittest
from unittest.mock import patch

from tools import current_view


class HostCallTests(unittest.TestCase):
    def locate(self, text: str, function: str) -> int:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "h.lisp").write_text(text, encoding="utf-8")
            return current_view.host_call(root, function, "h.lisp")

    def test_skips_comments_and_the_definition(self) -> None:
        text = ("; (fn-x a) in a comment\n"
                "(defun fn-x (a) a)\n"
                "(defun caller (a)\n"
                "  (fn-x\n"
                "   a))\n")
        self.assertEqual(self.locate(text, "fn-x"), 4)

    def test_quoted_core_call_counts(self) -> None:
        self.assertEqual(self.locate("(fnn-core 'fn-x a)\n", "fn-x"), 1)

    def test_prefix_is_not_a_call(self) -> None:
        with self.assertRaises(current_view.ViewError):
            self.locate("(fn-x-y a)\n", "fn-x")


class TestedCoordinateTests(unittest.TestCase):
    def render(self, tested):
        return current_view.tested_coordinate(Path("."), {"id": "W9", "tested": tested},
                                             {"qualified": {"qualification": "record",
                                                             "closure_manifest": "closure"}},
                                             None, [])

    def test_null_means_no_image(self):
        qualified, detail = self.render(None)
        self.assertEqual(qualified, "no: no matching image evidence")
        self.assertIn("source proof experiments", detail)
        self.assertNotIn("lane image", detail)

    def test_missing_is_an_error(self):
        with self.assertRaisesRegex(current_view.ViewError, "lacks tested"):
            current_view.tested_coordinate(Path("."), {"id": "W9"}, {}, None, [])

    def test_invalid_coordinates_are_errors(self):
        for tested in [False, "", [], {}, {"image": "qualified"},
                       {"image": "unknown", "profile": "small"},
                       {"record": "r", "source": "", "profile": "small"},
                       {"image": "qualified", "profile": "small", "source": "rev"}]:
            with self.subTest(tested=tested), self.assertRaises(current_view.ViewError):
                self.render(tested)

    @patch.object(current_view, "record_link", return_value="record-link")
    @patch.object(current_view, "carried", return_value=(True, "matching"))
    def test_existing_sidecar_coordinates(self, carried, record_link):
        view = json.loads((current_view.ROOT / current_view.SIDECAR).read_text())
        for capability in view["capabilities"]:
            with self.subTest(capability=capability["id"]):
                current_view.tested_coordinate(Path("."), capability, view["images"], None, [])

    @patch.object(current_view, "record_link", return_value="record-link")
    @patch.object(current_view, "carried", return_value=(True, "matching"))
    def test_historical_coordinates_keep_their_meaning(self, carried, record_link):
        qualified, detail = self.render({"image": "qualified", "profile": "small"})
        self.assertEqual(qualified, "yes: qualified")
        self.assertIn("closure `closure`", detail)
        qualified, detail = self.render({"record": "lab", "source": "revision", "profile": "small"})
        self.assertEqual(qualified, "lab only: `revision`")
        self.assertIn("lane image of `revision`", detail)
        self.assertIn("not a shared qualification", detail)


class PendingBridgeTests(unittest.TestCase):
    def test_matching_old_manifest_cannot_qualify_new_caller(self):
        self.assertEqual(
            current_view.pending_bridge_verdicts(
                "actual wrapper-to-core bridge missing",
                "yes: exact-certified-manifest", "yes: matching-image", "yes: matching-deployment"),
            ("no: caller bridge pending",) * 3)

    def test_empty_pending_reason_is_rejected(self):
        with self.assertRaises(current_view.ViewError):
            current_view.pending_bridge_verdicts("", "yes", "yes", "yes")


class ViewTests(unittest.TestCase):
    def test_committed_view_is_current(self) -> None:
        committed = (current_view.ROOT / current_view.OUTPUT).read_text(encoding="utf-8")
        self.assertEqual(current_view.build(), committed)


if __name__ == "__main__":
    unittest.main()
