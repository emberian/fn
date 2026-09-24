"""tools/current_view.py: the host-call locator and the generated view."""

from pathlib import Path
import tempfile
import unittest

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


class ViewTests(unittest.TestCase):
    def test_committed_view_is_current(self) -> None:
        committed = (current_view.ROOT / current_view.OUTPUT).read_text(encoding="utf-8")
        self.assertEqual(current_view.build(), committed)


if __name__ == "__main__":
    unittest.main()
