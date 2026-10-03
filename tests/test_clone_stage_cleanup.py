"""S086: `checkpoint clone' learns publication is impossible before it copies,
and a clone refused or faulted removes its stage directory."""
import pathlib
import unittest

SOURCE = pathlib.Path(__file__).resolve().parents[1] / "host/native/checkpoint.lisp"


class CloneStage(unittest.TestCase):
    def body(self):
        text = SOURCE.read_text()
        start = text.index("(defun fnn-checkpoint-command-clone")
        return text[start:text.index("\n(defun", start + 1)]

    def test_platform_checked_before_stage_is_created(self):
        body = self.body()
        check = body.index('#-linux (fnn-refuse "clone publication requires')
        self.assertLess(check, body.index("(fnn-mkdir stage"))

    def test_stage_removed_unless_published_or_indeterminate(self):
        body = self.body()
        self.assertIn("delete-directory", body)
        self.assertIn("unwind-protect", body[body.index("(fnn-mkdir stage") - 400:])


if __name__ == "__main__":
    unittest.main()
