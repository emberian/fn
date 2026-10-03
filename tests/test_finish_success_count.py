"""S118: fn-store-sn-finish compares the successes history by its O(1) count
(fn-sl-count, equal to len of fn-sl-list by books/snoc-list.lisp
fn-sl-count-is-len), not by copying the history twice with fn-sf-successes."""
import pathlib
import unittest

SOURCE = pathlib.Path(__file__).resolve().parents[1] / "host/store-node-host.lisp"


class FinishSuccessCount(unittest.TestCase):
    def test_no_history_copy_in_finish(self):
        text = SOURCE.read_text()
        start = text.index("(defun fn-store-sn-finish ")
        body = text[start:text.index("\n(defun ", start + 1)]
        self.assertNotIn("(len (fn-sf-successes", body)
        self.assertEqual(body.count("fn-sl-count (fn-sf-successes-field"), 2)


if __name__ == "__main__":
    unittest.main()
