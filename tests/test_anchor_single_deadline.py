"""S096: the anchor UDP exchange charges both fd waits against ONE deadline
derived from TIMEOUT, not a full TIMEOUT each."""
import pathlib
import unittest

SOURCE = pathlib.Path(__file__).resolve().parents[1] / "host/native/anchor.lisp"


class AnchorSingleDeadline(unittest.TestCase):
    def test_waits_share_one_deadline(self):
        text = SOURCE.read_text()
        start = text.index("(defun fnn-anchor-udp-exchange")
        body = text[start:text.index("\n(defun ", start + 1)]
        self.assertNotIn(":output timeout)", body)
        self.assertNotIn(":input timeout)", body)
        self.assertIn("get-internal-real-time", body)
        self.assertGreaterEqual(body.count("fnn-anchor-remaining"), 2)


if __name__ == "__main__":
    unittest.main()
