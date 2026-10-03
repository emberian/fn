"""S102/S143: the control socket is never wider than 0600, not even between
bind and chmod -- fnn-control-listen binds under a 0077 umask."""
import pathlib
import re
import unittest

SOURCE = pathlib.Path(__file__).resolve().parents[1] / "host/native/control-transport.lisp"


class ControlListenUmask(unittest.TestCase):
    def test_bind_happens_under_restrictive_umask(self):
        text = SOURCE.read_text()
        start = text.index("(defun fnn-control-listen")
        body = text[start:text.index("\n(defun ", start + 1)]
        umask = re.search(r"sb-posix:umask\s+#o77\b|sb-posix:umask\s+#o077\b", body)
        bind = body.index("socket-bind")
        self.assertIsNotNone(umask, "fnn-control-listen sets no restrictive umask")
        self.assertLess(umask.start(), bind, "umask must be set before the bind")
        self.assertIn("unwind-protect", body[:bind], "the old umask must be restored")


if __name__ == "__main__":
    unittest.main()
