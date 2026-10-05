"""Consecutive handshake refusals drain iteratively (S091).

A refusal inside fnn-mux-start-waiting-handshake finishes its connection and
fnn-mux-finish ends by calling start-waiting again, so the stack grew by one
nesting per refused socket.  The raw harness tests/native_mux_cleanup_raw.lisp
refuses 300 queued sockets through the real functions and reads the depth.
"""
import pathlib
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
FAILURE = "S091: consecutive handshake refusals nest start-waiting"


class MuxStartWaiting(unittest.TestCase):
    def test_consecutive_refusals_do_not_nest(self):
        run = subprocess.run(["sbcl", "--script", "tests/native_mux_cleanup_raw.lisp"],
                             cwd=ROOT, capture_output=True, text=True, timeout=600)
        if FAILURE in run.stdout + run.stderr:
            self.fail(FAILURE)
        self.assertEqual(run.returncode, 0, run.stdout[-400:] + run.stderr[-400:])


if __name__ == "__main__":
    unittest.main()
