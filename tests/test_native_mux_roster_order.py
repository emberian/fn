"""fnn-mux-finish leaves the clients roster before it closes the socket (S084).

The stop hook (host/native/owner.lisp) shuts down every socket still in
fnn-owner-service-clients; a socket closed first can have its fd reused
underneath that shutdown.  The raw harness tests/native_mux_cleanup_raw.lisp
drives the real fnn-mux-finish and records the roster at fnn-socket-shut.
"""
import pathlib
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
FAILURE = "S084: socket closed while still in the clients roster"


class MuxRosterOrder(unittest.TestCase):
    def test_socket_leaves_the_roster_before_it_is_closed(self):
        run = subprocess.run(["sbcl", "--script", "tests/native_mux_cleanup_raw.lisp"],
                             cwd=ROOT, capture_output=True, text=True, timeout=600)
        if FAILURE in run.stdout + run.stderr:
            self.fail(FAILURE)
        self.assertEqual(run.returncode, 0, run.stdout[-400:] + run.stderr[-400:])


if __name__ == "__main__":
    unittest.main()
