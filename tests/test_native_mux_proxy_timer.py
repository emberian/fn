"""A :proxy connection asks ACL2 about its deadline only once due (S088).

fnn-mux-timers called the owner-serialized fnn-mux-proxy-expired for every
:proxy connection on every pass; the :handshake and :tls-queued branches gate
on (due hs-deadline).  The raw harness tests/native_mux_cleanup_raw.lisp runs
the real fnn-mux-timers and counts the calls.
"""
import pathlib
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
FAILURE = "S088: an undue :proxy deadline asked ACL2 anyway"


class MuxProxyTimer(unittest.TestCase):
    def test_undue_proxy_deadline_does_not_ask_acl2(self):
        run = subprocess.run(["sbcl", "--script", "tests/native_mux_cleanup_raw.lisp"],
                             cwd=ROOT, capture_output=True, text=True, timeout=600)
        if FAILURE in run.stdout + run.stderr:
            self.fail(FAILURE)
        self.assertEqual(run.returncode, 0, run.stdout[-400:] + run.stderr[-400:])


if __name__ == "__main__":
    unittest.main()
