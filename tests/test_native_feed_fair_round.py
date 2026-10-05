"""Actual push worker fairness and pace with kernel output and recorded owner leaves.

The SBCL is the one the image ships on (tests/native_harness.py runtime_sbcl:
FN_SBCL, else the runtime named by the FN_NATIVE_HOST image's wrapper, else
`sbcl` on PATH): a box's system SBCL may be absent or too old for the host
code (PKT-614), and that is not the worker's verdict."""
import os
import sys
from pathlib import Path
import subprocess
import unittest

from tests.native_harness import runtime_sbcl

ROOT = Path(__file__).resolve().parents[1]
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
RUNTIME = runtime_sbcl(IMAGE)


@unittest.skipUnless(RUNTIME, "no SBCL: FN_SBCL, the image's runtime or sbcl on PATH")
class FeedFairRoundTests(unittest.TestCase):
    def run_mode(self, mode, timeout=60):
        sbcl, env = RUNTIME
        return subprocess.run([sbcl, '--noinform', '--script',
                               'tests/native_feed_fair_round_raw.lisp', mode],
                              cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout)

    def assert_mode(self, mode, message=None):
        result = self.run_mode(mode)
        self.assertTrue(result.returncode == 0 and 'FEED_FAIR_PASS ' + mode in result.stdout,
                        (message + '\n' if message else '')
                        + result.stdout[-2000:] + result.stderr[-2000:])

    def test_blocked_kernel_write_yields_to_healthy_peer(self):
        self.assert_mode('write')

    def test_pending_tcp_completion_yields_to_healthy_peer(self):
        self.assert_mode('connect')

    def test_pending_tls_completion_yields_to_healthy_peer(self):
        self.assert_mode('tls')

    def test_tls_write_retains_range_and_original_progress_deadline(self):
        self.assert_mode('retained')

    def test_reply_suffix_and_eof_wait_for_durable_output_then_preserve_fault(self):
        self.assert_mode('reply')

    def test_peer_that_never_answers_is_dropped_at_the_reply_deadline(self):
        self.assert_mode('silent', 'a peer that never answers must be dropped at the reply deadline')

    def test_a_link_leaving_the_live_table_with_a_connection_is_reported_lost(self):
        self.assert_mode('removed', 'a removed link that held a connection must be reported lost '
                                    'before it closes')

    def test_an_answering_peer_gets_hundreds_of_commands_a_second(self):
        # SCEN-FEED-PACE: the worker loop over a kernel socket to a peer that
        # answers at once, one command in flight; it never waits while a
        # command could leave.  The fixed-sleep loop it replaces: 4.7 a second.
        # The run's own account (FEED_PACE ...) goes to stderr; the assertion
        # message is fixed, so the repair ledger can name it.
        result = self.run_mode('pace')
        sys.stderr.write(result.stdout[-2000:] + result.stderr[-2000:])
        self.assertTrue(result.returncode == 0 and 'FEED_FAIR_PASS pace' in result.stdout,
                        'an answering local peer must get hundreds of commands a second, '
                        'and the feed must never wait while one could leave')


if __name__ == "__main__":
    unittest.main()
