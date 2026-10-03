"""Actual push worker fairness with kernel output and recorded owner leaves."""
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]

class FeedFairRoundTests(unittest.TestCase):
    def run_mode(self, mode):
        result = subprocess.run([shutil.which('sbcl') or 'sbcl', '--noinform', '--script',
                                 'tests/native_feed_fair_round_raw.lisp', mode],
                                cwd=ROOT, capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('FEED_FAIR_PASS', result.stdout)

    def test_blocked_kernel_write_yields_to_healthy_peer(self):
        self.run_mode('write')

    def test_pending_tcp_completion_yields_to_healthy_peer(self):
        self.run_mode('connect')

    def test_pending_tls_completion_yields_to_healthy_peer(self):
        self.run_mode('tls')

    def test_tls_write_retains_range_and_original_progress_deadline(self):
        self.run_mode('retained')

    def test_reply_suffix_and_eof_wait_for_durable_output_then_preserve_fault(self):
        self.run_mode('reply')
