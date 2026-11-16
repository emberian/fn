"""Capture integration controls only; ACL2 model assertions run separately."""
from pathlib import Path
import importlib.util
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import ledger
import proof_repl

spec = importlib.util.spec_from_file_location('cut_launch', ROOT / 'tests/native-device-cut-launch.py')
launch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(launch)


class CaptureSourceTests(unittest.TestCase):
    def test_exact_actual_startup_is_preserved(self):
        original = proof_repl.forms((ROOT / 'tools/image-node.lsp').read_text())
        result = proof_repl.forms(launch.instrument((ROOT / 'tools/image-node.lsp').read_text()))
        self.assertEqual(result[-2], '(load "tests/native-device-cut-capture.lsp")')
        self.assertEqual(result[:-2] + result[-1:], original)

    def test_startup_replacement_refused(self):
        with self.assertRaises(ValueError):
            launch.instrument('(sb-ext:exit :code (invented-main))')

    def test_complete_selected_capture_not_normal_receipt(self):
        source = (ROOT / 'tests/native-device-cut-capture.lsp').read_text()
        forms = ledger.read_forms(source)
        observer = forms[-1]
        # Selected death freezes the one shared record stream, after the actual
        # ordinal has been assigned. It never inserts a successful I/O return.
        self.assertEqual(ledger.head(observer), 'setf')
        self.assertIn('sb-thread:grab-mutex', ledger.calls(observer))
        self.assertIn('fn2-device-evidence-record-locked', ledger.calls(observer))
        self.assertNotIn('fn2-device-perform', ledger.calls(observer))
        self.assertNotIn('fn2-host-post-result', ledger.calls(observer))

    def test_raw_cut_consumer_requires_actual_replay_and_complete_image(self):
        source = (ROOT / 'tests/native-device-cut-raw.lsp').read_text()
        calls = set().union(*(ledger.calls(f) for f in ledger.read_forms(source)))
        self.assertIn('fn2-native-device-cut-replay', calls)
        self.assertIn('(load "tests/native-device-effects-raw.lsp")', source)
        self.assertIn('(assert (eq (car replayed) :pass)', source)


if __name__ == '__main__':
    unittest.main()
