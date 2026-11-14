"""Mutation controls for the promoted host's static crash-coordinate audit."""
from pathlib import Path
import shutil
import json
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import served_native_program_check as checker


class ServedNativeProgramTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        _, paths, _ = checker.inspect(ROOT)
        for name in paths + ['tools/image-node.lsp'] + checker.MODEL_PATHS:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)

    def change(self, name, old, new):
        path = self.root / name
        source = path.read_text()
        self.assertIn(old, source)
        path.write_text(source.replace(old, new, 1))

    def test_actual_graph(self):
        report = checker.check(self.root)
        self.assertTrue(report['audit_ok'], report)
        self.assertEqual(report['cuts'], 14)
        self.assertEqual(report['cut_mapping_status'], 'incomplete')
        self.assertEqual(report['host_refinement'], 'not_checked')

    def test_handshake_budget_must_precede_transport_work(self):
        self.change('host/adapter.lisp',
                    '(fn2-host-tls-next-turn (fn2-native-tls-turns-left tls))',
                    '(values :ok (fn2-native-tls-turns-left tls))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_cancellation_cannot_restore_plaintext_dispatch(self):
        self.change('host/adapter.lisp', '(and cap (fn2-ncap-tls-selected cap)',
                    '(and cap (fn2-ncap-tls cap)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_staging_copy_must_advance_exact_count(self):
        self.change('host/adapter.lisp', '(incf (fn2-nop-tls-seed-offset op) n)',
                    '(incf (fn2-nop-tls-seed-offset op) (fn2-nop-len op))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_short_write_must_retain_offset(self):
        self.change('host/tls.lisp', '(incf (fn2-native-tls-output-offset tls) n)',
                    '(setf (fn2-native-tls-output-offset tls) 0)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_receive_must_observe_bio_capacity(self):
        self.change('host/tls.lisp', '(fn2-native-recv fd (sb-sys:vector-sap buffer) room)',
                    '(fn2-native-recv fd (sb-sys:vector-sap buffer) (length buffer))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_completion_requires_flushed_output(self):
        self.change('host/adapter.lisp',
                    '(and (fn2-nop-tls-finished op) (fn2-native-tls-output-empty-p tls) (or (not handshake) (= (fn2-nop-tls-seed-offset op) (fn2-nop-len op))))',
                    '(fn2-nop-tls-finished op)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_new_cut_requires_coordinate(self):
        self.change('host/adapter.lisp', '(fn2-n-boundary host "take")',
                    '(fn2-n-boundary host "new-stage")')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_comment_cannot_replace_real_ack(self):
        self.change('host/adapter.lisp', '(fn2-host-outbox-ack 1 core)',
                    '(fake-ack 1 core) ; (fn2-host-outbox-ack 1 core)\n')
        self.assertTrue(any('handoff order' in f for f in checker.check(self.root)['findings']))

    def test_worker_boundaries_cannot_swap(self):
        path = self.root / 'host/device.lisp'
        source = path.read_text().replace('"device-syscall"', '"TEMP"')
        source = source.replace('"device-syscall-return"', '"device-syscall"')
        path.write_text(source.replace('"TEMP"', '"device-syscall-return"'))
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_fence_cannot_be_a_write(self):
        self.change('host/device.lisp', '(:fence (fn2-device-fence', '(:fence (%fn2-device-pwrite')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_model_must_land_pending_writes_before_restart(self):
        self.change('sim/sim.lisp', '(fn2-sim-crash-flight-writes (fn2-sim-rows fn2-sim)',
                    '(omit-pending-writes (fn2-sim-rows fn2-sim)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_advance_must_reach_crash(self):
        self.change('sim/sim.lisp',
                    '(mv-let (fn2-core fn2-sim fn2-own) (fn2-sim-crash profile',
                    '(mv-let (fn2-core fn2-sim fn2-own) (skip-crash profile')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_ack_count_cannot_be_zero(self):
        self.change('host/adapter.lisp', '(fn2-host-outbox-ack 1 core)', '(fn2-host-outbox-ack 0 core)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_raw_result_cannot_be_discarded(self):
        self.change('host/device.lisp', '(fn2-device-job-result job) n', '(fn2-device-job-result job) 0')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_syscall_offset_must_come_from_job(self):
        self.change('host/device.lisp', '(fn2-device-job-offset job)', '0')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_crash_guard_cannot_be_false(self):
        self.change('sim/sim.lisp', '(when (equal fault *fn2-fault-crash*))', '(when nil)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_shared_normalizer_cannot_fabricate_count(self):
        self.change('books/host-boundary.lisp', 'kind code count aux len nil cancelled)',
                    'kind code 0 aux len nil cancelled)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_host_wrapper_cannot_change_argument_flow(self):
        self.change('books/host-ops.lisp', '(,target ,@args fn2-ops)', '(,target 0 fn2-ops)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_decoded_result_must_reach_normalizer(self):
        self.change('host/adapter.lisp',
                    '(fn2-n-complete host (fn2-device-job-slot job) code count 0 nil',
                    '(fn2-n-complete host (fn2-device-job-slot job) :ok 0 0 nil')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_cli_cannot_count_source_audit_as_complete_cut_mapping(self):
        command = [sys.executable, str(ROOT / 'tools/native_program_check.py'), '--json']
        full = subprocess.run(command, capture_output=True, text=True, timeout=30)
        self.assertEqual(full.returncode, 1, full.stdout + full.stderr)
        self.assertTrue(json.loads(full.stdout)['audit_ok'])
        source = subprocess.run(command + ['--source-only'], capture_output=True, text=True, timeout=30)
        self.assertEqual(source.returncode, 0, source.stdout + source.stderr)


if __name__ == '__main__':
    unittest.main()
