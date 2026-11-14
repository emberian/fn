"""Mutation controls for the promoted host's static crash-coordinate audit."""
from pathlib import Path
import shutil
import json
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import served_native_program_check as checker
import served_storage_cut_check as storage_checker


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
        self.assertEqual(report['cuts'], 9)
        self.assertEqual(report['cut_mapping_status'], 'incomplete')
        self.assertEqual(report['host_refinement'], 'not_checked')

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

    def test_fence_return_cut_witness_names_the_composition_gap(self):
        report = checker.check(self.root)
        family = report['storage_return_cut_family']
        self.assertTrue(family['source_ok'], family)
        self.assertFalse(family['mapping_complete'])
        self.assertIn('scheduled-source-present', family['model_composition'])
        cuts = {cut['label']: cut for cut in family['cuts']}
        self.assertEqual(cuts['device-syscall-return']['phase'], 'physical-returned-unposted')
        self.assertFalse(cuts['device-syscall-return']['terminal_posted'])
        self.assertIn('before fn2-sim-native-post', cuts['device-return']['model_prefix'])
        self.assertTrue(all(e['ast_path'] and e['contract'] for e in family['evidence']))

    def test_reachable_fence_return_cannot_be_omitted(self):
        mapping = dict(storage_checker.FENCE_CUTS)
        del mapping[('fn2-device-worker', 'device-syscall-return')]
        with mock.patch.dict(storage_checker.FENCE_CUTS, mapping, clear=True):
            report = checker.check(self.root)
        self.assertFalse(report['audit_ok'])
        self.assertTrue(any('fence cut relation' in f for f in report['findings']))

    def test_physical_return_cannot_be_attributed_to_terminal_post(self):
        mapping = dict(storage_checker.FENCE_CUTS)
        mapping[('fn2-device-worker', 'device-syscall-return')] = 'terminal-posted'
        with mock.patch.dict(storage_checker.FENCE_CUTS, mapping, clear=True):
            report = checker.check(self.root)
        self.assertFalse(report['audit_ok'])

    def test_unreachable_physical_call_cannot_satisfy_fence_witness(self):
        # The old walk/order inventory still sees exactly the same calls.
        self.change('host/device.lisp', '(fn2-device-perform device job)',
                    '(when nil (fn2-device-perform device job))')
        report = checker.check(self.root)
        self.assertFalse(report['audit_ok'])
        self.assertTrue(any('physical call between callbacks' in f for f in report['findings']))

    def test_post_inserted_before_return_cannot_satisfy_fence_witness(self):
        self.change('host/device.lisp', '(fn2-device-perform device job)',
                    '(fn2-device-perform device job) (fn2-host-post-result 0 0 0 0 0 0 0 0 0 core)')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_fence_snapshot_commit_cannot_be_disabled(self):
        self.change('sim/storage.lisp',
                    '(fn2-storage-fence-bytes 0 (* slot (fn2-sim-storage-rows fn2-sim-storage)) t fn2-sim-storage)',
                    '(fn2-storage-fence-bytes 0 (* slot (fn2-sim-storage-rows fn2-sim-storage)) nil fn2-sim-storage)')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_fence_cannot_enter_send_only_release_phase(self):
        self.change('sim/sim.lisp',
                    '(release (and (equal kind *fn2-action-send*)',
                    '(release (and (equal kind *fn2-action-fence*)')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_model_new_yield_requires_a_new_composition_witness(self):
        self.change('sim/sim.lisp',
                    '((when (and (eq code :would-block) (equal physical-count 0)))',
                    '((when (or (eq code :ok) (and (eq code :would-block) (equal physical-count 0))))')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_real_scheduler_cannot_bypass_split_stage(self):
        self.change('sim/sim.lisp',
                    '(fn2-sim-step-completion slot fault word fn2-core fn2-sim fn2-own)',
                    '(fn2-sim-complete slot fault word fn2-core fn2-sim fn2-own)')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_retained_raw_count_cannot_be_fabricated(self):
        self.change('sim/sim.lisp', '(return-count (nth 6 packet))', '(return-count 0)')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_retained_raw_fault_cannot_be_discarded(self):
        self.change('sim/sim.lisp', '(return-fault (nth 10 packet))', '(return-fault *fn2-fault-none*)')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_native_trace_must_retain_actual_syscall_result(self):
        self.change('host/adapter.lisp',
                    '(fn2-device-job-result job) (fn2-device-job-errno job))))',
                    '0 (fn2-device-job-errno job))))')
        self.assertFalse(checker.check(self.root)['storage_return_cut_family']['source_ok'])

    def test_cli_cannot_count_source_audit_as_complete_cut_mapping(self):
        command = [sys.executable, str(ROOT / 'tools/native_program_check.py'), '--json']
        full = subprocess.run(command, capture_output=True, text=True, timeout=30)
        self.assertEqual(full.returncode, 1, full.stdout + full.stderr)
        self.assertTrue(json.loads(full.stdout)['audit_ok'])
        source = subprocess.run(command + ['--source-only'], capture_output=True, text=True, timeout=30)
        self.assertEqual(source.returncode, 0, source.stdout + source.stderr)


if __name__ == '__main__':
    unittest.main()
