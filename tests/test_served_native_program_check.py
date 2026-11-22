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
        self.assertEqual(report['cuts'], 21)
        self.assertEqual(report['cut_mapping_status'], 'incomplete')
        self.assertEqual(report['host_refinement'], 'not_checked')

    def test_storage_cut_context_cannot_lose_incarnation(self):
        self.change('host/adapter.lisp',
                    '(fn2-n-boundary host "device-submit" slot (fn2-nop-gen op))',
                    '(fn2-n-boundary host "device-submit" slot 0)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_terminal_post_cut_cannot_drop_generation(self):
        self.change('host/adapter.lisp',
                    '(fn2-n-boundary host "post" slot (fn2-nop-gen op))',
                    '(fn2-n-boundary host "post" slot 0)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_worker_cut_cannot_drop_actual_job(self):
        self.change('host/device.lisp',
                    '(funcall (fn2-device-boundary device) "device-syscall-return" job)',
                    '(funcall (fn2-device-boundary device) "device-syscall-return")')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_selected_ordinal_cannot_be_fabricated(self):
        self.change('host/adapter.lisp',
                    '(funcall *fn2-n-boundary-observer* host (fn2-nhost-boundaries host)',
                    '(funcall *fn2-n-boundary-observer* host 1')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_correspondence_must_replay_actual_core(self):
        self.change('sim/native-device-cut.lisp',
                    '(fn2-native-device-control-replay', '(pretend-control-replay')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_partial_storage_path_cannot_claim_tls_or_compress(self):
        report = checker.check(self.root)
        self.assertEqual(len(report['physical_cut_replay']['labels']), 4)
        self.assertIn('post', report['physical_cut_replay']['conditional_labels'])
        self.assertIn(['fn2-n-post-completions', 'post'], report['unmapped_sites'])
        self.assertEqual(len(report['unmapped_sites']), 17)
        self.assertIn(['fn2-n-start-now', 'connect-start'], report['unmapped_sites'])
        self.assertIn(['fn2-n-ready', 'connect-ready'], report['unmapped_sites'])
        self.assertIn(['fn2-native-compress-record-step', 'compress-transform'], report['unmapped_sites'])
        self.assertEqual(report['cut_mapping_status'], 'incomplete')

    def test_native_digest_word_offset_cannot_change(self):
        self.change('host/b3-native.lisp', '(sb-sys:sap-ref-32 sap 28) dg)',
                    '(sb-sys:sap-ref-32 sap 24) dg)')
        self.assertTrue(any('native ABI/effect wiring changed: fn2-b3-native-store' in f
                            for f in checker.check(self.root)['findings']))

    def test_native_captured_word_cannot_overwrite_previous_word(self):
        self.change('host/b3-native.lisp',
                    '(setf (sb-sys:sap-ref-32 sap 4) (fn2-digests-w1 src dg))',
                    '(setf (sb-sys:sap-ref-32 sap 0) (fn2-digests-w1 src dg))')
        self.assertTrue(any('native ABI/effect wiring changed: fn2-b3-native-load' in f
                            for f in checker.check(self.root)['findings']))

    def test_native_digest_store_cannot_add_an_unmodeled_write(self):
        self.change('host/b3-native.lisp',
                    '(declare (type sb-sys:system-area-pointer sap))\n (fn2-digest-store-words',
                    '(declare (type sb-sys:system-area-pointer sap))\n'
                    ' (fn2-digests-set-w0 0 99 dg)\n (fn2-digest-store-words')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_native_node_cannot_swap_captured_inputs(self):
        self.change('host/b3-native.lisp',
                    '(fn2-b3-native-load left (sb-alien:alien-sap l) dg)',
                    '(fn2-b3-native-load right (sb-alien:alien-sap l) dg)')
        self.assertTrue(any('native ABI/effect wiring changed: fn2-b3-native-node' in f
                            for f in checker.check(self.root)['findings']))

    def test_native_node_cannot_bypass_shared_store(self):
        self.change('host/b3-native.lisp',
                    '(fn2-b3-%node (sb-alien:alien-sap l) (sb-alien:alien-sap r) (sb-alien:alien-sap out))\n'
                    '   (fn2-b3-native-store dst (sb-alien:alien-sap out) dg)',
                    '(fn2-b3-%node (sb-alien:alien-sap l) (sb-alien:alien-sap r) (sb-alien:alien-sap out))\n'
                    '   (fn2-digests-set-w0 dst 0 dg)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_handshake_budget_must_precede_transport_work(self):
        self.change('host/tls.lisp',
                    '(fn2-tls-transport-next (fn2-tls-%input-room handle)',
                    '(unbudgeted-next (fn2-tls-%input-room handle)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_cancellation_cannot_restore_plaintext_dispatch(self):
        self.change('host/adapter.lisp', '(fn2-tls-transport-selected-p (fn2-nop-cap op)',
                    '(live-handle-only (fn2-nop-cap op)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_staging_copy_must_advance_exact_count(self):
        self.change('host/tls.lisp', ':start1 offset :end1 (+ offset count)',
                    ':start1 offset :end1 (+ offset (length seed))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_record_must_authorize_live_loan(self):
        self.change('host/tls.lisp', '(fn2-host-tls-record-next slot',
                    '(unvalidated-record-select slot')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_record_cannot_use_native_mirror_bounds(self):
        self.change('host/tls.lisp', '(sb-sys:sap+ (sb-sys:vector-sap bytes) address) count)',
                    '(fn2-n-sap host (fn2-nop-address op)) (fn2-nop-len op))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_failure_preserves_observed_payload(self):
        self.change('host/adapter.lisp',
                    '(fn2-n-complete host slot :failed count 0 nil (fn2-n-octets host address count))',
                    '(fn2-n-complete host slot :failed count)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_child_requires_live_core_and_upper_pending(self):
        self.change('host/tls.lisp', '(fn2-host-tls-child-next slot',
                    '(unvalidated-child-select slot')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_child_uses_authorized_private_offset(self):
        self.change('host/tls.lisp', 'action bytes offset offset count)',
                    'action bytes 0 offset count)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_record_must_observe_raw_count(self):
        self.change('host/tls.lisp', 'serial raw moved errno transport record)',
                    'serial raw 0 errno transport record)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_short_write_must_retain_offset(self):
        self.change('host/tls.lisp',
                    '(multiple-value-bind (raw errno)\n        (fn2-native-tls-perform tls action offset count',
                    '(multiple-value-bind (raw errno)\n        (fn2-native-tls-perform tls action 0 count')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_receive_must_observe_bio_capacity(self):
        self.change('host/tls.lisp', '(fn2-native-recv fd (sb-sys:vector-sap input) count)',
                    '(fn2-native-recv fd (sb-sys:vector-sap input) (length input))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_completion_requires_flushed_output(self):
        self.change('books/tls-record-policy.lisp',
                    '((< oo ol) (mv :act 5 oo (min quantum (- ol oo))))',
                    '(nil (mv :act 5 oo (min quantum (- ol oo))))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_observation_preserves_epoch_and_raw_return(self):
        self.change('host/tls.lisp',
                    '(fn2-tls-transport-observe cap-index nonce slot generation serial raw 0 errno ledger)',
                    '(fn2-tls-transport-observe cap-index nonce slot generation serial 0 0 errno ledger)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_handoff_preserves_pending_input(self):
        self.change('host/adapter.lisp',
                    '(setf (fn2-native-tls-transport tls) ledger)',
                    '(setf (fn2-native-tls-transport tls) (create-fn2-tls-transport))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_free_cannot_bypass_logical_retirement(self):
        self.change('host/tls.lisp',
                    '(fn2-tls-transport-retire cap-index nonce (fn2-native-tls-transport tls))',
                    '(values :closing (fn2-native-tls-transport tls))')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_pointer_must_come_from_ledger(self):
        self.change('host/tls.lisp',
                    '(fn2-tls-transport-handle (fn2-native-tls-transport tls))',
                    '(private-handle-copy tls)')
        self.assertFalse(checker.check(self.root)['audit_ok'])

    def test_tls_allocation_identity_cannot_be_fabricated(self):
        self.change('host/tls.lisp', '(values (sb-sys:sap-int allocated) 0)',
                    '(values 4096 0)')
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
        self.change('books/host-result.lisp', 'kind code count aux len nil cancelled)',
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
