"""Structural controls; actual BOOT execution requires its producer assembly."""
import hashlib
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
import checkpoint_boot_input_extract as extract


class DescriptorSource(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT/'books/checkpoint-boot-descriptor.lisp').read_text()
        self.forms = lr.parse(self.source).forms

    def test_canonical_input_bodies_and_guards_are_extracted_verbatim(self):
        fixture = json.loads((ROOT/'tools/fixtures/checkpoint-descriptor-input-before.json').read_text())
        before = fixture['source']
        self.assertEqual(hashlib.sha256(before.encode()).hexdigest(), fixture['source_sha256'])
        after = extract.remove_from_restore(before)
        self.assertEqual(extract.remove_from_restore(after), after)
        self.assertEqual(extract.provider(before), (ROOT/'books/checkpoint-descriptor-input.lisp').read_text())
        for name, definition in fixture['definitions'].items():
            self.assertIn(definition, extract.provider(before))
            self.assertFalse(lr.match('(defun '+name+' ?*body)', lr.parse(after).forms))
        # Other actual restore producers remain byte-identical.
        for name in ('fn2-checkpoint-restore-capture-ref', 'fn2-checkpoint-restore-anchor-step'):
            a, b = extract.unique(before, name), extract.unique(after, name)
            self.assertEqual(before[a.start:a.end], after[b.start:b.end])

    def test_existing_range_and_reader_abis_are_used(self):
        calls = lr.match('(fn2-layout-range-code ?*args)', self.forms)
        self.assertEqual(len(calls), 1)
        self.assertEqual(len(calls[0].captures['args']), 9)
        self.assertIn('slot gen 0 len nil kind id ogen fn2-pool', self.source)
        calls = lr.match('(fn2-checkpoint-check-step ?*args)', self.forms)
        self.assertEqual(len(calls), 1)
        reader = (ROOT/'books/checkpoint-descriptor-read.lisp').read_text()
        definition = extract.unique(reader, 'fn2-checkpoint-check-step')
        self.assertEqual(len(calls[0].captures['args']), len(definition.items[2].items))

    def test_current_gate_precedes_actual_child_access_in_both_callbacks(self):
        for name in ('fn2-boot-checkpoint-descriptor-target', 'fn2-boot-checkpoint-descriptor-check'):
            node = extract.unique(self.source, name)
            body = self.source[node.start:node.end]
            self.assertLess(body.index('(fn2-boot-bootstrap-current-p'), body.index('(stobj-let'))
            self.assertIn('(equal (fn2-machine-pending id fn2-core) 0)', body)
            self.assertIn('(equal (fn2-machine-checkpoint-index id fn2-core) c)', body)
        self.assertIn('(equal (fn2-machine-rx-slot id fn2-core) slot)', self.source)
        self.assertIn('(equal (fn2-machine-rx-gen id fn2-core) gen)', self.source)

    def test_zero_grant_and_resume_do_not_reseed_evidence(self):
        node = extract.unique(self.source, 'fn2-boot-checkpoint-descriptor-pool')
        body = self.source[node.start:node.end]
        self.assertLess(body.index('((when (zp budget))'), body.index('(fn2-boot-descriptor-source-p'))
        self.assertLess(body.index('(readable (fn2-layout-range-code'), body.index('(fn2-digests (if first'))
        self.assertIn('(if first (fn2-checkpoint-restore-load-hash', body)
        self.assertIn('(if first (fn2-checkpoint-boot-geometry-copy', body)
        self.assertIn('(fn2-fc-context (if first', body)
        self.assertNotIn('fn2-checkpoint-boot-geometry-load', body)
        self.assertNotIn('checkpoint-layout-ready', body)
        # Existing reader is the sole expected Ref/hash/physical-context join.
        self.assertEqual(len(lr.match('(fn2-checkpoint-check-step ?*args)', lr.parse(body).forms)), 1)

    def test_no_receipt_or_candidate_authority_is_minted(self):
        for name in ('fn2-boot-config-put', 'fn2-boot-config-set-bootstrap-owner-gen',
                     'fn2-checkpoints-set-state', 'fn2-checkpoints-set-checkpoint'):
            self.assertFalse(lr.match('('+name+' ?*args)', self.forms))
        self.assertNotIn('(defun fn2-boot-bootstrap-current-p', self.source)
        self.assertIn('*fn2-checkpoint-state-preparing*', self.source)
        self.assertIn('fn2-boot-config-anchor-checked-mask', self.source)

    def test_skip_requires_receipt_and_unambiguous_exact_physical_scan(self):
        skip = extract.unique(self.source, 'fn2-boot-descriptor-skipped-p')
        body = self.source[skip.start:skip.end]
        self.assertIn('(and (natp c) (< c 4)', body)
        self.assertIn('(fn2-boot-bootstrap-receipt-p kind id ogen fn2-boot-config fn2-origin)', body)
        self.assertIn('(equal (logand (ash 1 c) (fn2-boot-config-anchor-checked-mask fn2-boot-config)) 0)', body)
        for mask in ('empty', 'invalid'):
            call = '(logand (ash 1 c) (fn2-boot-config-anchor-' + mask + '-mask fn2-boot-config))'
            self.assertIn('(equal ' + call + ' 0)', body)
            self.assertIn('(not (equal ' + call + ' 0))', body)
        target = extract.unique(self.source, 'fn2-boot-checkpoint-descriptor-target-pool')
        code = self.source[target.start:target.end]
        self.assertIn('(mv :skip 0 0)', code)
        self.assertLess(code.index('(fn2-boot-descriptor-skipped-p'),
                        code.index('(fn2-boot-descriptor-source-p'))
        # Source refusal remains the fallback; an absent candidate cannot skip.
        self.assertIn('(mv :source 0 0)', code)
        self.assertEqual(len(lr.match('(fn2-checkpoint-restore-read-target ?*args)', [target])), 1)


if __name__ == '__main__':
    unittest.main()
