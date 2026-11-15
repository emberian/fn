from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import cost_omissions as audit

DECL = '''(defcost release :answers (:ok :fault) :tables (core-reads core-sources)
 :doc "Release the real parent and nested READ.")'''
ARM = '''(defmachine-arms request :declare :arms
 ((:source (:do (drop) (release id generation) :accept (:ok))
            (:charge :steps 24 :bytes 4096))
  (:hand (:if (= serial 0) ((:charge))
            ((:do (drop-again) (release id generation) :accept (:ok)) (:charge :steps 24))))))'''


class CostOmissions(unittest.TestCase):
    def test_reached_mutable_omission_keeps_actual_charges_separate(self):
        found = audit.audit({'provider': DECL, 'consumer': ARM})
        self.assertEqual([x.operation for x in found], ['release', 'release'])
        self.assertEqual(found[0].missing, [':bytes', ':steps', ':descriptors'])
        self.assertIn(':steps 24', found[0].arm_charges[0])
        self.assertEqual(found[0].status, 'unpriced-callback-bound')
        self.assertIn('unverified', found[0].coverage)

    def test_explicit_zero_is_not_silently_omitted(self):
        self.assertEqual(audit.audit({'p': DECL.replace(':answers', ':steps 0 :answers'), 'a': ARM}), [])

    def test_pure_arithmetic_and_unreached_declarations_do_not_trigger(self):
        self.assertEqual(audit.audit({'p': '(defcost release :doc "Pure address arithmetic.")', 'a': ARM}), [])
        self.assertEqual(audit.audit({'p': DECL}), [])

    def test_subarms_keep_cleanup_calls_visible(self):
        found = audit.audit({'p': DECL, 'a': ARM.replace(':arms', ':subarms')})
        self.assertEqual(len(found), 2)
        self.assertIn('/:subarms/', found[0].arm)

    def test_child_does_not_hide_unpriced_stateful_boundary(self):
        found = audit.audit({'p': DECL.replace(':answers', ':child real-release :answers'), 'a': ARM})
        self.assertEqual(len(found), 2)

    def test_real_mutations_change_audit_not_expected_output_only(self):
        positive = DECL.replace(':answers', ':steps 12 :answers')
        self.assertFalse(audit.audit({'p': positive, 'a': ARM}))
        self.assertEqual(len(audit.audit({'p': positive.replace(':steps 12 ', ''), 'a': ARM})), 2)
        self.assertFalse(audit.audit({'p': DECL, 'a': ARM.replace('(release id generation)', '(other id generation)')}))

    def test_unknown_provider_is_an_explicit_partial_scope_result(self):
        report = audit.audit_report({'a': ARM})
        self.assertEqual(report.findings, [])
        self.assertEqual(len(report.unknown_providers), 2)
        self.assertIn('supplied sources', report.unknown_providers[0]['reason'])
        self.assertEqual(report.ambiguous_declarations, [])

    def test_conflicting_actual_declarations_never_use_last_wins(self):
        changed = DECL.replace(':answers', ':steps 12 :answers')
        for sources in ({'first': DECL, 'second': changed, 'a': ARM},
                        {'first': changed, 'second': DECL, 'a': ARM}):
            report = audit.audit_report(sources)
            self.assertEqual(report.findings, [])
            self.assertEqual(report.unknown_providers, [])
            self.assertEqual(len(report.ambiguous_declarations), 1)
            self.assertEqual(len(report.ambiguous_declarations[0]['reached_at']), 2)
        # Identical redundant declarations remain one known provider.
        self.assertEqual(len(audit.audit_report({'p': DECL, 'copy': DECL, 'a': ARM}).findings), 2)

    def test_quoted_and_must_fail_declarations_are_not_real_owners(self):
        fake = "(defmacro template () '" + DECL + ')\n(must-fail ' + DECL + ')'
        self.assertFalse(audit.audit({'p': fake, 'a': ARM}))


if __name__ == '__main__':
    unittest.main()
