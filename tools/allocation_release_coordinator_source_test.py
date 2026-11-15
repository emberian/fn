"""Actual producer/dispatcher source controls; no ACL2 or IO PASS implied."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import release_coordinator_mv_transform as mvfix

SOURCE = Path('books/allocation-release-coordinator.lisp')


class ReleaseCoordinator(unittest.TestCase):
    def test_claim_and_credit_end_precede_member_exposure(self):
        s = SOURCE.read_text()
        submit = s[s.index('(defun fn2-allocation-release-submit '):s.index('(defun fn2-allocation-release-install-member ')]
        order = ['(fn2-pool-credit-begin ', '(fn2-pool-reserve-credit ',
                 '(fn2-allocation-release-pack-staged ', '(fn2-commit-start ',
                 '(fn2-release-live-claim ', '(fn2-pool-credit-end ',
                 '(fn2-commit-put-txn-member ', '*fn2-allocation-release-phase-waiting*']
        positions = [submit.index(call) for call in order]
        self.assertEqual(positions, sorted(positions))
        self.assertIn('(fn2-commit-resource id 0 fn2-core)', s)
        self.assertIn('(fn2-release-evidence-claim-children journal epoch allocation batch', s)
        self.assertIn('(fn2-allocation-release-credit-group (fn2-commit-rows fn2-commit))', s)
        self.assertIn('(fn2-pool-class-for (fn2-allocation-release-member-capacity) fn2-pool)', s)
        self.assertNotIn('(fn2-core-reserve ', s)
        self.assertNotIn('(fn2-commit-admit-txn ', submit)

    def test_dispatch_has_typed_refusal_and_real_field_match(self):
        generic = Path('books/retirement-coordinator.lisp').read_text()
        self.assertIn('(fn2-retirement-adapter-release-allocation . (mv :invalid fn2-core))', generic)
        actual = Path('books/checkpoint-lifecycle-coordinator.lisp').read_text()
        self.assertIn('(fn2-retirement-adapter-release-allocation . (fn2-allocation-release-install-member ', actual)
        s = SOURCE.read_text()
        install = s[s.index('(defun fn2-allocation-release-install-member '):s.index('(defun fn2-release-live-workspace-terminal-p ')]
        for required in ['(fn2-release-evidence-row-matches ', '(fn2-release-evidence-row-owned-p ',
                         '(fn2-format-release-allocation-decode ', '(fn2-release-member-fields-match-p ',
                         '*fn2-allocation-release-phase-waiting*', '*fn2-allocation-release-phase-persisted*']:
            self.assertIn(required, install)
        self.assertNotIn('fn2-alloc-release', install)
        commit = Path('books/commit.lisp').read_text()
        self.assertIn('(fn2-allocation-release-coordinator-events)', commit)
        body = commit[commit.index('(defun fn2-commit-txn-body '):commit.index('(defun fn2-commit-txn-scan ')]
        self.assertNotIn('*record-kind-release-allocation*', body)

    def test_exact_terminal_settlement_before_actual_credit_return(self):
        s = SOURCE.read_text()
        poll = s[s.index('(defun fn2-allocation-release-poll '):]
        for required in ['(fn2-release-live-workspace-terminal-p writer writer-gen batch fn2-core)',
                         '(fn2-commit-take-exact kind owner generation batch event fn2-core)',
                         '*fn2-commit-outcome-accepted*', '*fn2-allocation-release-phase-persisted*',
                         '(fn2-pool-release-credit slot gen group batch kind owner generation fn2-pool)',
                         '(fn2-allocation-release-set-workspace-released 0 1 fn2-allocation-release)']:
            self.assertIn(required, poll)
        self.assertLess(poll.index('(fn2-commit-take-exact '), poll.index('(fn2-pool-release-credit '))
        self.assertNotIn('(fn2-allocation-release-set-gen ', poll)
        self.assertNotIn('fn2-alloc-release', poll)

    def test_stobj_mv_class_and_structural_shapes(self):
        s = SOURCE.read_text()
        self.assertEqual(mvfix.transformed(s), (s, 0))
        sample = '(mv :uncertain b e (fn2-release-live-uncertain fn2-core))'
        expected = '(let ((fn2-core (fn2-release-live-uncertain fn2-core))) (mv :uncertain b e fn2-core))'
        self.assertEqual(mvfix.transformed(sample), (expected, 1))
        def walk(n):
            if isinstance(n, lr.Lst):
                h = getattr(n.items[0], 'text', '') if n.items else ''
                if h == 'if': self.assertEqual(len(n.items), 4)
                if h == 'b*': self.assertEqual(len(n.items), 3)
                for child in n.items: walk(child)
            elif isinstance(n, lr.Pre): walk(n.node)
        for form in lr.parse(s).forms: walk(form)

    def test_retirement_is_terminal_without_replenishment(self):
        s = SOURCE.read_text()
        poll = s[s.index('(defun fn2-allocation-release-poll '):]
        self.assertIn("(member-eq returned '(:ok :retired))", poll)
        prestart = s[s.index('(defun fn2-release-live-return-empty '):s.index('(defun fn2-release-live-start-refused-p ')]
        self.assertLess(prestart.index('(eq returned :retired)'), prestart.index('(fn2-pool-credit-abort-empty '))
        fixture = Path('tests/allocation-release-credit-retirement-unit.lisp').read_text()
        lr.parse(fixture)
        for actual in ['(fn2-cwc-body-with-limit 1 fn2-pool)', '(fn2-release-live-return-empty ',
                       '(fn2-allocation-release-poll ', '*fn2-pool-credit-depleted*',
                       '*fn2-pool-state-retired*', '(eq polled :persisted)']:
            self.assertIn(actual, fixture)

if __name__ == '__main__':
    unittest.main()
