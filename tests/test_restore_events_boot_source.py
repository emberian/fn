"""Source transformation controls for the actual cold boot phase class."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
from restore_events_boot_source import PHASES, kind, boot

class EventBootSourceTests(unittest.TestCase):
    def test_machine_only_and_all_three_classes(self):
        src = '(defmachine other :states (:free))\n(defmachine fn2-boot :states (:free) :holds ((:read :storage-window)) :arms ((:free)))'
        out, n = kind(src)
        self.assertEqual(n, 3)
        for phase in PHASES:
            self.assertEqual(out.count(phase), 3)
        self.assertIn('(defmachine other :states (:free))', out)
        self.assertEqual(kind(out), (out, 0))

    def test_receipt_stage_preserves_payload_length(self):
        src = '(:read-result (:cond ((equal row-stage 10) (:next :checkpoint-payload-copy)) (t (:idle))))'
        out, n = boot(src)
        self.assertEqual(n, 1)
        self.assertIn('((equal row-stage 10) (:next :checkpoint-payload-copy))', out)
        self.assertIn('((equal row-stage 11) (:next :checkpoint-events-journal-received))', out)
        self.assertEqual(boot(out), (out, 0))

    def test_declaration_comment_and_string_untouched(self):
        src = '; (:read-result fake)\n"(:checkpoint-root-finish fake)"\n(:checkpoint-root-copy)'
        self.assertEqual(boot(src), (src, 0))

    def test_current_actual_machine_phase_closure(self):
        root = Path(__file__).resolve().parents[1]
        src = (root / 'books/boot.lisp').read_text()
        kinds = (root / 'books/boot-kind.lisp').read_text()
        lr.parse(src)
        self.assertEqual(kind(kinds), (kinds, 0))
        self.assertEqual(boot(src), (src, 0))
        for phase in PHASES:
            self.assertTrue(lr.match('(' + phase + ' ?*body)', lr.parse(src).forms, deep=True), phase)
        self.assertIn('(fn2-boot-checkpoint-investigation-finish id row-generation)', src)
        # The former stop was an unfinished implementation boundary. Check
        # the real forward path and its guarded final release, not that gap.
        forms = lr.parse(src).forms
        self.assertTrue(lr.match('((:validated) (:next :checkpoint-project-begin) ?*rest)', forms))
        path = {
            ':checkpoint-project-begin': ':checkpoint-project-step',
            ':checkpoint-project-step': ':checkpoint-project-protect',
            ':checkpoint-project-protect': ':checkpoint-cbase-acquire',
            ':checkpoint-cbase-acquire': ':checkpoint-loader-begin',
            ':checkpoint-loader-begin': ':checkpoint-loader-step',
            ':checkpoint-loader-step': ':checkpoint-adopt-begin',
            ':checkpoint-authority-copy': ':checkpoint-catalog-begin',
            ':checkpoint-catalog-copy': ':checkpoint-directory-install',
            ':checkpoint-directory-install': ':checkpoint-bank-bind',
            ':checkpoint-bank-bind': ':recover',
            ':recover': ':recover-wait',
            ':recover-wait': ':epoch',
        }
        for phase, target in path.items():
            body = lr.match('(' + phase + ' ?*body)', forms)[0].node
            self.assertTrue(lr.match('(:next ' + target + ')', [body]), (phase, target))
            self.assertFalse(lr.match('(:next :release)', [body]), phase)
        fence = lr.match('(:epoch-fence ?*body)', forms)[0].node
        self.assertTrue(lr.match('(fn2-issue-fence :principal 0)', [fence]))
        result = lr.match('(:epoch-result ?*body)', forms)[0].node
        self.assertTrue(lr.match('((not (equal row-outcome *fn2-outcome-done*)) (:stop :io))', [result]))
        self.assertTrue(lr.match('(fn2-boot-finish-bank-obligations id row-generation)', [result]))
        self.assertEqual(len(lr.match('(:next :release)', forms)), 1)
        self.assertTrue(lr.match('(:next :release)', [result]))
        self.assertIn('(if (equal row-stage 10) row-read-length 4096)', src)

    def test_actual_selected_path_has_a_final_fence_dominator(self):
        src = (Path(__file__).resolve().parents[1] / 'books/boot.lisp').read_text()
        self.assert_selected_recovery_gates(src)

    def assert_selected_recovery_gates(self, src):
        """Refute source routing bypasses; this does not execute ACL2 or claim boot success."""
        forms = lr.parse(src).forms
        machine = lr.match('(defmachine-arms fn2-boot ?*body)', forms, deep=False)[0].node
        arms_decl = next(machine.items[i + 1] for i, x in enumerate(machine.items[:-1]) if getattr(x, 'low', '') == ':arms')
        def arm(name):
            rows = [m.node for m in lr.match('(' + name + ' ?*body)', arms_decl.items, deep=False)
                    if m.captures['body']]
            self.assertEqual(len(rows), 1, name)
            return rows[0]
        def route(phase, answer, target, operation):
            node = arm(phase)
            self.assertTrue(lr.match('(' + operation + ' ?*args)', [node], deep=True), operation)
            cases = lr.match('((:' + answer + ') ?*actions)', [node], deep=True)
            self.assertEqual(len(cases), 1, (phase, answer))
            self.assertTrue(lr.match('(:next ' + target + ')', [cases[0].node], deep=True), (phase, target))
        route(':checkpoint-events-finish', 'validated', ':checkpoint-project-begin', 'fn2-boot-checkpoint-investigation-finish')
        route(':checkpoint-project-step', 'projected', ':checkpoint-project-protect', 'fn2-checkpoint-projection-step-op')
        route(':checkpoint-project-protect', 'protected', ':checkpoint-cbase-acquire', 'fn2-checkpoint-projection-protect-op')
        route(':checkpoint-cbase-acquire', 'held', ':checkpoint-loader-begin', 'fn2-checkpoint-cbase-acquire-op')
        route(':checkpoint-loader-step', 'complete', ':checkpoint-adopt-begin', 'fn2-checkpoint-summary-loader-step-op')
        route(':checkpoint-loader-step', 'changed', ':checkpoint-loader-begin', 'fn2-checkpoint-summary-loader-step-op')
        scan = arm(':checkpoint-loader-step')
        self.assertTrue(lr.match('((:more :yield) ?*rest)', [scan], deep=True))
        self.assertTrue(lr.match('(:otherwise (:stop :checkpoint))', [scan], deep=True))
        self.assertFalse(lr.match('((:row ?*codes) ?*rest)', [scan], deep=True))
        route(':checkpoint-adopt-preflight', 'copy', ':checkpoint-adopt-copy', 'fn2-checkpoint-summary-apply-preflight-op')
        route(':checkpoint-adopt-copy', 'applied', ':checkpoint-authority-begin', 'fn2-checkpoint-summary-apply-step-op')
        route(':checkpoint-authority-copy', 'complete', ':checkpoint-catalog-begin', 'fn2-checkpoint-summary-authority-cold-step-op')
        route(':checkpoint-catalog-copy', 'complete', ':checkpoint-directory-install', 'fn2-event-catalog-cold-step-op')
        self.assertTrue(lr.match('(:do (code) (fn2-directory-cold-install-op) :accept (:installed))', [arm(':checkpoint-directory-install')], deep=True))
        # The cold splice can still stop at its explicit integration frontier.
        # Generic recovery MUST have a nonvacuous path to READY, with final
        # epoch-result as a cut vertex; removing it must remove every path.
        graph = {node.items[0].low: {m.captures['target'].low for m in lr.match('(:next ?target)', [node], deep=True)}
                 for node in arms_decl.items if isinstance(node, lr.Lst) and node.items and isinstance(node.items[0], lr.Atom)}
        def reaches(start, removed):
            pending, seen = [start], set()
            while pending:
                current = pending.pop()
                if current in removed or current in seen:
                    continue
                if current == ':ready':
                    return True
                seen.add(current)
                pending.extend(graph.get(current, ()))
            return False
        self.assertTrue(reaches(':recover', set()))
        self.assertTrue(reaches(':checkpoint-events-finish', set()))
        self.assertFalse(reaches(':checkpoint-project-begin', {':checkpoint-loader-step'}))
        self.assertFalse(reaches(':recover', {':epoch-result'}))
        self.assertFalse(reaches(':checkpoint-events-finish', {':epoch-result'}))
        self.assertTrue(lr.match('(:issue (fn2-issue-fence :principal 0) ?*rest)', [arm(':epoch-fence')], deep=True))
        self.assertTrue(lr.match('(:cond ((equal row-event-ready 0) (:idle)) ((not (equal row-outcome *fn2-outcome-done*)) (:stop :io)) (t ?*success))', [arm(':epoch-result')], deep=True))
        self.assertTrue(lr.match('(fn2-boot-adopt-epoch row-next-epoch)', [arm(':epoch-result')], deep=True))
        # Listeners are woken only in post-Fence release/ready arms.
        for phase in (':checkpoint-events-finish', ':checkpoint-project-begin', ':checkpoint-project-step', ':checkpoint-project-protect', ':checkpoint-cbase-acquire', ':checkpoint-loader-begin', ':checkpoint-loader-step', ':checkpoint-adopt-begin', ':checkpoint-adopt-copy', ':checkpoint-authority-copy', ':checkpoint-directory-install', ':checkpoint-bank-bind', ':recover-wait', ':epoch', ':epoch-fence'):
            self.assertFalse(lr.match('(:wake-row ?target)', [arm(phase)], deep=True), phase)

    def test_real_forward_gates_reject_bypasses(self):
        src = (Path(__file__).resolve().parents[1] / 'books/boot.lisp').read_text()
        mutations = (
            ('((:complete) (:next :checkpoint-adopt-begin)', '((:complete) (:next :checkpoint-authority-begin)'),
            ('((:more :yield) (:next :checkpoint-loader-step)', '((:more :yield :row) (:next :checkpoint-loader-step)'),
            ('((:validated) (:next :checkpoint-project-begin)', '((:validated) (:next :ready)'),
            ('((:protected) (:next :checkpoint-cbase-acquire)', '((:protected) (:next :checkpoint-adopt-begin)'),
            ('((:held) (:next :checkpoint-loader-begin)', '((:held) (:next :checkpoint-authority-begin)'),
        )
        for old, new in mutations:
            self.assertIn(old, src)
            with self.assertRaises(AssertionError):
                self.assert_selected_recovery_gates(src.replace(old, new, 1))
        epoch = lr.match('(:epoch-result :on-refusal ?*body)', lr.parse(src).forms, deep=True)[0].node
        body = src[epoch.start:epoch.end]
        old = '((not (equal row-outcome *fn2-outcome-done*)) (:stop :io))'
        self.assertIn(old, body)
        altered = lr.write(src, [(epoch.start, epoch.end, body.replace(old, '((not (equal row-outcome *fn2-outcome-done*)) (:next :release))', 1))])
        with self.assertRaises(AssertionError):
            self.assert_selected_recovery_gates(altered)

if __name__ == '__main__':
    unittest.main()
