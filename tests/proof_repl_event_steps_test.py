from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch
from types import SimpleNamespace
import tempfile
import os
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import proof_repl as repl


class EventSteps(unittest.TestCase):
    def test_scope(self):
        events = ['(local (defthm private (equal x x)))',
                  '(defthm public (equal x x) :hints (("Goal" :use private)))',
                  '(encapsulate () (local (defthm nested (equal y y))))']
        hoisted, body = repl.encapsulated('(in-package "ACL2")\n' + '\n'.join(events),
                                         Path('.'), set(), 20, 2000000)
        self.assertEqual(hoisted, [])
        self.assertEqual(body, '(encapsulate ()\n' + '\n'.join(
            f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {f}))'
            for f in events) + '\n)')
        self.assertEqual(body.count('with-prover-step-limit'), 3)

    def test_unsafe(self):
        for form in [':ubt foo', '(set-prover-step-limit 3000000)',
                     '(with-prover-step-limit 3000000 t (thm t))', '(defttag foo)',
                     '(local (defttag foo))', '(progn (thm t) (set-prover-step-limit 0))',
                     '(encapsulate () (local (with-prover-step-limit 0 t (thm t))))',
                     '(thm t) (thm t)', '(local (thm t) (thm t))']:
            with self.subTest(form=form), self.assertRaises(ValueError):
                repl.per_event_steps(form, 2000000)
        for steps in [0, -1, 2000001, 2.5, True]:
            with self.subTest(steps=steps), self.assertRaises(ValueError):
                repl.per_event_steps('(thm t)', steps)

    def test_scoped_range_requires_explicit_finite_positive_time_limit(self):
        for limit in [None, 0, -1, float('inf'), -float('inf'), float('nan')]:
            args = SimpleNamespace(per_event_steps=2000000, ld_local=True, limit=limit)
            with self.subTest(limit=limit), \
                 patch.object(repl, 'book_path') as book, \
                 patch.object(repl, 'send_many') as send, \
                 self.assertRaisesRegex(SystemExit, 'explicit positive finite --limit'):
                repl.send_range(args)
            book.assert_not_called()
            send.assert_not_called()

    def test_scoped_range_disables_only_outer_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'events.lisp'
            path.write_text('(local (defthm private (equal x x)))')
            args = SimpleNamespace(name='test', book=str(path), start=None, until=None,
                                   through=None, skip_includes=True, ld_local=True,
                                   limit=20, full=False, keep_going=False, per_event_steps=2000000)
            with patch.object(repl, 'book_path', return_value=path), \
                 patch.object(repl, 'read_state', return_value={}), \
                 patch.object(repl, 'guard_notes', return_value=[]), \
                 patch.object(repl, 'warn_free_expands'), \
                 patch.object(repl, 'send_many', return_value=0) as send:
                self.assertEqual(repl.send_range(args), 0)
                self.assertEqual(send.call_args.args[2], 0)
                self.assertTrue(send.call_args.kwargs['scoped_event_budgets'])
                self.assertIn('(with-prover-time-limit 20 ', send.call_args.args[1][-1][1])

    def test_server_preserves_inner_cap_and_bounded_compound_deadline(self):
        form = '(encapsulate () (with-prover-step-limit 2000000 t (with-prover-time-limit 20 (thm t))))'
        acl2 = Mock()
        acl2.send.return_value = ('', False)
        state = {'sends': 0, 'load_timeout': 120}
        repl.handle({'op': 'send', 'form': form, 'limit': 0,
                     'scoped_event_budgets': True}, acl2, state, 20)
        acl2.send.assert_called_once_with(form, 120)
        acl2.reset_mock()
        repl.handle({'op': 'send', 'form': '(thm t)', 'limit': None}, acl2, state, 20)
        acl2.send.assert_called_once_with('(with-prover-time-limit 20 (thm t))', 60)

    def test_q1_declared_source_event_classes(self):
        root = Path(__file__).resolve().parents[1]
        books = ('arms machines core-children exec-state machines-directory arm-children '
                 'ops-heads ops-issued-count ops-issued-effects arm-issue-effects '
                 'machine-arms core-lowering core-product-lowering').split()
        sources = [root / 'books' / (book + '.lisp') for book in books]
        sources.append(root / 'tests' / 'column-snapshot-support.lisp')
        for source in sources:
            with self.subTest(source=source.name):
                hoisted, body = repl.encapsulated(source.read_text(), source.parent,
                                                  set(), 20, 2000000)
                self.assertTrue(body.startswith('(encapsulate ()'))
        event = '(defcolumns example ((value :u32)))'
        self.assertEqual(repl.per_event_steps(event, 2000000, 20),
                         f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {event}))')
        with self.assertRaises(ValueError):
            repl.per_event_steps('(fn2-unknown-event t)', 2000000, 20)

    def test_stable_source_event_declarations_keep_original_budgets(self):
        root = Path(__file__).resolve().parents[1]
        for book in ['commit-geometry', 'run-geometry', 'digest-store', 'pool-digest',
                     'merkle', 'origin', 'read-pins']:
            source = root / 'books' / (book + '.lisp')
            with self.subTest(book=book):
                hoisted, body = repl.encapsulated(source.read_text(), source.parent,
                                                  set(), 20, 2000000)
                originals = [form for form in repl.forms(source.read_text())
                             if repl.form_head(form) not in ['in-package', 'include-book', 'defpkg']]
                self.assertEqual(body, '(encapsulate ()\n' + '\n'.join(
                    f'(with-prover-step-limit 2000000 t {repl.wrap_limit(form, 20, event=True)})'
                    for form in originals) + '\n)')
        for form in ['(defttag unsafe)', '(defaxiom unsafe t)', '(fn2-unreviewed-macro t)']:
            with self.subTest(form=form), self.assertRaises(ValueError):
                repl.per_event_steps(form, 2000000, 20)

    def test_reference_effect_actual_source_constructor_events(self):
        root = Path(os.environ.get('FN_PROOF_EVENT_SOURCE_ROOT',
                                   Path(__file__).resolve().parents[1]))
        sources = [root / name for name in [
            'books/reference-effect-lowering.lisp',
            'tests/reference-effect-lowering-unit.lisp',
            'tests/reference-effect-emitted-unit.lisp']]
        if not all(source.is_file() for source in sources):
            self.skipTest('reference effect sources absent; set FN_PROOF_EVENT_SOURCE_ROOT to their checkout')
        constructors = []
        for source in sources:
            with self.subTest(source=source.name):
                originals = [form for form in repl.forms(source.read_text())
                             if repl.form_head(form) not in ['in-package', 'include-book', 'defpkg']]
                constructors.extend(repl.form_head(form) for form in originals
                                    if repl.form_head(form) in ['defcorechild', 'defstobj'])
                hoisted, body = repl.encapsulated(source.read_text(), source.parent,
                                                  set(), 20, 2000000)
                self.assertEqual(body, '(encapsulate ()\n' + '\n'.join(
                    f'(with-prover-step-limit 2000000 t {repl.wrap_limit(form, 20, event=True)})'
                    for form in originals) + '\n)')
        self.assertEqual(constructors.count('defcorechild'), 3)
        self.assertEqual(constructors.count('defstobj'), 1)

    def test_cold_allocator_complete_source_inventory(self):
        root = Path(os.environ.get('FN_PROOF_COLD_ALLOC_ROOT',
                                   Path(__file__).resolve().parents[1]))
        sources = [root / ('books/' + book + '.lisp') for book in
                   ['alloc', 'columns', 'declare', 'operations', 'owed', 'tuple']]
        sources.append(root / 'tests/alloc-adopt-identity-unit.lisp')
        if not all(source.is_file() for source in sources):
            self.skipTest('cold allocator fixture absent; set FN_PROOF_COLD_ALLOC_ROOT')
        heads = set()
        for source in sources:
            with self.subTest(source=source.name):
                originals = [form for form in repl.forms(source.read_text())
                             if repl.form_head(form) not in ['in-package', 'include-book', 'defpkg']]
                heads.update(repl.form_head(form) for form in originals)
                hoisted, body = repl.encapsulated(source.read_text(), source.parent,
                                                  set(), 20, 2000000)
                self.assertEqual(body, '(encapsulate ()\n' + '\n'.join(
                    f'(with-prover-step-limit 2000000 t {repl.wrap_limit(form, 20, event=True)})'
                    for form in originals) + '\n)')
        self.assertIn('fn2-cm-defreaders', heads)
        self.assertIn('defun-nx', heads)

    def test_native_b3_actual_source_evidence_events(self):
        root = Path(os.environ.get('FN_PROOF_NATIVE_SOURCE_ROOT',
                                   Path(__file__).resolve().parents[1]))
        heads = set()
        for book in ['native-b3-correspondence', 'native-b3-evidence']:
            source = root / 'books' / (book + '.lisp')
            with self.subTest(book=book):
                originals = [form for form in repl.forms(source.read_text())
                             if repl.form_head(form) not in ['in-package', 'include-book', 'defpkg']]
                heads.update(repl.form_head(form) for form in originals)
                hoisted, body = repl.encapsulated(source.read_text(), source.parent,
                                                  set(), 20, 2000000)
                self.assertEqual(body, '(encapsulate ()\n' + '\n'.join(
                    f'(with-prover-step-limit 2000000 t {repl.wrap_limit(form, 20, event=True)})'
                    for form in originals) + '\n)')
        self.assertTrue({'defun-nx', 'fn2-owed-discharge', 'fn2-assert-owed-teeth',
                         'fn2-assert-square-evidence'}.issubset(heads))

    def test_derived_inventory_is_finite_and_keeps_original_scope(self):
        source = '''(defmacro own-event () '(thm t))
(local (defmacro private-event () '(thm t)))
(defcolumns sample ((value :u8)))
(defun decoy () '(defmacro not-declared () nil))
(encapsulate () (local (private-event)) (own-event) (sample-preserves step (sample)))'''
        names = repl.declared_event_macros([source])
        self.assertEqual(names, {'own-event', 'private-event', 'sample-preserves'})
        original = repl.forms(source)[-1]
        self.assertEqual(repl.per_event_steps(original, 2000000, 20, names),
                         f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {original}))')
        with self.assertRaises(ValueError):
            repl.per_event_steps('(not-declared)', 2000000, 20, names)
        for head in ['skip-proofs', 'defaxiom', 'defttag', 'set-prover-step-limit',
                     'with-prover-step-limit', 'ld', 'u', 'progn!']:
            declared = repl.declared_event_macros([f'(defmacro {head} () nil)'])
            with self.subTest(head=head), self.assertRaises(ValueError):
                repl.per_event_steps(f'({head})', 2000000, 20, declared)

    def test_inventory_refreshes_after_declaration_removal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / 'target.lisp'
            dependency = root / 'dependency.lisp'
            target.write_text('(include-book "dependency")\n(own-event)')
            dependency.write_text('(defmacro own-event () \'(thm t))')
            names, first_hashes, text = repl.source_event_inventory(target, root)
            self.assertIn('own-event', names)
            self.assertEqual(text, target.read_text())
            dependency.write_text('(defun replacement () nil)')
            names, second_hashes, _ = repl.source_event_inventory(target, root)
            self.assertNotIn('own-event', names)
            self.assertNotEqual(first_hashes['dependency'], second_hashes['dependency'])
            with self.assertRaises(ValueError):
                repl.per_event_steps('(own-event)', 2000000, 20, names)

    def test_bound66_frozen_full_original_event_transform(self):
        plan_path = os.environ.get('FN_PROOF_BOUND66_PLAN')
        root_path = os.environ.get('FN_PROOF_BOUND66_ROOT')
        if not plan_path or not root_path:
            self.skipTest('set FN_PROOF_BOUND66_PLAN and FN_PROOF_BOUND66_ROOT for frozen source controls')
        import json
        import hashlib
        root = Path(root_path)
        plan = json.loads(Path(plan_path).read_text())
        names, hashes, _ = repl.source_event_inventory(root / (plan['root'] + '.lisp'), root)
        self.assertEqual(set(hashes), {row['book'] for row in plan['rows']})
        for row in plan['rows']:
            source = root / (row['book'] + '.lisp')
            with self.subTest(book=row['book']):
                self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), row['raw_sha256'])
                originals = [form for form in repl.forms(source.read_text())
                             if repl.form_head(form) not in ['in-package', 'include-book', 'defpkg']]
                _, body = repl.encapsulated(source.read_text(), source.parent,
                                           set(), 20, 2000000, names)
                self.assertEqual(body, '(encapsulate ()\n' + '\n'.join(
                    f'(with-prover-step-limit 2000000 t {repl.wrap_limit(form, 20, event=True)})'
                    for form in originals) + '\n)')

    def test_reviewed_assembly_generator_heads(self):
        # The core preservation macro comes from core.lisp's explicit columns
        # generator; successor columns are a literal template in their provider.
        for form in ['(defcost operation :answers t)',
                     '(fn2-core-preserves operation (fn2-core) :rows nil)',
                     '(fn2-succ-slots-preserves operation (fn2-succ-slots) :raw-rows t)']:
            with self.subTest(form=form):
                self.assertEqual(repl.per_event_steps(form, 2000000, 20),
                                 f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {form}))')

    def test_scoped_range_checks_attachment_boundary_before_sending(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'events.lisp'
            path.write_text('(attach-stobj generic concrete)')
            args = SimpleNamespace(name='test', book=str(path), start=None, until=None,
                                   through=None, skip_includes=True, ld_local=True,
                                   limit=20, full=False, keep_going=False, per_event_steps=2000000)
            with patch.object(repl, 'book_path', return_value=path), \
                 patch.object(repl, 'send_many') as send, \
                 self.assertRaisesRegex(SystemExit, 'attachment'):
                repl.send_range(args)
            send.assert_not_called()

    def test_must_fail_actual_checkpoint_source_is_one_original_event(self):
        root = Path(os.environ.get('FN_PROOF_CHECKPOINT_SOURCE_ROOT',
                                   Path(__file__).resolve().parents[1]))
        source = root / 'tests/checkpoint-carrier-unit.lisp'
        if not source.is_file():
            self.skipTest('set FN_PROOF_CHECKPOINT_SOURCE_ROOT to the actual checkpoint fixture checkout')
        names, hashes, text = repl.source_event_inventory(source, root)
        forms = repl.forms(text)
        original = next(form for form in forms if repl.form_head(form) == 'must-fail')
        expected = f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {original}))'
        self.assertEqual(repl.per_event_steps(original, 2000000, 20, names), expected)
        hoisted, body = repl.encapsulated(text, source.parent, set(), 20, 2000000, names)
        self.assertIn(expected, body)
        self.assertEqual(expected.count('(with-prover-step-limit '), 1)
        self.assertIn(':expected :soft :check-expansion t', expected)
        self.assertTrue(any('std/testing/must-fail' in form for form in hoisted))

    def test_must_fail_final_result_still_controls_refusal(self):
        # Parser controls only: expected inner errors are not outer failures.
        caught = 'ACL2 Error in inner event\nSummary\nForm: (MUST-FAIL ...)\nTime: 0.01 seconds\n'
        self.assertFalse(repl.errored(caught))
        self.assertTrue(repl.errored(caught + 'ACL2 Error in MUST-FAIL: expected failure but command succeeded\n'))
        original = '(must-fail (thm nil) :expected :soft :check-expansion t)'
        wrapped = repl.per_event_steps(original, 2000000, 20)
        self.assertEqual(wrapped, f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {original}))')
        self.assertEqual(wrapped.count('with-prover-step-limit'), 1)
        with self.assertRaises(ValueError):
            repl.per_event_steps('(must-fail-unreviewed (thm nil))', 2000000, 20)

    def test_macro_time_cap(self):
        form = '(fn2-machines-preserves example)'
        self.assertEqual(repl.per_event_steps(form, 2000000, 20),
                         f'(with-prover-step-limit 2000000 t (with-prover-time-limit 20 {form}))')

    def test_default_and_generated_event(self):
        form = '(make-event (value (list (quote defthm) (quote generated) t)))'
        self.assertEqual(repl.per_event_steps(form, 10), f'(with-prover-step-limit 10 t {form})')
        self.assertEqual(repl.encapsulated('(local (thm t))', Path('.'), set(), 20)[1],
                         '(encapsulate ()\n(with-prover-time-limit 20 (local (thm t)))\n)')


if __name__ == '__main__':
    unittest.main()
