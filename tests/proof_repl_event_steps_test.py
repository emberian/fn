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
