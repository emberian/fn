from pathlib import Path
import sys
import unittest
from unittest.mock import Mock, patch
from types import SimpleNamespace
import tempfile
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
