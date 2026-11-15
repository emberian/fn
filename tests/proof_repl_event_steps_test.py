from pathlib import Path
import sys
import unittest
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
