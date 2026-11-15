"""Connected source controls; no ACL2 admission or executable PASS is implied."""
from pathlib import Path
import unittest
import lisp_rewrite as lisp

class CreditSource(unittest.TestCase):
    def test_same_profile_and_actual_child_geometry(self):
        source = Path('books/checkpoint-working-credit-init.lisp').read_text()
        lisp.parse(source)
        self.assertIn('(defun fn2-checkpoint-working-credit-init (profile fn2-core)', source)
        self.assertIn('(fn2-profilep profile)', source)
        self.assertIn('profile (fn2-commit-rows fn2-commit)', source)
        self.assertIn('(fn2-commit-io-rows fn2-commit-io) fn2-pool)', source)

    def test_one_fit_before_only_configuration_mutation(self):
        source = Path('books/checkpoint-working-credit.lisp').read_text()
        parsed = lisp.parse(source)
        form = next(source[n.start:n.end] for n in parsed.forms
                    if source[n.start:n.end].startswith('(defun fn2-checkpoint-working-credit-configure'))
        self.assertLess(form.index('(fn2-checkpoint-service-demand-vector profile fn2-pool)'),
                        form.index('(fn2-checkpoint-working-credit-fitp 0 groups service fn2-pool)'))
        self.assertLess(form.index('(fn2-checkpoint-working-credit-fitp 0 groups service fn2-pool)'),
                        form.index('(fn2-pool-credit-configure groups fn2-pool)'))
        self.assertEqual(form.count('(fn2-pool-credit-configure groups fn2-pool)'), 1)
        self.assertNotIn('(update-', form)
        self.assertNotIn('(fn2-pool-reserve', form)

    def test_total_class_loops_and_actual_controls(self):
        source = Path('books/checkpoint-working-credit.lisp').read_text()
        self.assertEqual(source.count('(if (not (and (natp class) (< class (nfix (fn2-pool-nclasses fn2-pool)))))'), 3)
        fixture = Path('tests/checkpoint-working-credit-configure-unit.lisp').read_text()
        lisp.parse(fixture)
        for control in ['(eq protected-only :exhausted)', '(eq malformed :geometry)',
                        '(eq configured :ok)', '*fn2-checkpoint-working-window-count*',
                        '(fn2-pool-reservable-count 0 fn2-pool)']:
            self.assertIn(control, fixture)
        self.assertNotIn(' 29', fixture)

if __name__ == '__main__':
    unittest.main()
