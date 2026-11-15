"""Source-only contract checks; ACL2 guard/equality admission remains required."""
import unittest
import sys
REQUIRE_METADATA = "--metadata-projection" in sys.argv
if REQUIRE_METADATA:
    sys.argv.remove("--metadata-projection")
from pathlib import Path
from lisp_source import forms, read_sexp, generated_definition_expansion
import ledger
import host_check


def parsed(text):
    return [read_sexp(x) for x in forms(text)]


def all_defuns(x):
    if not isinstance(x, list):
        return []
    if x[:1] == ['defun']:
        return [x]
    return [f for child in x for f in all_defuns(child)]


def declaration(path, name):
    return next(x for x in parsed(Path(path).read_text())
                if isinstance(x, list) and x[:2] == ['defcolumns-predicate', name])


def public_body(d):
    return ['and'] + d[d.index(':shape') + 1] + d[d.index(':tests') + 1]


CASES = [('books/runs.lisp', 'fn2-run-buildp'),
         ('books/checkpoint.lisp', 'fn2-checkpoint-slotp')]


class Carried(unittest.TestCase):
    def test_fixture_local_stobj_bindings(self):
        tree = parsed(Path('tests/columns-carried-unit.lisp').read_text())
        def bindings(x):
            if not isinstance(x, list):
                return []
            own = [x] if x[:1] == ['with-local-stobj'] else []
            return own + [b for child in x for b in bindings(child)]
        found = bindings(tree)
        self.assertEqual(len(found), 5)
        for binding in found:
            self.assertEqual(binding[2][0], 'mv-let')
            self.assertIn(binding[1], binding[2][1])
        # Direct nesting was the actual first translation refusal.
        broken = ['with-local-stobj', 'outer', ['with-local-stobj', 'inner']]
        self.assertNotEqual(broken[2][0], 'mv-let')

    def test_checked_public_behavior_unchanged(self):
        for path, name in CASES:
            old = Path('tools/fixtures/columns-carried-baseline.lisp').read_text()
            f = next(x for x in parsed(old) if isinstance(x, list) and x[:2] == ['defun', name])
            d = declaration(path, name)
            self.assertEqual(f[2], d[2])
            self.assertEqual(f[-1], public_body(d))
            # Dropping either a shape or a bound must break public equivalence.
            for key in (':shape', ':tests'):
                mutated = list(d)
                i = d.index(key) + 1
                mutated[i] = d[i][1:]
                self.assertNotEqual(f[-1], public_body(mutated))

    def test_actual_callers_carry_exact_shapes(self):
        required = ['books/checkpoint-metadata-manifest.lisp', 'books/checkpoint-summary-authority-live.lisp', 'books/checkpoint-summary-authority-state.lisp']
        if not all(Path(p).exists() for p in required):
            if REQUIRE_METADATA:
                self.fail('Required late metadata projection consumers are missing')
            self.skipTest('REQUIRED later gate: run with --metadata-projection in composed metadata tree')
        for path, name, provider in [
            ('books/checkpoint-metadata-manifest.lisp', 'fn2-run-buildp', 'books/runs.lisp'),
            ('books/checkpoint-summary-authority-live.lisp', 'fn2-checkpoint-slotp', 'books/checkpoint.lisp'),
            ('books/checkpoint-summary-authority-state.lisp', 'fn2-checkpoint-slotp', 'books/checkpoint.lisp')]:
            shape = declaration(provider, name)
            shape = shape[shape.index(':shape') + 1]
            candidates = [x for x in all_defuns(parsed(Path(path).read_text()))
                          if name + '-carried' in str(x)]
            self.assertEqual(len(candidates), 1)
            for premise in shape:
                self.assertIn(str(premise), str(candidates[0][3]))

    def test_shared_inventory_and_cost_expansion(self):
        for path, name in CASES:
            text = Path(path).read_text()
            d = declaration(path, name)
            expanded = generated_definition_expansion(d)
            names = {x[1] for x in expanded}
            self.assertEqual(names, {name, name + '-carried', name + '-carried-equivalence'})
            self.assertEqual(expanded[0][-1], public_body(d))
            self.assertEqual(expanded[1][-1], ['and'] + d[d.index(':tests') + 1])
            inventory = {str(f[1]) for f, _ in ledger.source_events(ledger.Reader(text).top_level())
                         if ledger.head(f) in ('defun', 'defthm')}
            self.assertTrue(names <= inventory)
            self.assertTrue({name, name + '-carried'} <= host_check.world_names(text))

    def test_one_generator_retains_checks_and_named_equivalence(self):
        s = Path('books/columns.lisp').read_text()
        for needle in ('(and ,@shape ,@tests)', ':guard (and ,@shape)',
                       '(and ,@tests)', '"-CARRIED-EQUIVALENCE"',
                       '(equal (,name ,@formals) (,carried ,@formals))', ':rule-classes nil'):
            self.assertIn(needle, s)


if __name__ == '__main__':
    unittest.main()
