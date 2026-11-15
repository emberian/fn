"""Source-only contract checks; ACL2 guard/equality admission remains required."""
import subprocess
import unittest
from pathlib import Path
from lisp_source import forms, read_sexp


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
    def test_checked_public_behavior_unchanged(self):
        for path, name in CASES:
            old = subprocess.check_output(['git', 'show', '53973df71:' + path], text=True)
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

    def test_one_generator_retains_checks_and_named_equivalence(self):
        s = Path('books/columns.lisp').read_text()
        for needle in ('(and ,@shape ,@tests)', ':guard (and ,@shape)',
                       '(and ,@tests)', '"-CARRIED-EQUIVALENCE"',
                       '(equal (,name ,@formals) (,carried ,@formals))', ':rule-classes nil'):
            self.assertIn(needle, s)


if __name__ == '__main__':
    unittest.main()
