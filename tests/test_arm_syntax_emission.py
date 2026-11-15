"""Internal syntax/literal data boundaries in whole-arm proof proposals."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parents[1] / 'meta/emit'))
from emit_lean import Atom, List, val
from emit_arm_syntax import expr_val, phase_val
from served_proof_gen import step_to_lean, term_to_lean, codes_opt_lean


def symbol(package, name):
    atom = Atom(':' + name if package == 'KEYWORD' else name)
    atom.symbol_package, atom.symbol_name = package, name
    return atom


class ArmSyntaxEmission(unittest.TestCase):
    def test_variable_and_quoted_value_are_separate(self):
        x = symbol('ACL2', ':SIZE')
        quoted = List([symbol('COMMON-LISP', 'QUOTE'), x])
        self.assertIn('(Val.sym "ACL2:::SIZE")', expr_val(quoted))
        self.assertIn('(Val.sym "QUOTE")', expr_val(quoted))
        local = symbol('ACL2', 'X')
        self.assertEqual(expr_val(local), '(Val.sym "X")')
        self.assertEqual(val(local), '(Val.sym "ACL2::X")')
        self.assertIn('(Val.sym "X")', step_to_lean(('let', 'Y', local)))
        self.assertIn('(Val.sym "ACL2::X")', term_to_lean(('quote', local)))
        self.assertIn('(Val.sym "ACL2::X")', codes_opt_lean([local]))

    def test_case_keys_are_data(self):
        key = symbol('ACL2', 'X')
        form = List([symbol('COMMON-LISP', 'CASE'), key,
                     List([List([key]), Atom('7')]),
                     List([symbol('COMMON-LISP', 'OTHERWISE'), Atom('8')])])
        result = expr_val(form)
        self.assertIn('(Val.sym "ACL2::X")', result)
        self.assertIn('(Val.sym "X")', result)
        self.assertIn('(Val.sym "OTHERWISE")', result)
        phase = List([Atom(':CASE'), key, List([List([key]), Atom(':READY')])])
        self.assertIn('(Val.sym "ACL2::X")', phase_val(phase))

    def test_synthetic_internal_names_are_explicit(self):
        synthetic = List([Atom('QUOTE'), Atom('1')])
        self.assertEqual(expr_val(synthetic), '(Val.ofList [(Val.sym "QUOTE"), (Val.int 1)])')
        self.assertEqual(expr_val(Atom('ID')), '(Val.sym "ID")')
        with self.assertRaises(SystemExit):
            val(Atom('ID'))


if __name__ == '__main__':
    unittest.main()
