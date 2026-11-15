"""Package identity controls for legacy world literals, without loading ACL2."""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT = Path(__file__).parents[1]
SPEC = importlib.util.spec_from_file_location('emit_lean', ROOT / 'meta/emit/emit_lean.py')
e = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(e)


class SymbolLiterals(unittest.TestCase):
    def test_metadata_precedes_atom_syntax(self):
        for name in ('NIL', 'T', '123', '#\\A', ':SIZE', 'COMMON-LISP::CAR', ''):
            atom = e.Atom(name)
            atom.symbol_package, atom.symbol_name = 'ACL2', name
            self.assertEqual(e.val(atom), '(Val.sym ' + e.lean_str('ACL2::' + name) + ')')
        self.assertNotEqual(e.symbol_value('KEYWORD', 'SIZE'), e.symbol_value('ACL2', ':SIZE'))
        self.assertNotEqual(e.symbol_value('COMMON-LISP', 'CAR'), e.symbol_value('ACL2', 'CAR'))
        self.assertEqual(e.symbol_value('COMMON-LISP', 'NIL'), 'Val.nil')

    def test_trailer_validation(self):
        for trailer in ('(:FN2-SYMBOL-PACKAGES)',
                        '(:FN2-SYMBOL-PACKAGES (("X" "OTHER" "X")))',
                        '(:FN2-SYMBOL-PACKAGES (("X" "ACL2" "X") ("X" "KEYWORD" "X")))',
                        '(:FN2-SYMBOL-PACKAGES ((X "ACL2" "X")))'):
            with self.assertRaises(SystemExit):
                e.read_all('(X) ' + trailer)
        with self.assertRaises(SystemExit):
            e.val(e.Atom('CAR'))
        self.assertEqual(e.val(e.Atom(':SIZE')), '(Val.sym ":SIZE")')

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for the live printer control')
    def test_live_printer_packages_and_syntactic_names(self):
        source = (ROOT / 'meta/emit/print-world.lisp').read_text()
        helper = source[source.index('(defun meta-symbol-packages'):source.index('(defun meta-print-world (path)')]
        program = '''(make-package "ACL2" :use '("COMMON-LISP"))
(in-package "ACL2")
''' + helper + '''
(let* ((*package* (find-package "ACL2")) (*print-case* :upcase)
       (*print-pretty* nil) (*print-escape* t)
       (world (list 'car :size (intern ":SIZE") (intern "123")
                    (intern "a | b") (intern "a | b" "KEYWORD")
                    (intern "a\\\\\\\"b") nil t)))
  (prin1 world) (terpri) (prin1 (meta-symbol-packages world)) (terpri))
'''
        result = subprocess.run(['sbcl', '--noinform', '--disable-debugger', '--script', '/dev/stdin'],
                                input=program, text=True, capture_output=True, timeout=10, check=True)
        forms = e.read_all(result.stdout)
        self.assertEqual(len(forms), 1)
        row = forms[0]
        self.assertEqual(str(row[0]), 'CAR')  # syntactic names do not gain package prefixes
        self.assertEqual(e.term(e.List([row[0], e.Atom('X')])), '(.app "CAR" [(.var "X")])')
        for atom, package, name in zip(row,
                ['COMMON-LISP', 'KEYWORD', 'ACL2', 'ACL2', 'ACL2', 'KEYWORD', 'ACL2', 'COMMON-LISP', 'COMMON-LISP'],
                ['CAR', 'SIZE', ':SIZE', '123', 'a | b', 'a | b', 'a\\"b', 'NIL', 'T']):
            self.assertEqual((atom.symbol_package, atom.symbol_name), (package, name))
            self.assertEqual(e.val(atom), e.symbol_value(package, name))


if __name__ == '__main__':
    unittest.main()
