"""Whole generator identity and actual factory expansion controls; no ACL2."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lisp
import proof_repl
BASELINE = '6d678f2c3'


def tree(n):
    if isinstance(n, lisp.Pre):
        if n.prefix == ',@' and lisp.flat(n.node) == '(fn2-machine-initial-row-facts name cols)':
            return None
        return n.prefix, tree(n.node)
    if isinstance(n, lisp.Lst):
        items, result, i = n.items, [], 0
        while i < len(items):
            if lisp.flat(items[i]) in {':hints', ':guard-hints'}:
                i += 2
            else:
                value = tree(items[i])
                if value is not None:
                    result.append(value)
                i += 1
        return tuple(result)
    return n.text if isinstance(n, lisp.Str) else n.low


class MachineInitializerHints(unittest.TestCase):
    def baseline(self, path):
        return subprocess.check_output(['git', 'show', f'{BASELINE}:{path}'], cwd=ROOT)

    def test_entire_machine_generator_changes_only_proof_hints_and_import(self):
        old = lisp.parse(self.baseline('books/machines.lisp'))
        new = lisp.parse(ROOT / 'books/machines.lisp')
        imports = [f for f in new.forms if lisp.flat(f) == '(include-book "columns-call-guards")']
        self.assertEqual(len(imports), 1)
        self.assertEqual([tree(f) for f in old.forms],
                         [tree(f) for f in new.forms if f not in imports and not (
                             isinstance(f, lisp.Lst) and lisp.flat(f.items[0]) == 'defun'
                             and lisp.flat(f.items[1]) in {'fn2-machine-row-values',
                                                         'fn2-machine-initial-row-facts'})])
        factory = lisp.match(None, new.forms, deep=False, head='defun',
                             name='fn2-machine-prepare-events')[0].node
        self.assertEqual(len(lisp.match(None, [factory], head='fn2-columns-call-guard-hint')), 7)

    def test_full_rich_conn_schema_and_custom_initial_value_lowering_unchanged(self):
        self.assertEqual(self.baseline('books/conn-schema.lisp'), (ROOT / 'books/conn-schema.lisp').read_bytes())
        old = lisp.parse(self.baseline('books/machines.lisp'))
        new = lisp.parse(ROOT / 'books/machines.lisp')
        a = lisp.match(None, old.forms, deep=False, head='defun', name='fn2-machine-initial-values')
        b = lisp.match(None, new.forms, deep=False, head='defun', name='fn2-machine-initial-values')
        self.assertEqual(lisp.flat(a[0].node), lisp.flat(b[0].node))

    def test_helper_include_is_acyclic_and_uses_declared_owner(self):
        helper = proof_repl.include_graph(ROOT, 'books/columns-call-guards')
        self.assertNotIn('books/machines', helper)
        graph = proof_repl.include_graph(ROOT, 'books/machines')
        self.assertIn('books/columns-call-guards', graph['books/machines'])

    def factory_control(self, candidate=None):
        with tempfile.NamedTemporaryFile(suffix='.lisp') as baseline:
            baseline.write(self.baseline('books/machines.lisp'))
            baseline.flush()
            command = ['sbcl', '--noinform', '--script',
                       'tests/machine-initializer-hint-controls.lsp', baseline.name]
            if candidate is not None:
                command.append(str(candidate))
            return subprocess.run(command, cwd=ROOT, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for factory controls')
    def test_actual_factory_expansions_and_pure_initializers(self):
        r = self.factory_control()
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn('MACHINE INITIALIZER HINT SOURCE CONTROLS PASS', r.stdout)

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for factory controls')
    def test_real_controls_reject_missing_row_premises_and_dropped_setters(self):
        source = (ROOT / 'books/machines.lisp').read_text()
        premise = '(and (,wfp ,name) (natp slot) (< slot (,rows ,name)))'
        changes = [
            (premise, '(and (natp slot) (< slot (,rows ,name)))'),
            (premise, '(and (,wfp ,name) (< slot (,rows ,name)))'),
            (premise, '(and (,wfp ,name) (natp slot))'),
            ("name 'slot (fn2-machine-row-values cols)",
             "name 'slot (fn2-machine-row-values (cdr cols))")]
        for before, after in changes:
            with self.subTest(after=after), tempfile.NamedTemporaryFile(suffix='.lisp') as candidate:
                self.assertIn(before, source)
                candidate.write(source.replace(before, after, 1).encode())
                candidate.flush()
                result = self.factory_control(candidate.name)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('assertion', result.stdout.lower())


if __name__ == '__main__':
    unittest.main()
