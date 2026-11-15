"""Source controls for automatic public column guard boundaries; no ACL2."""
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lisp
BASELINE = 'd09ae7ad41055adfc77f30a980d84a9178706eba'


def tree(node):
    if isinstance(node, lisp.Pre):
        return node.prefix, tree(node.node)
    if isinstance(node, lisp.Lst):
        items = node.items
        if items and lisp.flat(items[0]) == 'xargs':
            result, i = [], 0
            while i < len(items):
                if lisp.flat(items[i]) == ':guard-hints':
                    i += 2
                else:
                    result.append(tree(items[i]))
                    i += 1
            return tuple(result)
        return tuple(tree(item) for item in items)
    return node.text if isinstance(node, lisp.Str) else node.low


def before(path):
    return lisp.parse(subprocess.check_output(['git', 'show', f'{BASELINE}:{path}'], cwd=ROOT))


class ColumnCallGuards(unittest.TestCase):
    def test_generated_fold_events_change_only_guard_hints(self):
        def factory(forms):
            return [tree(form) for form in forms if isinstance(form, lisp.Lst)
                    and len(form.items) > 1 and lisp.flat(form.items[1]) == 'fn2-rf-events']
        self.assertEqual(factory(before('books/runs-schema.lisp').forms),
                         factory(lisp.parse(ROOT / 'books/runs-schema.lisp').forms))

    def test_all_actual_ribbon_definitions_and_guards_unchanged(self):
        def definitions(forms):
            return [tree(form) for form in forms if isinstance(form, lisp.Lst)
                    and lisp.flat(form.items[0]) in {'defun', 'defun-nx', 'defmacro', 'defthm', 'defthm-owed'}]
        self.assertEqual(definitions(before('books/ribbon.lisp').forms),
                         definitions(lisp.parse(ROOT / 'books/ribbon.lisp').forms))

    def test_existing_hint_constructor_and_explicit_hints_unchanged(self):
        original = before('books/columns-guard-hints.lisp').forms
        new = lisp.parse(ROOT / 'books/columns-guard-hints.lisp').forms
        self.assertEqual([tree(f) for f in original], [tree(f) for f in new])
        old = before('books/ribbon.lisp').forms
        new = lisp.parse(ROOT / 'books/ribbon.lisp').forms
        changed = {'fn2-ribbon-hash-loop', 'fn2-ribbon-emit-bytes', 'fn2-ribbon-add'}
        def explicit(forms):
            return {lisp.flat(f.items[1]): lisp.flat(f) for f in forms
                    if isinstance(f, lisp.Lst) and len(f.items) > 1 and lisp.flat(f.items[0]) == 'defun'
                    and lisp.flat(f.items[1]) not in changed}
        self.assertEqual(explicit(old), explicit(new))

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source metadata control')
    def test_signature_and_contract_filter_and_explicit_enables(self):
        result = subprocess.run(['sbcl', '--noinform', '--script', 'tests/columns-call-guard-controls.lsp'],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('COLUMN CALL GUARD SOURCE CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()
