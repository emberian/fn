"""Check the shared resource-hint delta without launching ACL2."""
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lisp

BASELINE = '9666d7ba6'
HELPERS = {'fn2-arms-resource-stobj-callees', 'fn2-arms-resource-callees'}


def tree(node):
    if isinstance(node, lisp.Pre):
        if (node.prefix == ',@' and isinstance(node.node, lisp.Lst)
                and lisp.flat(node.node.items[0]) == 'fn2-arms-resource-callees'):
            return None
        return (node.prefix, tree(node.node))
    if isinstance(node, lisp.Lst):
        return tuple(value for child in node.items if (value := tree(child)) is not None)
    return node.text if isinstance(node, lisp.Str) else node.low


class ResourceOpacity(unittest.TestCase):
    def test_only_proof_hint_splices_change(self):
        before = subprocess.run(
            ['git', 'show', f'{BASELINE}:books/machine-arms.lisp'], cwd=ROOT,
            check=True, stdout=subprocess.PIPE).stdout
        old = lisp.parse(before)
        new = lisp.parse(ROOT / 'books/machine-arms.lisp')
        current = [form for form in new.forms if not (
            isinstance(form, lisp.Lst) and len(form.items) > 1
            and lisp.flat(form.items[0]) == 'defun'
            and lisp.flat(form.items[1]) in HELPERS)]
        self.assertEqual([tree(form) for form in old.forms], [tree(form) for form in current])

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL needed for metadata controls')
    def test_metadata_filter_keeps_issuing_strategy(self):
        result = subprocess.run(
            ['sbcl', '--noinform', '--script', 'tests/arm-resource-opacity-controls.lsp'],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('BT RESOURCE OPACITY SOURCE CONTROLS PASS', result.stdout)


if __name__ == '__main__':
    unittest.main()
