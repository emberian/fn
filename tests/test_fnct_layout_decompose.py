from pathlib import Path
import shutil
import subprocess
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
from fnct_layout_decompose import transform, MACRO, CHECK

ROOT = Path(__file__).resolve().parents[1]


class FnctLayoutDeclarations(unittest.TestCase):
    def test_transformation_identity_completeness_idempotence(self):
        current = (ROOT / 'books/consumer-codec.lisp').read_text()
        forms = lr.parse(current).forms
        calls = [n for n in forms if isinstance(n, lr.Lst) and n.items[0].low == 'fn2-fnct-deflayout']
        self.assertEqual(len(calls), 19)
        self.assertEqual(transform(current), current)
        missing = lr.write(current, [(calls[0].start, calls[0].end, '')])
        duplicate = lr.write(current, [(calls[0].start, calls[0].end, current[calls[0].start:calls[0].end] * 2)])
        table = next(n for n in forms if isinstance(n, lr.Lst) and n.items[0].low == 'defconst'
                     and n.items[1].low == '*fn2-fnct-codes*')
        row_list = table.items[2].node
        new_row = lr.write(current, [(row_list.end - 1, row_list.end - 1, '\n (19 :future ((v :u8)) nil)')])
        for mutant in [missing, duplicate, new_row]:
            with self.assertRaises(ValueError):
                transform(mutant)
        # Rebuild the old aggregate input using the exact unchanged lookup.
        lookup = next(n for n in forms if isinstance(n, lr.Lst) and n.items[0].low == 'defun'
                      and n.items[1].low == 'fn2-fnct-word-row')
        start = lookup.start
        check_at = current.index(CHECK, start)
        old = current[:start] + '(make-event (value `(progn ,@(fn2-fnct-deflayout-forms *fn2-fnct-codes*))))' + current[check_at + len(CHECK):]
        old += '\n' + current[lookup.start:lookup.end] + '\n'
        result = transform(old)
        self.assertEqual(transform(result), result)
        self.assertEqual(result.count(MACRO), 1)
        self.assertEqual([n.items[1].low for n in lr.parse(result).forms
                          if isinstance(n, lr.Lst) and n.items[0].low == 'fn2-fnct-deflayout'],
                         [n.items[1].low for n in calls])

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
    def test_actual_complete_generated_forms_and_inventory_controls(self):
        result = subprocess.run(['sbcl', '--noinform', '--script', 'tests/fnct-layout-controls.lsp'],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout[-5000:])
        self.assertIn('FNCT LAYOUT CONTROLS PASS: 19 declarations', result.stdout)


if __name__ == '__main__':
    unittest.main()
