"""The completed reader family is a structural substitution, with proof edges."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import ledger
from history_reader_rewrite import replace_calls, carried_exec_definition, replace_dispatch_targets


def read(text):
    return [f for f, _ in ledger.Reader(text).top_level()]


class HistoryReaderRewrite(unittest.TestCase):
    def test_dispatch_targets_are_literal_and_scoped(self):
        text = "(call 'old) (other 'old) '(call 'old) ; old\n"
        self.assertEqual(replace_dispatch_targets(text, 'call', {'old': 'new'}),
                         "(call 'new) (other 'old) '(call 'old) ; old\n")

    def test_carried_execution_keeps_logical_body(self):
        text = '(defun step (s) (declare (xargs :guard (statep s))) (old s))'
        got = read(carried_exec_definition(text, '(carriedp s)', {'old': 'resident'}))[0]
        self.assertEqual(got[3][1][-1], read('(and (statep s) (carriedp s))')[0])
        self.assertEqual(got[-1], read('(mbe :logic (old s) :exec (resident s))')[0])

    def test_nested_calls_and_quotes(self):
        self.assertEqual(
            replace_calls('(old (other s) hist) \'(old s) (quote (other s))',
                          {'old': 'served', 'other': 'resident'},
                          {'old': ['s', 'fn-hist'], 'other': ['s']}),
            '(served (resident s fn-hist) hist) \'(old s) (quote (other s))')

    def test_every_completion_body_and_equality(self):
        references = {}
        for book in ('owner-commit-carried', 'owner-refresh-indexed',
                     'identity-retain-carried', 'owner-parse-carried'):
            references.update({str(f[1]): f for f in read((ROOT / 'books' / (book + '.lisp')).read_text())
                               if isinstance(f, list) and f and f[0] == 'defun'})
        events = read((ROOT / 'books/history-served-finish.lisp').read_text())
        clones = {str(f[1]): f for f in events if isinstance(f, list) and f and f[0] == 'defun'}
        names = {str(f[1]) for f in events if isinstance(f, list) and len(f) > 1 and f[0] == 'defthm'}
        guards = {str(f[1]) for f in events if isinstance(f, list) and len(f) > 1 and f[0] == 'verify-guards'}
        mapping = {'fn-' + n.removeprefix('fn-hsv-'): n for n in clones}
        mapping['fn-ccar-completion-record'] = 'fn-hist-completion-record'
        formals = {n: [str(a) for a in references[n][2]] for n in mapping}
        self.assertEqual(len(clones), 13)
        for old, new in mapping.items():
            if new == 'fn-hist-completion-record':
                continue
            with self.subTest(reader=new):
                expected = read(replace_calls(ledger.source_text(references[old][4]), mapping, formals))[0]
                self.assertEqual(clones[new][4], expected)
                self.assertIn(new + '-is-reference', names)
                self.assertIn(new, guards)


if __name__ == '__main__':
    unittest.main()
