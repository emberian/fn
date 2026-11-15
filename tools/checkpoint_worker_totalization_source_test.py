"""Source controls for the exact seven-worker guard-preserving transformation."""
from pathlib import Path
import copy
import hashlib
import json
import unittest
import checkpoint_worker_totalize as transform
import lisp_rewrite as lisp

ROWS = json.loads(transform.RECEIPT.read_text())['functions']

def calls(node, name):
    found = []
    if isinstance(node, lisp.Lst):
        if node.items and getattr(node.items[0], 'text', '') == name:
            found.append(node)
        for child in node.items:
            found.extend(calls(child, name))
    elif isinstance(node, lisp.Pre):
        found.extend(calls(node.node, name))
    return found

class WorkerTotality(unittest.TestCase):
    def test_full_form_reversible_and_guard_domain_subset(self):
        self.assertEqual(len(ROWS), 7)
        for row in ROWS:
            transform.validate_guard(row)
            source = Path(row['path']).read_text()
            node = transform.definition(source, row['name'])
            self.assertEqual(transform.restored(source[node.start:node.end], row), row['original_form'])

    def test_weakened_natural_guard_and_success_fallback_refused(self):
        row = copy.deepcopy(ROWS[1])
        row['original_form'] = row['original_form'].replace('(natp i)', '', 1)
        row['original_guard'] = row['original_guard'].replace('(natp i)', '', 1)
        row['original_sha256'] = hashlib.sha256(row['original_form'].encode()).hexdigest()
        with self.assertRaises(AssertionError):
            transform.validate_guard(row)
        current = transform.transformed(ROWS[1])
        current = current[:current.rindex(':bounds')] + current[current.rindex(':bounds'):].replace(':bounds', ':ok', 1)
        with self.assertRaises(AssertionError):
            transform.restored(current, ROWS[1])

    def test_actual_public_entry_arguments_and_factory_ranges(self):
        root = Path('books/checkpoint-working-reserve.lisp').read_text()
        future = Path('books/checkpoint-future-working.lisp').read_text()
        for source, caller, helper in [
            (root, 'fn2-checkpoint-root1-reserve', 'fn2-checkpoint-windows-reserve-loop'),
            (root, 'fn2-checkpoint-root1-reserve', 'fn2-checkpoint-working-credit-fitp'),
            (future, 'fn2-checkpoint-future-reserve-with-credit', 'fn2-checkpoint-future-reserve-loop')]:
            found = calls(transform.definition(source, caller), helper)
            self.assertEqual(len(found), 1)
            self.assertEqual(found[0].items[1].text, '0')
        factories = [n for n in lisp.parse(future).forms if isinstance(n, lisp.Lst)
                     and getattr(n.items[0], 'text', '') == 'fn2-checkpoint-future-transfer-interface']
        self.assertEqual([(n.items[2].text, n.items[3].text, n.items[4].text) for n in factories],
                         [('1', '5', 'nil'), ('1', '5', 't'), ('5', '8', 'nil'), ('5', '8', 't')])
        release = transform.definition(future, 'fn2-checkpoint-future-release-one')
        call = calls(release, 'fn2-checkpoint-future-no-loansp')[0]
        self.assertEqual([n.text for n in call.items[1:3]], ['0', 'left'])
        caller_equations = transform.caller_fixture(ROWS)
        self.assertIn('(posp left)', caller_equations)
        self.assertEqual(len(lisp.parse(caller_equations).forms), 7)
        self.assertIn('unreachable-in-composition: public admission', root)

    def test_prepared_logical_equations_are_generated_from_actual_source(self):
        expected = transform.fixture(ROWS) + '\n; Actual public preconditions and factory instantiations, extracted from source.\n' + transform.caller_fixture(ROWS)
        actual = Path('tests/checkpoint-worker-totalization-unit.lisp').read_text()
        self.assertEqual(actual, expected)
        self.assertEqual(len(lisp.parse(actual).forms), 41)
        self.assertNotIn('(defun ', actual)  # no legacy implementation twin

if __name__ == '__main__':
    unittest.main()
