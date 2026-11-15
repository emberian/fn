"""Source contract: only the existing row equation's proof theory changes."""
import hashlib
import json
import unittest
from pathlib import Path
from lisp_source import forms, read_sexp

BASE = json.loads(Path('tools/fixtures/pool-row-step-proof-baseline.json').read_text())


def inventory(text):
    found = []
    def mask(x):
        if not isinstance(x, list):
            return x
        if x[:2] == ['defthm', 'fn2-pool-row-invariantp-step']:
            found.append(x)
            return ['row-step-proof-here']
        return [mask(v) for v in x]
    masked = mask([read_sexp(f) for f in forms(text)])
    assert len(found) == 1
    return found[0], hashlib.sha256(json.dumps(masked, sort_keys=True).encode()).hexdigest()


class RowProof(unittest.TestCase):
    def test_no_runtime_statement_or_other_event_changes(self):
        theorem, digest = inventory(Path('books/pool.lisp').read_text())
        self.assertEqual(digest, BASE['remaining_ast_sha256'])
        i = theorem.index(':hints')
        self.assertEqual(theorem[:i], BASE['theorem'][:BASE['theorem'].index(':hints')])
        changed = list(theorem)
        changed[2] = ['implies', 'nil', theorem[2]]
        self.assertNotEqual(changed[:i], BASE['theorem'][:BASE['theorem'].index(':hints')])

    def test_explicit_small_theory_keeps_both_actual_definitions(self):
        theorem, _ = inventory(Path('books/pool.lisp').read_text())
        hint = theorem[theorem.index(':hints') + 1]
        self.assertEqual(hint, [[':in-theory',
            ['union-theories', ['quote', ['fn2-pool-row-invariantp', 'fn2-pool-row-okp', 'zp']],
             ['theory', ['quote', 'minimal-theory']]]]])


if __name__ == '__main__':
    unittest.main()
