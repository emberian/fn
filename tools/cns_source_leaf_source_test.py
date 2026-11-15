"""Exact served definitions and dependency ownership; no ACL2 execution."""
import hashlib
import json
from pathlib import Path
import unittest
import certs
import ledger

def converted(x):
    if isinstance(x, ledger.Sym):
        return str(x)
    if isinstance(x, str):
        return json.dumps(x)
    if isinstance(x, list):
        return [converted(v) for v in x]
    return x

ROOT = Path(__file__).resolve().parents[1]
BASE = json.loads((ROOT / 'tools/fixtures/cns-source-leaf-baseline.json').read_text())

def parsed(path):
    return [converted(x) for x in ledger.read_forms((ROOT / path).read_text())]

def keep(x):
    return (isinstance(x, list) and x and x[0] not in ['include-book', 'in-theory']
            and not (len(x) > 1 and x[0] in ['defun', 'fn2-pool-preserves']
                     and x[1] == 'fn2-rd-copy'))

def digest(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True).encode()).hexdigest()

READ_DIMENSIONS = [
    ['fn2-pool-dimensions', 'fn2-rd-octets', ':observations', [':data'],
     ':opaque', ['fn2-rd-copy', 'fn2-rd-entry-row']],
    ['fn2-pool-dimensions', 'fn2-read-octets-children', ':observations',
     [':rows', ':data'], ':opaque', ['fn2-rd-octets']],
]

def original_consumer_forms(path, forms):
    if path == 'books/machines-c-read.lisp':
        # Only these two reviewed interface requests postdate the extraction.
        # Check their complete inventory before comparing every original AST.
        additions = [x for x in forms if x[:1] == ['fn2-pool-dimensions']]
        if additions != READ_DIMENSIONS:
            raise ValueError('actual READ dimension request inventory changed')
        forms = [x for x in forms if x not in READ_DIMENSIONS]
    return [x for x in forms if keep(x)]

class SourceLeaves(unittest.TestCase):
    def test_existing_runtime_guards_and_claims_exact(self):
        for path, expected in BASE.items():
            if path != 'moved_forms':
                self.assertEqual([digest(x) for x in original_consumer_forms(path, parsed(path))], expected, path)

    def test_reviewed_read_additions_do_not_hide_request_mutations(self):
        import copy
        forms = parsed('books/machines-c-read.lisp')
        for mode in ['missing', 'observation', 'callee']:
            mutated = copy.deepcopy(forms)
            addition = next(x for x in mutated if x[:2] ==
                            ['fn2-pool-dimensions', 'fn2-read-octets-children'])
            if mode == 'missing':
                mutated.remove(addition)
            elif mode == 'observation':
                addition[3] = [':rows']
            else:
                addition[1] = 'fn2-read-value-children'
            with self.assertRaisesRegex(ValueError, 'inventory changed'):
                original_consumer_forms('books/machines-c-read.lisp', mutated)

    def test_copy_guard_mutation_breaks_exact_source_contract(self):
        import copy
        original = BASE['moved_forms'][0]
        mutated = copy.deepcopy(original)
        declaration = mutated[3][1]
        guard_at = declaration.index(':guard') + 1
        declaration[guard_at] = 't'
        self.assertNotEqual(digest(original), digest(mutated))

    def test_copy_has_single_exact_owner(self):
        definitions = []
        for path in (ROOT / 'books').glob('*.lisp'):
            text = path.read_text()
            if '(defun fn2-rd-copy ' in text:
                definitions.append(path.relative_to(ROOT).as_posix())
        self.assertEqual(definitions, ['books/pool-copy.lisp'])
        moved = [x for x in parsed('books/pool-copy.lisp')
                 if x[:1] in [['defun'], ['fn2-pool-preserves']]]
        self.assertEqual(moved, BASE['moved_forms'])
        self.assertIn(['in-theory', ['disable', 'fn2-rd-copy']], parsed('books/pool-copy.lisp'))
        self.assertIn(['in-theory', ['disable', 'fn2-rd-octets', 'fn2-rd-value']], parsed('books/machines-c-read.lisp'))

    def test_state_imports_only_own_declaration_dependencies(self):
        includes = [x[1] for x in parsed('books/cns-source-state.lisp') if x[:1] == ['include-book']]
        self.assertEqual(includes, ['"columns"', '"commit-geometry"'])
        closure = certs.closure(ROOT, 'books/cns-source-state')
        self.assertEqual(len(closure), 11)
        self.assertNotIn('books/machines-c-read', closure)

    def test_actual_copy_and_workspace_consumers_have_providers(self):
        copy_consumers = []
        for directory in ['books', 'tests']:
            for path in (ROOT / directory).glob('*.lisp'):
                text = path.read_text()
                if '(fn2-rd-copy ' in text and path.name != 'pool-copy.lisp':
                    book = path.relative_to(ROOT).with_suffix('').as_posix()
                    self.assertIn('books/pool-copy', certs.closure(ROOT, book), book)
                    copy_consumers.append(book)
        self.assertEqual(set(copy_consumers), {'books/machines-c-read', 'books/cns-source-raw',
                         'books/authority', 'books/cns', 'tests/cns-enum-whole-result-controls'})
        for book in ['books/cns-source-capture', 'books/cns-source-manifest',
                     'books/cns-source-raw', 'tests/cns-source-hash-interleave-unit']:
            self.assertIn('books/cns-source-workspace', certs.closure(ROOT, book), book)
        self.assertIn('  books/pool-copy \\\n', (ROOT / 'Makefile').read_text())

if __name__ == '__main__':
    unittest.main()
