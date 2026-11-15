"""Check the ownership move and guard-only repair, not ACL2 admission."""
import hashlib
import json
import unittest
from pathlib import Path
import ledger

BASE = json.loads(Path('tools/fixtures/vocab-harvest-guard-baseline.json').read_text())
PATHS = ('books/vocab.lisp', 'books/borrow-accounting.lisp')


def nodes(x):
    if isinstance(x, list):
        yield x
        for y in x:
            yield from nodes(y)


def inventory(texts):
    functions, theorems, locations = {}, {}, {}
    for path, text in texts.items():
        for x in nodes(ledger.read_forms(text)):
            if len(x) < 3 or not isinstance(x[1], ledger.Sym):
                continue
            if x[0] == 'defun':
                declarations = [a for a in x[3:] if ledger.head(a) == 'declare']
                guards = []
                stobjs = []
                for d in declarations:
                    for a in d[1:]:
                        if ledger.head(a) == 'xargs':
                            options = ledger.keyword_plist(a[1:])
                            if ':guard' in options:
                                guards.append(options[':guard'])
                            if ':stobjs' in options:
                                stobjs.append(options[':stobjs'])
                functions[str(x[1])] = [x[2], x[-1], guards, stobjs]
            elif x[0] == 'defthm':
                options = ledger.keyword_plist(x[3:])
                theorems[str(x[1])] = [x[2], options.get(':rule-classes')]
                locations.setdefault(str(x[1]), []).append(path)
    return functions, theorems, locations


class HarvestGuard(unittest.TestCase):
    def test_existing_runtime_guards_and_public_statements_unchanged(self):
        f, t, _ = inventory({p: Path(p).read_text() for p in PATHS})
        digest = lambda x: hashlib.sha256(json.dumps(x, sort_keys=True).encode()).hexdigest()
        self.assertEqual({k: digest(v) for k, v in f.items()}, BASE['functions'])
        self.assertEqual({k: digest(t[k]) for k in BASE['theorems']}, BASE['theorems'])
        mutant = dict(t)
        mutant['fn2-ops-peek-posted-slot'] = [['implies', 'nil', t['fn2-ops-peek-posted-slot'][0]], t['fn2-ops-peek-posted-slot'][1]]
        self.assertNotEqual(mutant['fn2-ops-peek-posted-slot'], BASE['moved_contract'])

    def test_one_producer_owned_contract_before_real_guard_caller(self):
        texts = {p: Path(p).read_text() for p in PATHS}
        _, _, locations = inventory(texts)
        self.assertEqual(locations['fn2-ops-peek-posted-slot'], ['books/vocab.lisp'])
        s = texts['books/vocab.lisp']
        self.assertLess(s.index('(defun fn2-ops-peek-posted'), s.index('(defthm fn2-ops-peek-posted-slot'))
        self.assertLess(s.index('(defthm fn2-ops-peek-posted-slot'), s.index('(defun fn2-harvest-next'))
        self.assertNotIn('(include-book "borrow-accounting")', s)
        self.assertIn('fn2-columns-scalar-frame-hint', s)
        self.assertIn('fn2-ops-latch-peer-posted-frame', s)

    def test_only_fifo_length_observation_opted_in_and_bounds_explicitly_used(self):
        parsed = ledger.read_forms(Path('books/vocab.lisp').read_text())
        harvest = next(x for x in nodes(parsed) if x[:2] == ['defun', 'fn2-harvest-next'])
        calls = [x for x in nodes(harvest[3]) if x[:1] == ['fn2-columns-scalar-frame-hint']]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][2], ['quote', ['fn2-ops-posted-fifo-length']])
        self.assertEqual(calls[0][3], ['quote', ['fn2-ops-peek-posted', 'fn2-ops-latch-peer']])
        self.assertIn(':use', str(harvest[3]))
        self.assertIn('fn2-ops-peek-posted-post-bounds', str(harvest[3]))

    def test_frame_use_covers_both_actual_marked_cell_states(self):
        parsed = ledger.read_forms(Path('books/vocab.lisp').read_text())
        harvest = next(x for x in nodes(parsed) if x[:2] == ['defun', 'fn2-harvest-next'])
        uses = [x for x in nodes(harvest[3])
                if x[:2] == [':instance', 'fn2-ops-latch-peer-posted-frame']]
        slot = ['mv-nth', 1, ['fn2-ops-peek-posted', 'fn2-ops']]
        self.assertEqual(len(uses), 2)
        for cell in (0, 1):
            expected = [':instance', 'fn2-ops-latch-peer-posted-frame',
                        ['cell', cell], ['slot', slot],
                        ['fn2-ops', [f'fn2-ops-set-c{cell}-harvested', slot, 1, 'fn2-ops']]]
            self.assertIn(expected, uses)

    def test_no_invented_ring_invariant_and_all_posted_metadata_framed(self):
        _, t, _ = inventory({'books/vocab.lisp': Path('books/vocab.lisp').read_text()})
        fact = str(t['fn2-ops-peek-posted-post-bounds'][0])
        self.assertIn('fn2-opsp', fact)
        self.assertIn('fn2-ops-wfp', fact)
        self.assertIn('fn2-ops-peek-posted', fact)
        self.assertNotIn('semanticp', fact)
        frame = str(t['fn2-ops-latch-peer-posted-frame'][0])
        for field in ('fn2-ops-post-head', 'fn2-ops-post-count', 'fn2-ops-posted-fifo-length'):
            self.assertIn(field, frame)


if __name__ == '__main__':
    unittest.main()
