"""Source consistency only: no ACL2 execution or runtime work-count claim."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr


def shape(n):
    if isinstance(n, lr.Str):
        return ('string', n.text)
    if isinstance(n, lr.Atom):
        return n.low
    if isinstance(n, lr.Pre):
        return (n.prefix, shape(n.node))
    return tuple(shape(c) for c in n.items)


def walk(n):
    yield n
    if isinstance(n, lr.Lst):
        for child in n.items:
            yield from walk(child)
    elif isinstance(n, lr.Pre):
        yield from walk(n.node)


def check_source(layout, runs):
    sources = ((layout, '*fn2-codec-decode-fuel*', '4096',
                '(,step base slot gen off end okind oslot ogen *fn2-codec-decode-fuel* fn2-fields fn2-pool)'),
               (runs, '*fn2-ov-search-steps*', '40',
                '(fn2-ov-search *fn2-ov-search-steps* 0 (fn2-overlays-count o fn2-overlays) o eb qbase qk qs qg fn2-overlays fn2-overlay-index fn2-fields fn2-pool)'))
    for text, name, value, use in sources:
        forms = lr.parse(text).forms
        definitions = [shape(f) for f in forms if isinstance(f, lr.Lst)
                       and len(f.items) > 1 and shape(f.items[0]) == 'defconst'
                       and shape(f.items[1]) == name]
        if definitions != [('defconst', name, value)]:
            raise AssertionError('source quantum changed: ' + name)
        expected = shape(lr.parse(use).forms[0])
        matches = [n for f in forms for n in walk(f) if shape(n) == expected]
        if len(matches) != 1:
            raise AssertionError('actual generated call no longer consumes quantum: ' + name)


class ReadWorkSourceTests(unittest.TestCase):
    def setUp(self):
        self.layout = (ROOT / 'books/layout.lisp').read_text()
        self.runs = (ROOT / 'books/runs-assemble.lisp').read_text()

    def test_actual_generated_calls_use_exact_extracted_quanta(self):
        check_source(self.layout, self.runs)

    def test_changed_decode_fuel_is_rejected(self):
        with self.assertRaises(AssertionError):
            check_source(self.layout.replace('(defconst *fn2-codec-decode-fuel* 4096)',
                                             '(defconst *fn2-codec-decode-fuel* 4097)'), self.runs)

    def test_bypassed_decode_quantum_is_rejected(self):
        with self.assertRaises(AssertionError):
            check_source(self.layout.replace('ogen *fn2-codec-decode-fuel* fn2-fields fn2-pool)',
                                             'ogen 8192 fn2-fields fn2-pool)'), self.runs)

    def test_bypassed_overlay_quantum_is_rejected(self):
        with self.assertRaises(AssertionError):
            check_source(self.layout, self.runs.replace('(fn2-ov-search *fn2-ov-search-steps* 0',
                                                       '(fn2-ov-search 80 0'))


if __name__ == '__main__':
    unittest.main()
