import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from ledger import Sym, read_forms
from decoded_window_initial_trace import InitialInstrument, generate, ROOT

class DecodedInitialTraceTests(unittest.TestCase):
    def test_exact_source_artifact(self):
        self.assertEqual((ROOT / 'books/decoded-window-initial-source-trace.lisp').read_text(), generate())

    def test_unclassified_callee_refuses(self):
        with self.assertRaisesRegex(ValueError, 'unclassified trusted source'):
            InitialInstrument({}).expr([Sym('unreviewed-allocation'), Sym('state')])

    def test_bad_cond_refuses(self):
        with self.assertRaisesRegex(ValueError, 'unreviewed cond shape'):
            InitialInstrument({}).expr([Sym('cond'), [Sym('t'), 1, 2]])

    def test_subtraction_retains_neg_and_add(self):
        output = InitialInstrument({}).expr([Sym('-'), Sym('end'), Sym('start')])
        self.assertIn(':negate', output)
        self.assertIn(':add', output)

    def test_reserve_retains_actual_call_and_borrow(self):
        output = InitialInstrument({}).expr([Sym('fn-zin-out-reserve'), 64, Sym('out')])
        self.assertIn('(fn-zin-out-reserve ', output)
        self.assertIn(":borrow 'fn-zin-out-reserve", output)
        self.assertNotIn(':constructor', output)

    def test_projection_hints_do_not_name_future_observers(self):
        defined = set()
        for f in read_forms(generate()):
            if not isinstance(f, list) or not f:
                continue
            if str(f[0]) == 'defun-nx':
                defined.add(str(f[1]))
            if str(f[0]) == 'defthm':
                def walk(x):
                    if isinstance(x, list):
                        for y in x:
                            yield from walk(y)
                    elif isinstance(x, Sym):
                        yield str(x)
                observer_symbols = {s for s in walk(f) if s.startswith('fn-piw-')}
                observer_symbols.discard(str(f[1]))
                self.assertTrue(observer_symbols <= defined, observer_symbols - defined)

    def test_reset_recursion_retains_ruler_conditions(self):
        self.assertIn(':ruler-extenders :all', generate())

if __name__ == '__main__':
    unittest.main()
