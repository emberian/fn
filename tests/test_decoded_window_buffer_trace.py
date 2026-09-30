import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from ledger import Sym,read_forms
from decoded_window_buffer_trace import BufferInstrument,generate,ROOT

class DecodedBufferTraceTests(unittest.TestCase):
    def test_exact_artifact(self):
        self.assertEqual((ROOT/'books/decoded-window-initial-buffer-trace.lisp').read_text(),generate())

    def test_unknown_operation_refuses(self):
        with self.assertRaisesRegex(ValueError,'unclassified trusted source'):
            BufferInstrument({}).expr([Sym('unreviewed-grow'),Sym('buffer')])

    def test_resize_keeps_actual_operation_and_arguments(self):
        s=BufferInstrument({}).expr([Sym('resize-fn-octets$c-buf'),64,Sym('buffer')])
        self.assertIn('(resize-fn-octets$c-buf ',s)
        self.assertIn(':array-resize',s)
        self.assertIn("'resize-fn-octets$c-buf",s)

    def test_array_and_fill_writes_are_distinct(self):
        g=BufferInstrument({})
        self.assertIn(':array-write',g.expr([Sym('update-fn-octets$c-bufi'),2,3,Sym('buffer')]))
        self.assertIn(':fill-write',g.expr([Sym('update-fn-octets$c-fill'),2,Sym('buffer')]))

    def test_subtraction_keeps_negate_and_add(self):
        s=BufferInstrument({}).expr([Sym('-'),Sym('top'),Sym('off')])
        self.assertIn(':negate',s);self.assertIn(':add',s)

    def test_recursive_observers_keep_measures(self):
        s=generate()
        self.assertIn(':measure (nfix (- (nfix end) (nfix dst))) :ruler-extenders :all',s)
        self.assertIn(':measure (len xs) :ruler-extenders :all',s)

    def test_no_future_projection_runes(self):
        introduced=set()
        for f in read_forms(generate()):
            if not isinstance(f,list) or not f:continue
            if str(f[0])=='defun-nx':introduced.add(str(f[1]))
            if str(f[0])=='defthm':
                def syms(x):
                    if isinstance(x,list):
                        for y in x:yield from syms(y)
                    elif isinstance(x,Sym):yield str(x)
                names={x for x in syms(f) if x.startswith('fn-pib-')};names.discard(str(f[1]))
                self.assertTrue(names<=introduced,names-introduced)

if __name__=='__main__':unittest.main()
