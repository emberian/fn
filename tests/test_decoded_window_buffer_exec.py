import copy
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from ledger import Sym, read_forms
from decoded_window_buffer_exec import ROOT, export_map, generate

class DecodedBufferExecTests(unittest.TestCase):
    def setUp(self):
        self.forms=read_forms((ROOT/'books/deflate-inflate.lisp').read_text())

    def buffer(self, name='fn-zin-win'):
        return next(f for f in self.forms if isinstance(f,list) and f and str(f[0])=='defabsstobj' and str(f[1])==name)

    def test_exact_generated_source(self):
        self.assertEqual((ROOT/'books/decoded-window-initial-buffer-exec.lisp').read_text(), generate())

    def test_selects_actual_executives(self):
        mapping=export_map(self.forms)
        self.assertEqual(mapping['fn-zin-win-append-list'],Sym('fn-oct-write-list'))
        self.assertEqual(mapping['fn-zin-tab-append-back'],Sym('fn-octets$c-append-back'))
        self.assertEqual(mapping['fn-zin-out-reserve'],Sym('fn-octets$c-reserve'))

    def test_changed_selector_is_read(self):
        b=self.buffer();e=b[b.index(Sym(':exports'))+1][0]
        e[e.index(Sym(':exec'))+1]=Sym('changed-selected-executive')
        self.assertEqual(export_map(self.forms)[str(e[0])],Sym('changed-selected-executive'))

    def test_changed_foundation_refuses(self):
        b=self.buffer();b[b.index(Sym(':foundation'))+1]=Sym('different-foundation')
        with self.assertRaisesRegex(ValueError,'changed buffer foundation'):export_map(self.forms)

    def test_missing_selector_refuses(self):
        b=self.buffer();e=b[b.index(Sym(':exports'))+1][0];i=e.index(Sym(':exec'));del e[i:i+2]
        with self.assertRaisesRegex(ValueError,'missing explicit executive'):export_map(self.forms)

    def test_missing_buffer_refuses(self):
        self.forms.remove(self.buffer())
        with self.assertRaisesRegex(ValueError,'missing buffer declaration'):export_map(self.forms)

    def test_duplicate_buffer_refuses(self):
        self.forms.append(copy.deepcopy(self.buffer()))
        with self.assertRaisesRegex(ValueError,'duplicate buffer declaration'):export_map(self.forms)

    def test_models_are_not_executable_subjects(self):
        generated=read_forms(generate())
        defs=[f for f in generated if isinstance(f,list) and f and str(f[0])=='defun-nx']
        self.assertEqual(len(defs),4)
        self.assertFalse(any(isinstance(f,list) and f and str(f[0])=='defun' for f in generated))

if __name__=='__main__':unittest.main()
