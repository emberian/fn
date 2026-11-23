"""Retained export structure controls, not admission of an application world."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import ledger

class RetainedExport(unittest.TestCase):
    def test_diagnostic_is_scoped_and_requires_existing_world(self):
        forms = ledger.read_forms((ROOT / 'meta/emit/print-cns-selected-member-retained.lsp').read_text())
        self.assertEqual([ledger.head(f) for f in forms], ['in-package', 'progn!', 'value-triple'])
        diagnostic = forms[1]
        self.assertEqual(diagnostic[1], [ledger.Sym('set-raw-mode'), ledger.Sym('t')])
        self.assertEqual(diagnostic[2], [ledger.Sym('load'), 'meta/emit/print-world.lisp'])
        binding = diagnostic[3]
        self.assertEqual(ledger.head(binding), 'let')
        self.assertEqual(binding[1][0], [ledger.Sym('*meta-w*'),
                                         [ledger.Sym('w'), ledger.Sym('*the-live-state*')]])
        self.assertEqual(binding[1][1], [ledger.Sym('*meta-errors*'), ledger.Sym('nil')])
        calls = [f for f in binding[2:] if isinstance(f, list) and ledger.head(f) == 'meta-print-certificate']
        self.assertEqual(len(calls), 1)
        self.assertEqual(str(calls[0][-1]).lower(), 'nil')
        self.assertEqual(str(calls[0][-2]).lower(), 'nil')
        atoms = []
        def visit(x):
            if isinstance(x, list):
                for y in x: visit(y)
            elif isinstance(x, ledger.Sym): atoms.append(str(x).lower())
        visit(forms)
        for forbidden in (':q', 'include-book', 'lp', 'defaxiom', 'skip-proofs', 'defttag'):
            self.assertNotIn(forbidden, atoms)
        self.assertIn('fn2-tv-attachment', atoms)
        self.assertIn('fn2-cns-put-answer', atoms)
        self.assertEqual(str(forms[-1][1]), ':cns-selected-member-returned-to-acl2')

if __name__ == '__main__':
    unittest.main()
