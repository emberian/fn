import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from ledger import Sym
from payload_action_trace import ActionInstrument,generate,ROOT

class PayloadActionTraceTests(unittest.TestCase):
    def test_artifact_pins_actual_source_and_matches(self):
        self.assertEqual((ROOT/'books/payload-action-source-trace.lisp').read_text(),generate())
    def test_unknown_callee_refuses(self):
        with self.assertRaisesRegex(ValueError,'unclassified trusted source'):
            ActionInstrument({}).expr([Sym('unreviewed-buffer-resize'),Sym('state')])
    def test_malformed_multiple_value_binding_refuses(self):
        with self.assertRaisesRegex(ValueError,'unreviewed mv-let shape'):
            ActionInstrument({}).expr([Sym('mv-let'),Sym('not-a-binding-list'),1,2])
    def test_match_carries_copy_effects_and_trace(self):
        output=generate()
        self.assertIn('fn-pzc-copy',output)
        self.assertIn('(mv-nth 2 (car ',output)
        self.assertIn('fn-pat-zin-match-value-and-effects-projection',output)
    def test_subtraction_keeps_negation(self):
        output=ActionInstrument({}).expr([Sym('-'),Sym('n'),Sym('k')])
        self.assertIn(':negate',output)
        self.assertIn(':add',output)
    def test_borrowed_mutation_still_has_actual_value_call(self):
        output=ActionInstrument({}).expr([Sym('fn-zin-set'),6,9,Sym('state')])
        self.assertIn('(fn-zin-set ',output)
        self.assertIn(":borrow 'fn-zin-set",output)

if __name__=='__main__': unittest.main()
