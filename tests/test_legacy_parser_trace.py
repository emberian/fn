"""Generator remains exact and fails closed on a new source operation."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from ledger import Sym
from legacy_parser_trace import Instrument, generate, ROOT

class LegacyParserTraceTests(unittest.TestCase):
    def test_generated_book_matches_source(self):
        self.assertEqual(generate(), (ROOT / 'books/legacy-parser-trace.lisp').read_text())

    def test_unknown_operation_refused(self):
        with self.assertRaisesRegex(ValueError, 'unclassified'):
            Instrument({}).expr([Sym('new-allocator'), 1])

    def test_quote_is_not_executed(self):
        self.assertEqual(Instrument({}).expr([Sym('quote'), [Sym('new-allocator'), 1]]),
                         '(cons (quote (new-allocator 1)) nil)')

    def test_signed_event_preserves_operands(self):
        text = Instrument({}).expr([Sym('-'), Sym('end'), Sym('start')])
        self.assertIn('(list :signed', text)
        self.assertIn('(cons end nil)', text)
        self.assertIn('(cons start nil)', text)
        self.assertNotIn('nfix', text)

if __name__ == '__main__':
    unittest.main()
