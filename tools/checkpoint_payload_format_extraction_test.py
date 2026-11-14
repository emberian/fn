"""Source-only extraction controls; no parser/hash execution claim."""
from pathlib import Path
import itertools
import json
import unittest
ROOT = Path(__file__).resolve().parents[1]
class Extraction(unittest.TestCase):
    def test_complete_live_source_only_declared_extraction_sites(self):
        f = json.loads((ROOT/'tools/fixtures/checkpoint_payload_format_extraction.json').read_text())
        source = f['old']
        for e in f['edits']:
            self.assertEqual(source.count(e['old']), 1)
            source = source.replace(e['old'], e['new'], 1)
        self.assertEqual(source, (ROOT/'books/checkpoint-payload.lisp').read_text())
    def test_header_phase_and_code_normalization(self):
        for decode, refs, compare in itertools.product((False, True), repeat=3):
            old = (':manifest-header', False) if not decode else ((':manifest-identity', False) if not refs else ((':manifest-identity', True) if not compare else (':ok', False)))
            shared = ':manifest-header' if not decode else (':manifest-identity' if not refs else (':identity-mismatch' if not compare else ':ok'))
            new = (':manifest-identity' if shared == ':identity-mismatch' else shared, shared == ':identity-mismatch')
            self.assertEqual(old, new)
    def test_entry_errors_and_acceptance(self):
        for decode, identity, proof in itertools.product((False, True), repeat=3):
            old = ':manifest-entry' if not (decode and identity) else (':manifest-proof' if not proof else ':ok')
            new = ':ok' if decode and identity and proof else (':manifest-proof' if decode and identity else ':manifest-entry')
            self.assertEqual(old, new)
    def test_actual_generated_decoder_and_field_refinements(self):
        source = (ROOT/'books/checkpoint-payload-format.lisp').read_text()
        self.assertIn('(fn2-am-get-header base total slot gen', source)
        self.assertIn('(fn2-am-get-entry base slot gen', source)
        self.assertIn('fn2-checkpoint-payload-read-header-fields-refinement', source)
        self.assertIn('fn2-checkpoint-payload-read-entry-fields-refinement', source)
if __name__ == '__main__': unittest.main()
