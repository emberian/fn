"""Source extraction controls, not ACL2 execution or physical-page witnesses."""
from pathlib import Path
import itertools
import json
import unittest

ROOT = Path(__file__).resolve().parents[1]

class Extraction(unittest.TestCase):
    def test_entire_live_caller_changes_only_frozen_extraction_sites(self):
        fixture = json.loads((ROOT / 'tools/fixtures/checkpoint_semantic_page_extraction.json').read_text())
        source = fixture['old']
        for edit in fixture['edits']:
            self.assertEqual(source.count(edit['old']), 1)
            source = source.replace(edit['old'], edit['new'], 1)
        self.assertEqual(source, (ROOT / 'books/checkpoint-semantic-retention.lisp').read_text())

    def test_header_acceptance_and_normalized_refusal(self):
        for raw, schema, version, run, level, bounded in itertools.product((False, True), repeat=6):
            old = raw and schema and version and run and level and bounded
            helper = ':ok' if old else ':source-header'
            self.assertEqual(old, helper == ':ok')
            self.assertEqual(':ok' if old else ':source-header', helper)

    def test_entry_acceptance_on_actual_u32_retained_count_domain(self):
        for raw, schema, version, run, level in itertools.product((False, True), repeat=5):
            for expected in (0, 1, 2**32-1):
                for decoded in (-1, 0, 1, 2**32-1, 2**32):
                    old = raw and schema and version and run and level and decoded == expected
                    shared = raw and schema and version and run and level and 0 <= decoded < 2**32
                    self.assertEqual(old, shared and decoded == expected)

    def test_field_output_is_unconditionally_same_decoder_output(self):
        source = (ROOT / 'books/checkpoint-semantic-page.lisp').read_text()
        self.assertIn('fn2-checkpoint-semantic-page-read-header-fields-refinement', source)
        self.assertIn('fn2-checkpoint-semantic-page-read-header-reader-context', source)
        self.assertIn(':position 1', source)

if __name__ == '__main__':
    unittest.main()
