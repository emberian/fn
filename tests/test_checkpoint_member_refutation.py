"""Member-only integration controls; do not include in the generic registry packet."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).parents[1]
sys.path.insert(0, str(ROOT / 'meta/emit'))
from emit_lean import read_all

class MemberRefutationPlumbing(unittest.TestCase):
    def test_actual_member_binding_and_export_are_connected(self):
        source = (ROOT / 'tests/checkpoint-member-refutation-unit.lisp').read_text()
        self.assertIn('(not (fn2-checkpoint-installation-pack-member-fields-type$owed', source)
        self.assertIn(':use fn2-checkpoint-member-fields-type-readonly-removal-ground', source)
        self.assertIn('fn2-checkpoint-installation-pack-member-fields-type-under-guard', source)
        # The qualified guarded bundle exports both the original refutation
        # and its distinct supported-domain interface. Keep the full chain.
        self.assertIn('(include-book "tests/checkpoint-member-guarded-evidence-unit")',
                      (ROOT / 'tools/owed-export.lsp').read_text())
        guarded = (ROOT / 'tests/checkpoint-member-guarded-evidence-unit.lisp').read_text()
        self.assertIn('(include-book "checkpoint-member-refutation-unit")', guarded)
        self.assertIn('(include-book "checkpoint-member-interface-unit")', guarded)
        self.assertIn('link unverified', (ROOT / 'books/owed-report.lisp').read_text())
    def test_actual_member_sources_parse(self):
        for path in ['tests/checkpoint-member-refutation-unit.lisp',
                     'tests/checkpoint-member-refutation-export.lsp']:
            self.assertTrue(read_all((ROOT / path).read_text()))

if __name__ == '__main__':
    unittest.main()
