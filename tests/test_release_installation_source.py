"""Actual generated RELEASE schema and captured-bank producer binding controls."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr

class Installation(unittest.TestCase):
    def test_actual_wire_has_named_absolute_witness(self):
        source = (ROOT / 'books/format-events.lisp').read_text()
        matches = lr.match('(deflayout fn2-format-release-allocation ?*body)', lr.parse(source).forms, deep=False)
        self.assertEqual(len(matches), 1)
        form = source[matches[0].node.start:matches[0].node.end]
        self.assertIn('(installation-commit (:id commit))', form)
        self.assertIn('(installation-event (:id event))', form)
        self.assertLess(form.index('promoted-checkpoint'), form.index('installation-commit'))
        self.assertLess(form.index('installation-event'), form.index('RELEASE-EVIDENCE-'))
        self.assertIn('(fn2-layout-max-size *fn2-format-release-allocation*) 142', source)

    def test_stage_derives_event_from_actual_bank(self):
        source = (ROOT / 'books/release-allocation.lisp').read_text()
        for name in ['fn2-release-publication-source', 'fn2-allocation-release-stage', 'fn2-release-staged-current-p']:
            n = lr.match(f'(defun {name} ?*body)', lr.parse(source).forms, deep=False)[0].node
            form = source[n.start:n.end]
            self.assertIn('fn2-checkpoint-bank-evidence-event', form)
            self.assertNotIn('installation-event', lr.emit(n.items[2]))
        self.assertIn('(< cut installation) (< event installation-event)', source)

    def test_actual_packer_and_controls_cover_both_fields(self):
        source = (ROOT / 'books/release-allocation.lisp').read_text()
        n = lr.match('(defun fn2-allocation-release-pack-staged ?*body)', lr.parse(source).forms, deep=False)[0].node
        pack = source[n.start:n.end]
        controls = (ROOT / 'tests/release-allocation-staging-unit.lisp').read_text()
        for field, value in [('installation-commit', 3), ('installation-event', 8)]:
            self.assertIn(f'*fn2-format-release-allocation-field-{field}*', pack)
            self.assertIn(f'(fn2-allocation-release-{field} 0 fn2-allocation-release)', pack)
            self.assertIn(f'(assert-event (fn2-ras-run :{field}))', controls)
            self.assertIn(f'*fn2-format-release-allocation-field-{field}*) fn2-fields) {value})', controls)

if __name__ == '__main__':
    unittest.main()
