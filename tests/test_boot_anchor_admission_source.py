"""Exact shared intake extraction and real receipt/continuation ordering."""
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import lisp_rewrite as lr
import checkpoint_boot_input_extract as p


class AnchorAdmission(unittest.TestCase):
    def test_original_anchor_functions_have_one_narrow_provider(self):
        before = json.loads((ROOT/'tools/fixtures/checkpoint-descriptor-input-before.json').read_text())['source']
        self.assertEqual(p.anchor_provider(before), (ROOT/'books/checkpoint-anchor-input.lisp').read_text())
        after = p.remove_anchor_from_restore(p.remove_from_restore(before))
        self.assertEqual(p.remove_anchor_from_restore(after), after)
        self.assertEqual(p.remove_from_restore(after), after)
        for name in p.NAMES+p.ANCHOR_NAMES:
            self.assertFalse(lr.match('(defun '+name+' ?*body)', lr.parse(after).forms))

    def test_original_zero_reader_is_moved_not_reimplemented(self):
        fixture = json.loads((ROOT/'tools/fixtures/checkpoint-zero-range-before.json').read_text())
        self.assertIn(fixture['definition'], (ROOT/'books/checkpoint-zero-range.lisp').read_text())
        after = p.remove_zero_from_restore_read(fixture['source'])
        self.assertEqual(p.remove_zero_from_restore_read(after), after)
        self.assertFalse(lr.match('(defun fn2-checkpoint-restore-zero-range ?*body)', lr.parse(after).forms))
        # Preserve every other actual linked-reader function, guards included.
        for form in lr.parse(fixture['source']).forms:
            if isinstance(form,lr.Lst) and getattr(form.items[0],'low',None)=='defun':
                name = form.items[1].low
                if name == 'fn2-checkpoint-restore-zero-range':
                    continue
                new = p.unique(after,name)
                self.assertEqual(fixture['source'][form.start:form.end],after[new.start:new.end])

    def test_budget_source_window_and_initial_visit_precede_mutation(self):
        text = (ROOT/'books/boot-anchor-admission.lisp').read_text()
        fn = p.unique(text,'fn2-boot-anchor-admit-pool')
        body = text[fn.start:fn.end]
        self.assertLess(body.index('((when (zp budget))'),body.index('(fn2-boot-bootstrap-receipt-p'))
        self.assertLess(body.index('(fn2-boot-bootstrap-receipt-p'),body.index('(fn2-format-anchor-decode'))
        self.assertLess(body.index('(fn2-layout-range-code'),body.index('(fn2-format-anchor-decode'))
        self.assertIn('(fn2-checkpoint-restore-zero-range (- *fn2-format-sector-size* span)',body)
        # Fixed initial decode/tail yields before FORMAT gets its own grant.
        self.assertLess(body.index('(fn2-boot-anchor-return :more span)'),
                        body.index('(fn2-checkpoint-restore-anchor-step'))
        self.assertIn('(fn2-checkpoint-restore-anchor-step anchor anchor',body)

    def test_evidence_completion_precedes_checked_census(self):
        text = (ROOT/'books/boot-anchor-admission.lisp').read_text()
        fn = p.unique(text,'fn2-boot-anchor-admit-pool')
        body = text[fn.start:fn.end]
        checked = body.index('(update-fn2-boot-config-anchor-checked-mask')
        self.assertLess(body.index('(unless (eq code :candidate))'),checked)
        self.assertLess(body.index('(fn2-boot-save-anchor-evidence'),checked)
        self.assertLess(body.index('(unless (eq evidence :ok))'),checked)
        for kind in ('empty','invalid','checked'):
            self.assertIn('fn2-boot-config-anchor-'+kind+'-mask',body)
        self.assertNotIn('checkpoint-layout-ready',body)
        self.assertNotIn('fn2-boot-config-bootstrap-owner-gen',body)


if __name__ == '__main__':
    unittest.main()
