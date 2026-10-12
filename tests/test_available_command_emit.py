import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import available_command_emit as emit
from proof_repl import forms, head_and_name


class AvailableCommandEmitTests(unittest.TestCase):
    def test_group_and_listgroup_share_the_view_summary(self):
        generated = {head_and_name(f)[1]: f for f in forms(emit.render())
                     if head_and_name(f)[0] == 'defun'}
        for name in ('fn-av-nntp-group-result-cat',
                     'fn-av-nntp-listgroup-result-cat'):
            form = generated[name]
            self.assertEqual(form.count('(fn-scv-summary group v fn-cat)'), 1)
            self.assertIn('(low (cadr s))', form)
            self.assertIn('(fn-av-scat-group-initial-of archive group s)', form)
            self.assertNotIn('fn-scat-available-low', form)

    def test_empty_fallback_belongs_only_to_the_reply_formatter(self):
        generated = {head_and_name(f)[1]: f for f in forms(emit.render())
                     if head_and_name(f)[0] == 'defun'}
        helper = generated['fn-av-scat-group-initial-of']
        self.assertIn('(fn-scat-available-summary-of archive group s)', helper)
        self.assertNotIn('fn-cat', helper)
        self.assertNotIn('fn-scv-summary', helper)

    def test_source_shape_drift_is_refused(self):
        with self.assertRaises(ValueError):
            emit.one_summary('(defun fn-av-nntp-group-result-cat () nil)',
                             'fn-nntp-group-result-cat')


if __name__ == '__main__':
    unittest.main()
