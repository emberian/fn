"""Source transformation controls for the actual cold boot phase class."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
from restore_events_boot_source import PHASES, kind, boot

class EventBootSourceTests(unittest.TestCase):
    def test_machine_only_and_all_three_classes(self):
        src = '(defmachine other :states (:free))\n(defmachine fn2-boot :states (:free) :holds ((:read :storage-window)) :arms ((:free)))'
        out, n = kind(src)
        self.assertEqual(n, 3)
        for phase in PHASES:
            self.assertEqual(out.count(phase), 3)
        self.assertIn('(defmachine other :states (:free))', out)
        self.assertEqual(kind(out), (out, 0))

    def test_receipt_stage_preserves_payload_length(self):
        src = '(:read-result (:cond ((equal row-stage 10) (:next :checkpoint-payload-copy)) (t (:idle))))'
        out, n = boot(src)
        self.assertEqual(n, 1)
        self.assertIn('((equal row-stage 10) (:next :checkpoint-payload-copy))', out)
        self.assertIn('((equal row-stage 11) (:next :checkpoint-events-journal-received))', out)
        self.assertEqual(boot(out), (out, 0))

    def test_declaration_comment_and_string_untouched(self):
        src = '; (:read-result fake)\n"(:checkpoint-root-finish fake)"\n(:checkpoint-root-copy)'
        self.assertEqual(boot(src), (src, 0))

    def test_current_actual_machine_phase_closure(self):
        root = Path(__file__).resolve().parents[1]
        src = (root / 'books/boot.lisp').read_text()
        kinds = (root / 'books/boot-kind.lisp').read_text()
        lr.parse(src)
        self.assertEqual(kind(kinds), (kinds, 0))
        self.assertEqual(boot(src), (src, 0))
        for phase in PHASES:
            self.assertTrue(lr.match('(' + phase + ' ?*body)', lr.parse(src).forms, deep=True), phase)
        self.assertIn('(fn2-boot-checkpoint-investigation-finish id row-generation)', src)
        self.assertIn('((:validated) (:stop :checkpoint))', src)
        self.assertIn('(if (equal row-stage 10) row-read-length 4096)', src)

if __name__ == '__main__':
    unittest.main()
