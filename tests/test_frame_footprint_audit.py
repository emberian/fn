import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import frame_footprint_audit as audit


class FrameAuditTests(unittest.TestCase):
    def test_literal_child_drift(self):
        rows = audit.instances("(defthm x t :hints ((\"Goal\" :use ((:instance op-arm-row-frame (fn2-arm-ch '(0 56 5)))))))")
        log = "FRAMEAUDIT (OP-ARM-ROW-FRAME (implies (subsetp-equal '(0 57 5) fn2-arm-ch) t))\nFRAMEAUDIT-DONE"
        result = audit.check(rows, audit.world(log))
        self.assertEqual(result[0]['status'], 'mismatch')
        self.assertEqual(result[0]['missing'], [57])
        rows[0]['value'] = "'(0 57 5)"
        self.assertEqual(audit.check(rows, audit.world(log))[0]['status'], 'checked-subset')

    def test_dynamic_and_absent_are_unresolved(self):
        rows = audit.instances("(:instance op-arm-kids (fn2-arm-free *live-children*))")
        self.assertEqual(audit.check(rows, {})[0]['status'], 'unresolved')

    def test_semantic_numbers_strings_and_comments_excluded(self):
        source = '''(defthm x (equal phase 56)
          :hints (("(:instance fake (fn2-arm-ch '(56)))" :use
            ((:instance real (phase 56) (fn2-arm-cs '(56)) (fn2-arm-ch '(5)))))))
          ; (:instance ignored (fn2-arm-ch '(56)))
        '''
        rows = audit.instances(source)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]['value'], "'(5)")

    def test_generator_footprint_excludes_columns(self):
        rows = audit.instances("(fn2-env-x-same-events 'name '(call c) 'frame 'dir '(56) '(5))")
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]['theorem'], 'frame')
        self.assertEqual(rows[0]['value'], "'(5)")
        self.assertEqual(rows[0]['parameter'], 'fn2-arm-ch')

    def test_kids_generator_resolves_multivalue_call(self):
        rows = audit.instances("(fn2-env-x-kids-call-events 'write '(mv-nth 3 (fn2-issue-write c)) '(1 0 5))")
        self.assertEqual(rows[0]['theorem'], 'fn2-commit~fn2-issue-write-arm-kids')
        self.assertEqual(rows[0]['parameter'], 'fn2-arm-free')

    def test_conclusion_is_not_a_premise(self):
        rows = audit.instances("(:instance op (ch '(5)))")
        log = "FRAMEAUDIT (OP (implies t (subsetp-equal '(57) ch)))\nFRAMEAUDIT-DONE"
        self.assertEqual(audit.check(rows, audit.world(log))[0]['status'], 'unresolved')

    def test_incomplete_world_refused(self):
        with self.assertRaises(ValueError):
            audit.world('FRAMEAUDIT (OP NIL)')
        with self.assertRaises(ValueError):
            audit.world('(cw \"FRAMEAUDIT-DONE~%\")')


if __name__ == '__main__':
    unittest.main()
