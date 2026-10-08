"""tools/rewrite_reconfigure_stage.py: the staging entry moves to :stage."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "tools"))
import rewrite_reconfigure_stage as rw

BEFORE = """(defun f (service plan)
  (fnn-owner-live-reconfigure (run drive fnn-quantum-control service nil)
      (word reason)
    :before
    (progn
      (fnn-rc-begin run nil 'fn-native-admin-host-owner-reconfigure plan)
      (drive))
    :continue word))
"""

AFTER = """(defun f (service plan)
  (fnn-owner-live-reconfigure (run drive fnn-quantum-control service nil)
      (word reason)
    :stage (lambda (pcid) (fnn-owner-result 'fn-ores-config-result-p 'fn-native-admin-host-owner-reconfigure pcid plan))
    :before
    (progn
      (fnn-rc-begin run nil)
      (drive))
    :continue word))
"""

MANY = """(g (fnn-owner-live-reconfigure (r d s sv nil) (w x) :before (progn (fnn-rc-begin r t 'e a (b c) 3) (d)) :continue w))
"""


class RewriteStage(unittest.TestCase):
    def test_moves_the_entry_and_its_arguments(self):
        self.assertEqual(rw.rewrite(BEFORE), AFTER)

    def test_idempotent(self):
        self.assertEqual(rw.rewrite(AFTER), AFTER)

    def test_arguments_keep_their_text_and_reserve(self):
        out = rw.rewrite(MANY)
        self.assertIn("(fnn-rc-begin r t)", out)
        self.assertIn("'e pcid a (b c) 3))", out)

    def test_other_text_is_untouched(self):
        src = "; comment\n(defun h () 1)\n" + BEFORE + "(defun k () 2)\n"
        self.assertEqual(rw.rewrite(src), "; comment\n(defun h () 1)\n" + AFTER + "(defun k () 2)\n")


if __name__ == "__main__":
    unittest.main()
