import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from rewrite_commit_fault_literals import rewrite


class RewriteCommitFaults(unittest.TestCase):
    def test_commands_and_unrelated_numbers(self):
        text = "(list '(:auto 26) '(:auto 12) '(:start 0 2 26 0) 26) ; 26\n"
        result, count = rewrite(text)
        self.assertEqual(count, 2)
        self.assertEqual(result, "(list (list :auto *fn2-fault-none*) (list :auto *fn2-fault-no-space*) '(:start 0 2 26 0) 26) ; 26\n")
        self.assertEqual(rewrite(result), (result, 0))

    def test_membership_and_clock(self):
        result, count = rewrite("(or (member-equal fault '(11 12 26)) (equal fault 10) (fn2-sim-clock tick 26 sim))")
        self.assertEqual(count, 3)
        self.assertIn("(list *fn2-fault-tear* *fn2-fault-no-space* *fn2-fault-none*)", result)
        self.assertIn("(equal fault *fn2-fault-lying-flush*)", result)
        self.assertIn("(fn2-sim-clock tick *fn2-fault-none* sim)", result)

    def test_unknown_and_strings_remain(self):
        text = '(list ":auto 26" \'(:auto 99) (equal other 26))'
        self.assertEqual(rewrite(text), (text, 0))


if __name__ == "__main__":
    unittest.main()
