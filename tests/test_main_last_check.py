"""tools/main_last_check.py (obstructions-5 item 36)."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import main_last_check  # noqa: E402

GUARD = 'if __name__ == "__main__":\n    unittest.main()\n'


def check(text):
    return main_last_check.findings(Path("tests/test_x.py"), text)


class MainLastTests(unittest.TestCase):
    def test_a_guard_at_the_end_is_clean(self):
        self.assertEqual(check("import unittest\nclass A(unittest.TestCase): pass\n\n" + GUARD),
                         [])

    def test_a_guard_mid_file_is_refused_with_its_line(self):
        found = check("import unittest\n" + GUARD + "class B(unittest.TestCase): pass\n")
        self.assertEqual(len(found), 1)
        self.assertIn("tests/test_x.py:2:", found[0])
        self.assertIn("not the last statement (line 4 follows it)", found[0])

    def test_an_unguarded_unittest_main_in_a_class_body_is_refused(self):
        found = check("import unittest\nclass A(unittest.TestCase):\n    unittest.main()\n")
        self.assertEqual(len(found), 1)
        self.assertIn(":3: unittest.main() outside", found[0])

    def test_a_bare_main_imported_from_unittest_counts(self):
        found = check("from unittest import main\nmain()\n")
        self.assertIn(":2: unittest.main() outside", found[0])

    def test_two_guards_are_refused(self):
        found = check("import unittest\n" + GUARD + GUARD)
        self.assertTrue(any("a second" in one for one in found), found)

    def test_reversed_comparison_is_a_guard(self):
        self.assertEqual(check('import unittest\nif "__main__" == __name__:\n'
                               '    unittest.main()\n'), [])

    def test_a_module_without_a_guard_is_fine(self):
        self.assertEqual(check("import unittest\nclass A(unittest.TestCase): pass\n"), [])

    def test_this_file_is_clean(self):
        self.assertEqual(main_last_check.findings(Path(__file__)), [])


if __name__ == "__main__":
    unittest.main()
