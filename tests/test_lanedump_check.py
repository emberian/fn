import subprocess
import tempfile
import unittest
from pathlib import Path

from tools import lanedump_check as lc


def repo(test, files):
    d = tempfile.TemporaryDirectory()
    test.addCleanup(d.cleanup)
    r = Path(d.name)
    subprocess.run(["git", "init", "-q", str(r)], check=True)
    for f in files:
        (r / f).parent.mkdir(parents=True, exist_ok=True)
        (r / f).write_text("x")
    subprocess.run(["git", "-C", str(r), "add", "-f", "."], check=True)
    return str(r)


class LanedumpCheck(unittest.TestCase):
    def test_tracked_root_lanedump_is_refused(self):
        self.assertEqual(lc.main([repo(self, ["LANEDUMP.md", "a.txt"])]), 1)

    def test_nested_and_case_variant_are_refused(self):
        self.assertEqual(lc.main([repo(self, ["x/y/lanedump.MD"])]), 1)

    def test_clean_tree_and_the_coordinator_copy_pass(self):
        self.assertEqual(lc.main([repo(self, ["a.txt", "build/coordinator/lanedumps/bp.md",
                                              "LANEDUMP-notes.md"])]), 0)

    def test_not_a_git_tree_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(lc.main([d]), 1)


if __name__ == "__main__":
    unittest.main()
