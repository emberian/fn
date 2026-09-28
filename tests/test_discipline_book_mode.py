"""--book on the four discipline tools, and the ledger's one pickle key.

defkeystone (2026-09-27): a before/after diff of ONE book re-read ~1,300
books in each of ledger, teeth_check, must_fail_check and reach_check, and
`python3 tools/ledger.py` and `import ledger` pickled the tree under
different keys (`__main__` vs `ledger`), so no tool reused another's work.
"""
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import ledger                                                 # noqa: E402

BOOK = "tests/acl2/feed-connection-teeth-tests.lisp"


def tool(*args, env=None):
    return subprocess.run([sys.executable, *args], cwd=ROOT, capture_output=True,
                          text=True, timeout=900, env=env)


class PickleKeyTests(unittest.TestCase):
    def test_a_script_run_pickles_the_importers_class(self):
        with tempfile.TemporaryDirectory() as cache:
            env = dict(os.environ, FN_LEDGER_TREE_CACHE=cache)
            result = tool("-c", "import runpy, sys; sys.argv=['ledger.py','--book','%s'];"
                          "runpy.run_path('tools/ledger.py', run_name='__main__')" % BOOK,
                          env=env)
            self.assertEqual(result.returncode, 0, result.stderr[-2000:])
            # --book is lazy and never persists; a full script run does.
            result = tool("tools/ledger.py", "--check", env=env)
            entries = list(Path(cache).glob("*.pickle"))
            self.assertEqual(len(entries), 1, result.stderr[-2000:])
            probe = tool("-c", "import sys, time; sys.path.insert(0, 'tools');"
                         "import ledger; t = time.time(); tree = ledger.load_tree();"
                         "print(type(tree).__module__, round(time.time() - t, 1))", env=env)
            module, seconds = probe.stdout.split()
            self.assertEqual(module, "ledger")
            # A hit is a pickle load (seconds), not the ~80 s analysis.
            self.assertLess(float(seconds), 40.0, probe.stdout)


class BookModeTests(unittest.TestCase):
    def test_ledger_book_is_the_full_row_of_that_book(self):
        result = tool("tools/ledger.py", "--book", BOOK)
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])
        rows = json.loads(result.stdout)
        self.assertEqual([row["book"] for row in rows], [BOOK])
        full = ledger.book_row(ledger.load_tree().books[BOOK], ledger.load_tree())
        for field in ("must_fails", "assert_events", "theorems", "suspects", "includes"):
            self.assertEqual(rows[0][field], full[field], field)

    def test_ledger_book_refuses_a_non_book(self):
        result = tool("tools/ledger.py", "--book", "tools/ledger.py")
        self.assertEqual(result.returncode, 2)

    def test_must_fail_check_book_reads_one_book(self):
        result = tool("tools/must_fail_check.py", "--book", BOOK)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("must_fail_check: 1 test books", result.stdout)

    def test_teeth_summary_book_is_scoped(self):
        result = tool("tools/teeth_check.py", "--summary", "--book", BOOK)
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])
        self.assertIn("in 1 test books", result.stdout)
        self.assertNotIn("keystones have two or more hypotheses", result.stdout)

    def test_reach_summary_book_judges_only_its_events(self):
        result = tool("tools/reach_check.py", "--summary", "--book", "books/owner-invariants-step.lisp")
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])
        whole = tool("tools/reach_check.py", "--summary")
        count = lambda text: int(text.split(" registry events")[0].split()[-1])
        self.assertLess(count(result.stdout), count(whole.stdout))
        self.assertNotIn("now hosted", result.stdout)


if __name__ == "__main__":
    unittest.main()
