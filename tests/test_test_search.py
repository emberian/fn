"""Checks for `tools/test_search.py`: a `test?` verdict that cannot claim a
search Cgen did not run.

The transcripts below are cut from a real run on hbox (w28 launcher,
acl2s/cgen certified 2026-10-11; hbox:/tank/fn/scratch/b14-cgen-stobj.log).
The case that matters is the first: over a stobj function Cgen skips testing
and still prints "Test? succeeded"; the wrapper must say SKIPPED.
"""

import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import test_search  # noqa: E402

B, E = test_search.BEGIN, test_search.END

STOBJ_SKIP = f"""ACL2 !>
{B}
ACL2 !>CEgen/Note: Skipping testing completely, since some functions in this
conjecture either take stobj arguments or are constrained without an
attachment.

Test? succeeded. No counterexamples were found.
{E}
"""

FALSIFIED = f"""{B}
**Summary of Cgen/testing**
(IMPLIES (NATP X) (< X 5))
We tested 1025 examples across 2 subgoals, of which 998 (998 unique)
satisfied the hypotheses, and found 995 counterexamples and 3 witnesses.
**We falsified the conjecture. Here are counterexamples:**
 [found in : "top"]
 -- ((X 53))
 -- ((X 7))
Test? found a counterexample.
{E}
"""

SEARCHED = f"""{B}
**Summary of Cgen/testing**
(IMPLIES (NATP X) (<= 0 X))
We tested 2000 examples across 2 subgoals, of which 1876 (1876 unique)
satisfied the hypotheses, and found 0 counterexamples and 1876 witnesses.
Test? proved the conjecture under consideration. Therefore, no counterexamples
exist.
{E}
"""

UNSATISFIED = f"""{B}
**Summary of Cgen/testing**
(IMPLIES (AND (NATP X) (EQUAL X (+ X 1))) (< X 5))
We tested 2000 examples across 2 subgoals, of which 0 (0 unique) satisfied
the hypotheses, and found 0 counterexamples and 0 witnesses.
Test? proved the conjecture under consideration. Therefore, no counterexamples
exist.
{E}
"""


class Classify(unittest.TestCase):
    def test_stobj_skip_is_skipped_although_test_says_succeeded(self):
        verdict, detail = test_search.classify(STOBJ_SKIP)
        self.assertEqual(verdict, test_search.SKIPPED)
        self.assertIn("stobj", detail)

    def test_counterexample_names_the_first_binding(self):
        self.assertEqual(test_search.classify(FALSIFIED),
                         (test_search.COUNTEREXAMPLE, "((X 53))"))

    def test_a_real_search_is_searched_with_the_satisfied_count(self):
        verdict, detail = test_search.classify(SEARCHED)
        self.assertEqual(verdict, test_search.SEARCHED)
        self.assertTrue(detail.startswith("1876 examples 0 counterexamples"))

    def test_no_example_satisfying_the_hypotheses_is_skipped(self):
        verdict, detail = test_search.classify(UNSATISFIED)
        self.assertEqual(verdict, test_search.SKIPPED)
        self.assertIn("0 of 2000", detail)

    def test_succeeded_without_a_summary_is_skipped(self):
        text = f"{B}\nTest? succeeded. No counterexamples were found.\n{E}\n"
        verdict, detail = test_search.classify(text)
        self.assertEqual(verdict, test_search.SKIPPED)
        self.assertIn("no Cgen/testing summary", detail)

    def test_a_setup_error_is_skipped_not_searched(self):
        text = f"ACL2 Error in ( INCLUDE-BOOK \"x\" ...): no such book\n{SEARCHED}"
        verdict, detail = test_search.classify(text)
        self.assertEqual(verdict, test_search.SKIPPED)
        self.assertIn("setup failed", detail)

    def test_no_end_marker_is_skipped(self):
        verdict, _ = test_search.classify(SEARCHED.replace(E, ""))
        self.assertEqual(verdict, test_search.SKIPPED)

    def test_nested_binding_is_read_to_its_balancing_paren(self):
        text = FALSIFIED.replace("((X 53))", "((L (1 (2))) (N 0))")
        self.assertEqual(test_search.classify(text)[1], "((L (1 (2))) (N 0))")


class Driver(unittest.TestCase):
    def test_verbose_test_between_markers_after_books(self):
        text = test_search.driver("(natp x)", ["books/heap-figure.lisp"], "")
        lines = text.splitlines()
        self.assertIn(f'(include-book "{ROOT}/books/heap-figure" :ttags :all)', lines)
        self.assertIn("(acl2s-defaults :set verbosity-level 3)", lines)
        self.assertLess(lines.index(f'(cw "~%{B}~%")'), lines.index("(test? (natp x))"))
        self.assertLess(lines.index("(test? (natp x))"), lines.index(f'(cw "~%{E}~%")'))


class EndToEnd(unittest.TestCase):
    """main() against a fake ACL2 that replays the stobj transcript."""

    def test_main_prints_one_skipped_line_and_exits_2(self):
        with tempfile.TemporaryDirectory() as scratch:
            scratch = Path(scratch)
            canned = scratch / "transcript.txt"
            canned.write_text(STOBJ_SKIP)
            fake = scratch / "acl2"
            fake.write_text(f"#!/bin/sh\ncat > /dev/null\nhead -c 100000 '{canned}'\n")
            fake.chmod(fake.stat().st_mode | stat.S_IEXEC)
            log = scratch / "out.log"
            environment = {"FN_ACL2": str(fake), "FN_CERT_CACHE": str(scratch),
                           "FN_ACL2_SLOT_DIR": str(scratch / "slots")}
            completed = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "test_search.py"),
                 "--log", str(log), "(implies (stp st) (natp (fld st)))"],
                env={**os.environ, **environment}, capture_output=True, text=True,
                timeout=60, check=False)
            self.assertEqual(completed.returncode, 2, completed.stderr)
            self.assertEqual(completed.stdout.splitlines(),
                             [completed.stdout.strip()])
            self.assertTrue(completed.stdout.startswith("SKIPPED "))
            self.assertIn("Skipping testing completely", log.read_text())


if __name__ == "__main__":
    unittest.main()
