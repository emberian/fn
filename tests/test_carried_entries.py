"""tools/carried_entries.py: def-carried's completeness over the declared entries."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools import carried_entries, interface_kinds  # noqa: E402

BOOK = """(defun fn-inv (state) (declare (xargs :stobjs state)) (boundp-global 'x state))
(defun fn-writes (x state) (declare (xargs :stobjs state))
  (let ((state (f-put-global 'x x state))) (mv nil x state)))
(defun fn-new (x state) (declare (xargs :stobjs state))
  (if (consp x) (pprogn (princ$ "a" *standard-co* state) state) state))
(defun fn-new-mv (x state) (declare (xargs :stobjs state))
  (mv-let (a state) (fn-writes-single x state) (mv a x state)))
(defun fn-writes-single (x state) (declare (xargs :stobjs state)) (f-put-global 'y x state))
(defun fn-reads (x state) (declare (xargs :stobjs state)) (f-get-global x state))
(defun fn-pure (x) x)
(defun fn-via (x state) (declare (xargs :stobjs state)) (fn-new x state))
(defun fn-through-mac (x state) (declare (xargs :stobjs state)) (my-macro x state))
(defmacro my-macro (x state) `(list ,x ,state))
"""
ROW = {"name": "row", "where": "host/row.lisp:1", "invariant": "fn-inv", "established": ["fn-writes"],
       "transitions": [], "assumption": "a-owed", "owed": []}


def run(entries, **changes):
    source = interface_kinds.read_source([("books/b.lisp", BOOK)])
    row = dict(ROW, **changes)
    return carried_entries.judge([row], entries, source)


class CarriedEntries(unittest.TestCase):
    def test_new_state_returning_entry_unlisted_is_red(self):
        problems, _ = run(["fn-writes", "fn-new"])
        self.assertEqual(len(problems), 1)
        self.assertIn("host-called entry fn-new (fn-interfaces) returns the carried state state", problems[0])
        self.assertIn("nor owed under A-OWED", problems[0])

    def test_mv_and_called_state_returners_are_red(self):
        problems, _ = run(["fn-new-mv", "fn-writes-single", "fn-via"])
        self.assertEqual(len(problems), 3)

    def test_owed_entry_is_clean(self):
        problems, _ = run(["fn-writes", "fn-new"], owed=["fn-new"])
        self.assertEqual(problems, [])

    def test_transition_entry_is_clean(self):
        problems, _ = run(["fn-writes", "fn-new"], transitions=["fn-new"])
        self.assertEqual(problems, [])

    def test_stale_owed_name_is_red(self):
        for stale in ("fn-gone", "fn-reads", "fn-pure"):
            problems, _ = run(["fn-writes"], owed=[stale])
            self.assertEqual(len(problems), 1, stale)
            self.assertIn("stale owed name", problems[0])

    def test_owed_and_listed_is_red(self):
        problems, _ = run(["fn-writes"], owed=["fn-writes"])
        self.assertEqual(len(problems), 1)
        self.assertIn("remove it from the owed list", problems[0])

    def test_entry_that_does_not_return_state_is_ignored(self):
        problems, undecided = run(["fn-writes", "fn-reads", "fn-pure"])
        self.assertEqual((problems, undecided), ([], []))

    def test_macro_tail_is_undecided_not_clean_not_red(self):
        problems, undecided = run(["fn-writes", "fn-through-mac"])
        self.assertEqual(problems, [])
        self.assertEqual(undecided, ["fn-through-mac (entry, row row)"])

    def test_value_row_is_outside_the_rule(self):
        problems, _ = run(["fn-new"], invariant="fn-pure")
        self.assertEqual(problems, [])

    def test_rows_read_from_forms(self):
        with tempfile.TemporaryDirectory() as tmp:
            host = Path(tmp) / "host"
            host.mkdir()
            (Path(tmp) / "books").mkdir()
            (host / "r.lisp").write_text(
                "(def-carried r :invariant fn-inv :established ((fn-writes t1))\\n"
                " :transitions ((fn-new t2)) :incomplete (A-X (fn-a fn-b)))")
            (row,) = carried_entries.row_forms(Path(tmp))
        self.assertEqual((row["invariant"], row["established"], row["transitions"], row["assumption"], row["owed"]),
                         ("fn-inv", ["fn-writes"], ["fn-new"], "a-x", ["fn-a", "fn-b"]))


if __name__ == "__main__":
    unittest.main()
