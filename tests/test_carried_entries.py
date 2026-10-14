"""tools/carried_entries.py: def-carried's completeness over the declared entries."""

from __future__ import annotations

import sys
import contextlib
import io
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

    def test_generated_stobj_entry_uses_shared_function_knowledge(self):
        files = [("books/b.lisp", BOOK + "\n(defabsstobj fn-fixture"
                  " :exports ((fn-fixture-count :logic fn-fixture$a-count)))")]
        source = interface_kinds.read_source(files)
        functions = carried_entries.stobj_functions(files)
        entry = ["fn-fixture-count"]
        # Control: without the generated-function inventory it is undecidable.
        self.assertEqual(carried_entries.state_entries(entry, source), ([], entry))
        self.assertIn(entry[0], functions)
        self.assertEqual(carried_entries.state_entries(entry, source, functions), ([], []))
        inference = carried_entries.Inference(source, "state", functions)
        self.assertEqual(carried_entries.state_entries(entry, source, inference=inference), ([], []))
        self.assertEqual(carried_entries.judge([ROW], entry, source, functions), ([], []))


class PinsFramed(unittest.TestCase):
    """A-PINS-FRAMED teeth: fixture trees only, including raw host definitions."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        (self.root / "books").mkdir()
        (self.root / "host/native").mkdir(parents=True)
        self.entry = "fn-mutant"

    def fixture(self, body, helper="", raw=""):
        (self.root / "host/entry.lisp").write_text(
            "(defun fn-mutant (x state) (declare (xargs :mode :program :stobjs state)) "
            + body + ")\n(definterface fn-mutant :class :program :kinds ())\n")
        (self.root / "host/helper.lisp").write_text(helper)
        (self.root / "host/native/helper.lisp").write_text(raw)
        return carried_entries.frame_register(self.root)

    def refused(self, register, path, reason):
        self.assertNotIn(self.entry, register["escaped"])
        row = next(r for r in register["needs_proved_row"] if r["name"] == self.entry)
        self.assertTrue(any(e["call_path"] == path and reason in e["reason"]
                            for e in row["evidence"]), row)
        return row

    def test_a_direct_program_pin_writer_refused_by_name(self):
        register = self.fixture("(f-put-global 'fn-owner-conn-pins x state)")
        row = self.refused(register, [self.entry], "write fn-owner-conn-pins")
        self.assertEqual(row["writes"], ["fn-owner-conn-pins"])

    def test_b_host_helper_pin_writer_refused_by_name(self):
        register = self.fixture("(fn-helper x state)",
            "(defun fn-helper (x state) (f-put-global 'fn-owner-conn-pins x state))")
        self.refused(register, [self.entry, "fn-helper"], "write fn-owner-conn-pins")

    def test_c_two_calls_deep_pin_writer_refused_by_name(self):
        register = self.fixture("(fn-helper x state)",
            "(defun fn-helper (x state) (fn-deep x state))\n"
            "(defun fn-deep (x state) (f-put-global 'fn-owner-conn-pins x state))")
        self.refused(register, [self.entry, "fn-helper", "fn-deep"], "write fn-owner-conn-pins")

    def test_d_computed_global_name_refused_fail_closed(self):
        for accessor in ("f-put-global", "put-global", "set-global", "makunbound-global"):
            with self.subTest(accessor=accessor):
                register = self.fixture(f"(pprogn ({accessor} x nil state) state)")
                row = self.refused(register, [self.entry], "computed global name")
                self.assertEqual(row["writes"], sorted(carried_entries.FRAME_GLOBALS))

    def test_e_undefined_function_handed_state_refused_fail_closed(self):
        register = self.fixture("(pprogn (fn-unread x state) state)")
        self.refused(register, [self.entry], "unread function fn-unread")

    def test_f_unrelated_owner_global_writer_escaped(self):
        register = self.fixture("(f-put-global 'fn-owner-unrelated x state)")
        self.assertEqual(register["escaped"], [self.entry])
        self.assertEqual(register["needs_proved_row"], [])
        self.assertEqual(register["counts"]["entries_enumerated"], 1)

    def test_g_check_fails_and_names_entry_when_helper_gains_write(self):
        self.fixture("(fn-helper x state)", "(defun fn-helper (x state) state)")
        argv = ["--frame", "fn-owner-pins-carried", "--root", str(self.root)]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(carried_entries.main([*argv, "--write"]), 0)
            self.assertEqual(carried_entries.main([*argv, "--check"]), 0)
        register = self.fixture("(fn-helper x state)",
            "(defun fn-helper (x state) (f-put-global 'fn-owner-conn-pins x state))")
        before = (self.root / carried_entries.FRAME_FILE).read_bytes()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(carried_entries.main([*argv, "--check"]), 1)
        self.assertIn("fn-mutant: ESCAPED -> needs-proved-row", out.getvalue())
        self.assertEqual((self.root / carried_entries.FRAME_FILE).read_bytes(), before)
        self.refused(register, [self.entry, "fn-helper"], "write fn-owner-conn-pins")

    def test_raw_two_deep_helper_and_setf_global_refused(self):
        register = self.fixture("(pprogn (fnn-helper) state)", raw=
            "(defun fnn-helper () (fnn-deep))\n"
            "(defun fnn-deep () (setf (f-get-global 'fn-owner-conn-pins *the-live-state*) nil))")
        self.refused(register, [self.entry, "fnn-helper", "fnn-deep"], "write fn-owner-conn-pins")

    def test_raw_wholesale_state_replacement_refused(self):
        register = self.fixture("(pprogn (fnn-helper) state)",
            raw="(defun fnn-helper () (setf *the-live-state* nil))")
        self.refused(register, [self.entry, "fnn-helper"], "wholesale state")

    def test_unknown_raw_call_without_state_also_refused(self):
        register = self.fixture("(pprogn (fnn-helper) state)",
            raw="(defun fnn-helper () (fnn-missing))")
        self.refused(register, [self.entry, "fnn-helper"], "unread function fnn-missing")

    def test_unexpanded_macro_refused(self):
        register = self.fixture("(pprogn (fn-macro x state) state)",
            "(defmacro fn-macro (x state) `(f-put-global 'fn-owner ,x ,state))")
        self.refused(register, [self.entry], "unexpanded macro fn-macro")

    def test_dynamic_funcall_apply_refused_and_literal_calls_followed(self):
        for call in ("(funcall x state)", "(apply x (list state))"):
            register = self.fixture(f"(pprogn {call} state)")
            self.refused(register, [self.entry], "non-literal")
        for call in ("(funcall #'fn-helper x state)", "(apply 'fn-helper (list x state))",
                     "(funcall (function fn-helper) x state)"):
            register = self.fixture(f"(pprogn {call} state)",
                "(defun fn-helper (x state) (f-put-global 'fn-owner x state))")
            self.refused(register, [self.entry, "fn-helper"], "write fn-owner")

    def test_undecided_return_never_escaped(self):
        register = self.fixture("(fn-unread state)")
        row = self.refused(register, [self.entry], "UNDECIDED state return")
        self.assertEqual(register["UNDECIDED"], [self.entry])
        self.assertEqual(row["writes"], sorted(carried_entries.FRAME_GLOBALS))

    def test_recursive_helper_cycle_still_finds_write(self):
        register = self.fixture("(pprogn (fn-helper state) state)",
            "(defun fn-helper (state) (pprogn (fn-deep state) state))\n"
            "(defun fn-deep (state) (if nil (fn-helper state) (f-put-global 'fn-owner nil state)))")
        self.refused(register, [self.entry, "fn-helper", "fn-deep"], "write fn-owner")

    def test_same_name_raw_definition_is_not_hidden_by_logical_definition(self):
        register = self.fixture("(fn-helper x state)",
            "(defun fn-helper (x state) state)",
            "(defun fn-helper (x state) (f-put-global 'fn-owner-conn-pins x *the-live-state*))")
        self.refused(register, [self.entry, "fn-helper"], "write fn-owner-conn-pins")

    def test_quoted_calls_comments_and_strings_are_data(self):
        register = self.fixture("(pprogn '(f-put-global 'fn-owner nil state) state)",
            "; (defun fn-helper (state) (f-put-global 'fn-owner nil state))\n")
        self.assertEqual(register["escaped"], [self.entry])

    def test_state_rebinding_to_arbitrary_value_refused(self):
        register = self.fixture("(let ((state x)) state)")
        self.refused(register, [self.entry], "wholesale state")

    def test_state_output_rebinding_to_arbitrary_value_refused(self):
        register = self.fixture("(mv-let (a state) (mv nil x) state)")
        self.refused(register, [self.entry], "wholesale state output")

    def test_package_qualified_pin_name_refused(self):
        register = self.fixture("(f-put-global 'ACL2::FN-OWNER-CONN-PINS x state)")
        self.refused(register, [self.entry], "write fn-owner-conn-pins")

    def test_assignment_place_arguments_are_traversed(self):
        register = self.fixture("(pprogn (fnn-helper) state)", raw=
            "(defun fnn-helper () (setf (f-get-global 'fn-owner-other "
            "(f-put-global 'fn-owner-conn-pins nil *the-live-state*)) nil))")
        self.refused(register, [self.entry, "fnn-helper"], "write fn-owner-conn-pins")

    def test_unattached_abstract_local_witness_is_not_runtime_code(self):
        register = self.fixture("(pprogn (fn-abstract state) state)",
            "(encapsulate (((fn-abstract state) => state)) "
            "(local (defun fn-abstract (state) state)))")
        self.refused(register, [self.entry, "fn-abstract"], "no readable attachment")

    def test_readable_attachment_writer_is_followed(self):
        register = self.fixture("(pprogn (fn-abstract state) state)",
            "(encapsulate (((fn-abstract state) => state)) "
            "(local (defun fn-abstract (state) state)))\n"
            "(defattach (fn-abstract fnn-attached))", raw=
            "(defun fnn-attached (state) (f-put-global 'fn-owner-conn-pins nil *the-live-state*))")
        self.refused(register, [self.entry, "fn-abstract", "fnn-attached"], "write fn-owner-conn-pins")

    def test_h_take_without_state_is_escaped(self):
        register = self.fixture("(pprogn (take 3 x) state)")
        self.assertEqual(register["escaped"], [self.entry])
        self.assertEqual(register["needs_proved_row"], [])

    def test_i_unread_function_handed_state_is_refused(self):
        register = self.fixture("(pprogn (fn-unread state) state)")
        self.refused(register, [self.entry], "fail-closed: unread function fn-unread")

    def test_j_raw_reference_to_live_state_is_refused(self):
        register = self.fixture("(pprogn (fnn-helper) state)",
            raw="(defun fnn-helper () *the-live-state*)")
        self.refused(register, [self.entry, "fnn-helper"], "raw reference to *the-live-state*")

    def test_other_stobj_accessors_without_state_are_escaped(self):
        register = self.fixture("(pprogn (fn-arena-count fn-arena) (fn-hist-count fn-hist) state)")
        self.assertEqual(register["escaped"], [self.entry])

    def test_nested_writer_in_state_free_unread_call_is_still_refused(self):
        register = self.fixture("(pprogn (take 3 (f-put-global 'fn-owner-conn-pins nil state)) state)")
        self.refused(register, [self.entry], "write fn-owner-conn-pins")

    def test_state_taking_read_only_builtins_are_escaped(self):
        for head in carried_entries.FRAME_STATE_READ_ONLY:
            with self.subTest(head=head):
                register = self.fixture(f"(pprogn ({head} 'fn-owner state) state)")
                self.assertEqual(register["escaped"], [self.entry])

    def test_macro_without_state_is_escaped(self):
        register = self.fixture("(pprogn (fn-macro x) state)",
            "(defmacro fn-macro (x) `(take 3 ,x))")
        self.assertEqual(register["escaped"], [self.entry])

    def test_raw_global_setter_remains_closed_for_unrelated_name(self):
        register = self.fixture("(pprogn (fnn-helper) state)",
            raw="(defun fnn-helper () (set-global 'fn-owner-other nil))")
        self.refused(register, [self.entry, "fnn-helper"], "raw global setter")

    def test_unread_state_free_abstract_call_is_escaped(self):
        register = self.fixture("(pprogn (fn-abstract x) state)",
            "(encapsulate (((fn-abstract *) => *)) (local (defun fn-abstract (x) x)))")
        self.assertEqual(register["escaped"], [self.entry])


if __name__ == "__main__":
    unittest.main()
