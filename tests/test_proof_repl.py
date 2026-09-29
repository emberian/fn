"""tools/proof_repl.py: a live ACL2 session driven one form at a time.

The reader, the trimming and the sentinel protocol are tested against a fake
ACL2 that speaks just enough of the loop; one case runs the real ACL2 when
one is on PATH, since the point of the tool is the seconds-per-try loop the
freeze lanes did not have (review of 2026-09-22, F1 and F5).
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import pathlib
import shutil
import signal
import socket
import stat
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from contextlib import nullcontext
from types import SimpleNamespace
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_repl  # noqa: E402
from tests.test_certs import manifest_for, worktree, TEST_COMPATIBILITY  # noqa: E402

FAKE_ACL2 = r'''#!/usr/bin/env python3
import sys, time
world, labels = 0, {}
lines = iter(sys.stdin)
for line in lines:
    text = line.strip()
    if text.startswith('(cw "~%FN-REPL-DONE'):
        print(text.split('FN-REPL-DONE ')[1].split('~%')[0].join(["FN-REPL-DONE ", ""]))
        sys.stdout.flush()
        continue
    if "(good-bye)" in text:
        break
    if text == "(sleep-form)":
        time.sleep(60)
    if text == ":ubt!":
        next(lines, None)  # reads its argument: the sentinel
        print("ACL2 !>")
    elif text == "(raw-abort)":
        print("***** ABORTING from raw Lisp *****")
        print("Error:  Control stack exhausted")
        next(lines, None)  # ACL2 discards the pending input
    elif "FN-PROBE-AT" in text:
        print("FN-PROBE-AT %d" % world)
    elif text.startswith("(ubu! '"):
        world = labels[text[len("(ubu! '"):-1]]
    elif "(deflabel " in text:
        world += 1
        labels[text.split("(deflabel ")[1].split(")")[0]] = world
    elif "(defthm bad" in text:
        print("ACL2 Error [Failure] in ( DEFTHM BAD ...):  See :DOC failure.")
    elif "(defthm" in text or "(defun" in text or "with-prover-time-limit" in text:
        world += 1
        for i in range(70):
            print("Subgoal *1/%d" % i)
        print("*** Key checkpoint at the top level: ***")
        print("Summary")
        print("Form:  ( DEFTHM OK ...)")
        print("Time:  0.50 seconds (prove: 0.40, print: 0.00, other: 0.10)")
        print("Prover steps counted:  1234")
    else:
        print("GOT " + text)
    sys.stdout.flush()
'''


class ReaderTests(unittest.TestCase):
    def test_forms_keep_raw_text_quotes_and_strings_and_drop_comments(self):
        text = ('; comment (a)\n(in-package "ACL2")\n'
                "'(quoted form)\n"
                '(defthm t1 (equal "a ) b" "a ) b") :hints (("Goal")))\n'
                "#| block ( |# (local (defthm t2 t))\n")
        self.assertEqual(proof_repl.forms(text),
                         ['(in-package "ACL2")', "'(quoted form)",
                          '(defthm t1 (equal "a ) b" "a ) b") :hints (("Goal")))',
                          "(local (defthm t2 t))"])

    def test_head_and_name_sees_through_local_and_names_only_events(self):
        self.assertEqual(proof_repl.head_and_name("(defthm foo t)"), ("defthm", "foo"))
        self.assertEqual(proof_repl.head_and_name("(local (defthm Foo t))"), ("defthm", "foo"))
        self.assertEqual(proof_repl.head_and_name("(in-theory (enable x))"), ("in-theory", None))
        self.assertTrue(proof_repl.is_event("(defun f (x) x)"))
        self.assertFalse(proof_repl.is_event('(include-book "x")'))

    def test_an_event_is_wrapped_in_a_prover_time_limit_and_a_query_is_not(self):
        self.assertEqual(proof_repl.wrap_limit("(defthm a t)", 30),
                         "(with-prover-time-limit 30 (defthm a t))")
        self.assertEqual(proof_repl.wrap_limit("(pe 'a)", 30), "(pe 'a)")

    def test_brief_keeps_the_checkpoints_and_summary_of_a_long_output(self):
        long = "\n".join(["Goal", "x"] + ["Subgoal %d" % i for i in range(100)]
                         + ["*** Key checkpoint at the top level: ***", "(NOT (P X))",
                            "Summary", "Time: 1.0"])
        out = proof_repl.brief(long)
        self.assertIn("*** Key checkpoint", out)
        self.assertIn("Time: 1.0", out)
        self.assertNotIn("Subgoal 50", out)
        self.assertEqual(proof_repl.brief("short\noutput"), "short\noutput")
        self.assertTrue(proof_repl.errored("ACL2 Error [Failure] in ( DEFTHM X ...)"))


ENCAPSULATE_OUTPUT = """Summary
Form:  ( DEFTHM E2 ...)
Rules: ((:REWRITE F-ID))
Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.00)
Prover steps counted:  9
E2

End of Encapsulated Events.

Summary
Form:  ( ENCAPSULATE NIL (LOCAL ...) ...)
Rules: NIL
Time:  0.03 seconds (prove: 0.00, print: 0.00, other: 0.00)
Prover steps counted:  16
 T
"""


class MeasureTests(unittest.TestCase):
    def test_the_last_summary_is_the_forms_cost_not_the_sum(self):
        cost = proof_repl.measure(ENCAPSULATE_OUTPUT)
        self.assertEqual((cost["time"], cost["steps"], cost["summaries"]), (0.03, 16, 2))
        self.assertFalse(cost["steps_capped"])

    def test_a_step_limit_and_a_query_without_summary(self):
        capped = proof_repl.measure("Time:  1.20 seconds (prove: 1.2)\n"
                                    "Prover steps counted:  More than 100,000\n")
        self.assertEqual(capped["steps"], 100000)
        self.assertTrue(capped["steps_capped"])
        self.assertIn("prover steps >100,000", proof_repl.cost_words(capped))
        none = proof_repl.measure("(DEFUN F (X) X)\n")
        self.assertEqual((none["time"], none["steps"], none["summaries"]), (None, None, 0))
        self.assertEqual(proof_repl.cost_words(none, 0.4),
                         "ACL2 time -; prover steps -; elapsed 0.4 s")
        self.assertIn("elapsed 0.0 s", proof_repl.cost_words(none, 0))

    def test_totals_sum_forms_and_rank_by_steps(self):
        totals = proof_repl.Totals()
        totals.add("#1 defthm a", {"time": 0.5, "steps": 10}, 1.0, False)
        totals.add("#2 defthm b", {"time": 2.0, "steps": 900}, 3.0, True)
        totals.add("#3 in-theory", {"time": None, "steps": None}, 0.1, False)
        self.assertEqual(totals.line(), "[total: 3 forms, 1 refused; ACL2 time 2.50 s; "
                                        "prover steps 910; elapsed 4.1 s]")
        self.assertIn("#2 defthm b", totals.slowest()[0])
        self.assertEqual(len(totals.slowest()), 2)


class TrimTests(unittest.TestCase):
    def test_a_short_answer_is_whole(self):
        self.assertEqual(proof_repl.brief("a\n\nACL2 !>\nb"), "a\nb")

    def test_an_unanchored_long_answer_keeps_its_head_and_says_what_was_cut(self):
        # show-accumulated-persistence: the most expensive rules come first.
        lines = ["rule-%03d" % i for i in range(300)]
        out = proof_repl.brief("\n".join(lines), where="build/x.txt")
        self.assertIn("rule-000", out)
        self.assertIn("rule-024", out)
        self.assertNotIn("rule-025", out)
        self.assertIn("rule-299", out)
        self.assertIn("[... 215 lines cut (lines 26-240 of this answer); --full prints "
                      "everything; or: sed -n '26,240p' build/x.txt ...]", out)

    def test_a_long_anchored_answer_keeps_the_first_checkpoints_and_the_last_summary(self):
        lines = (["Goal'"] + ["Subgoal %d" % i for i in range(100)]
                 + ["*** Key checkpoint at the top level: ***"]
                 + ["checkpoint-line %d" % i for i in range(400)]
                 + ["Summary", "Form:  ( DEFTHM X ...)", "Time:  9.00 seconds",
                    "ACL2 Error [Failure] in ( DEFTHM X ...)"])
        out = proof_repl.brief("\n".join(lines))
        kept = out.splitlines()
        self.assertEqual(kept[0], "Goal'")
        self.assertIn("*** Key checkpoint at the top level: ***", kept)
        self.assertIn("Time:  9.00 seconds", kept)
        self.assertIn("ACL2 Error [Failure] in ( DEFTHM X ...)", kept)
        notes = [line for line in kept if line.startswith("[... ")]
        self.assertEqual(len(notes), 2)
        shown = [line for line in kept if not line.startswith("[... ")]
        cut = sum(int(note.split()[1]) for note in notes)
        self.assertEqual(len(shown) + cut, len(lines))

    def test_diagnostic_forms_are_never_trimmed(self):
        for form in (":pso", "(show-accumulated-persistence :frames)", "(pe 'foo)",
                     "(pbt 1)", ":pe foo", "(pso!)"):
            self.assertTrue(proof_repl.wants_full(form), form)
        for form in ("(defthm pe t)", "(accumulated-persistence t)", "(thm (equal x x))"):
            self.assertFalse(proof_repl.wants_full(form), form)


class RangeTests(unittest.TestCase):
    FORMS = ['(in-package "ACL2")', '(include-book "base")',
             '(local (include-book "std/lists/top" :dir :system))',
             "(defun f (x) x)", "(defthm a (equal (f x) x))", "(in-theory (disable f))",
             "(local (defthm b t))", "(defthm c t)"]

    def test_from_until_and_through_by_name_and_number(self):
        forms = self.FORMS
        self.assertEqual(list(proof_repl.select_range(forms)), list(range(8)))
        self.assertEqual(list(proof_repl.select_range(forms, "a", "c")), [4, 5, 6])
        self.assertEqual(list(proof_repl.select_range(forms, "A", through="b")), [4, 5, 6])
        self.assertEqual(list(proof_repl.select_range(forms, "#6")), [5, 6, 7])
        self.assertEqual(list(proof_repl.select_range(forms, until="#2")), [0])
        with self.assertRaises(SystemExit):
            proof_repl.select_range(forms, "nope")
        with self.assertRaises(SystemExit):
            proof_repl.select_range(forms, "#9")
        with self.assertRaises(SystemExit):
            proof_repl.select_range(forms, "c", "a")
        self.assertEqual(proof_repl.form_label(7, forms[6]), "#7 defthm b")

    def test_include_targets_resolve_from_the_including_book(self):
        books = proof_repl.ROOT / "books"
        self.assertEqual(proof_repl.include_target('(include-book "base")', books),
                         "books/base")
        self.assertEqual(proof_repl.include_target(
            '(local (include-book "../books/x" :ttags :all))', proof_repl.ROOT / "tests"),
            "books/x")
        self.assertIsNone(proof_repl.include_target(
            '(include-book "std/lists/top" :dir :system)', books))
        self.assertIsNone(proof_repl.include_target("(defthm include-book t)", books))


class ProbeFormTests(unittest.TestCase):
    def test_hints_are_replaced_at_the_events_own_level(self):
        form = ('(defthm foo (implies (p x) (q x :hints nil))\n'
                '  :hints (("Goal" :in-theory (enable p)))\n  :rule-classes nil)')
        out = proof_repl.set_keyword(form, ":hints", '(("Goal" :induct t))')
        self.assertEqual(out, '(defthm foo (implies (p x) (q x :hints nil))\n'
                              '  :hints (("Goal" :induct t))\n  :rule-classes nil)')

    def test_hints_are_added_when_absent_and_inside_local(self):
        self.assertEqual(proof_repl.set_keyword("(local (defthm foo t))", ":hints", "h"),
                         "(local (defthm foo t :hints h))")
        self.assertEqual(proof_repl.set_keyword("(defthm foo t :otf-flg t)", ":otf-flg", "nil"),
                         "(defthm foo t :otf-flg nil)")

    def test_a_theorem_is_renamed_and_a_definition_is_not(self):
        self.assertEqual(proof_repl.probe_form("(local (defthm Foo t))", None),
                         "(local (defthm Foo-probe t))")
        self.assertEqual(proof_repl.probe_form("(defun g (x) (g x))", None),
                         "(defun g (x) (g x))")


class CommandTests(unittest.TestCase):
    def test_a_keyword_command_takes_the_rest_of_its_line(self):
        self.assertEqual(proof_repl.commands(":ubt! foo"), [":ubt! foo"])
        self.assertEqual(proof_repl.commands(":ubt! foo\n(defthm a t)"),
                         [":ubt! foo", "(defthm a t)"])
        self.assertEqual(proof_repl.commands("(a) (b)"), ["(a)", "(b)"])
        self.assertEqual(proof_repl.commands(":pe f ; why\n:u\n(x)"), [":pe f", ":u", "(x)"])
        self.assertEqual(proof_repl.commands(":ubt! 'foo"), [":ubt! 'foo"])
        self.assertTrue(proof_repl.is_keyword_command("  :pbt :max"))
        self.assertFalse(proof_repl.is_keyword_command("(ubt! 'foo)"))

    def test_several_probe_forms_rename_only_the_target_and_hint_the_last(self):
        text = "(defthm helper t)\n(defthm target (p x))"
        self.assertEqual(proof_repl.probe_attempts(text, "target", "(h)"),
                         ["(defthm helper t)", "(defthm target-probe (p x) :hints (h))"])
        self.assertEqual(proof_repl.probe_attempts("(defthm target t)", "target", None),
                         ["(defthm target-probe t)"])
        self.assertEqual(proof_repl.probe_attempts("(defun h (x) x) (defthm z t)", "target",
                                                   None),
                         ["(defun h (x) x)", "(defthm z t)"])

    def test_undo_to_base_reports_what_it_did_and_when_it_could_not(self):
        def scripted(numbers):
            answers = iter(numbers)

            def ask(_name, request, **_kw):
                if "FN-PROBE-AT" in request["form"]:
                    value = next(answers)
                    return {"output": "" if value is None else f"FN-PROBE-AT {value}\n"}
                return {"output": ""}
            return ask
        with mock.patch.object(proof_repl, "ask", scripted([7])):
            self.assertEqual(proof_repl.undo_to_base("p", 7), (True, "clean"))
        with mock.patch.object(proof_repl, "ask", scripted([9, 7])):
            self.assertEqual(proof_repl.undo_to_base("p", 7),
                             (True, "undid 2 command(s) above the checkpoint"))
        with mock.patch.object(proof_repl, "ask", scripted([9, 8])):
            clean, how = proof_repl.undo_to_base("p", 7)
            self.assertFalse(clean)
            self.assertIn("command 8", how)
        with mock.patch.object(proof_repl, "ask", scripted([5])):
            self.assertFalse(proof_repl.undo_to_base("p", 7)[0])
        with mock.patch.object(proof_repl, "ask", scripted([None])):
            self.assertFalse(proof_repl.undo_to_base("p", 7)[0])


class EncapsulateTests(unittest.TestCase):
    def test_a_from_source_book_in_one_encapsulate_keeps_its_locals_local(self):
        text = ('(in-package "ACL2")\n(include-book "dep")\n(local (defthm l t))\n'
                '(defun f (x) x)\n')
        books = proof_repl.ROOT / "books"
        # ACL2 refuses a non-local include-book inside an encapsulate: it is
        # sent first, and the rest goes in the encapsulate (seven lanes hit
        # the refusal on 2026-09-27).
        self.assertEqual(proof_repl.encapsulated(text, books, set()),
                         (['(include-book "dep")'],
                          "(encapsulate ()\n(local (defthm l t))\n(defun f (x) x)\n)"))
        self.assertEqual(proof_repl.encapsulated(text, books, {"books/dep"}),
                         ([], "(encapsulate ()\n(local (defthm l t))\n(defun f (x) x)\n)"))

    def test_local_includes_stay_inside_and_defpkg_is_hoisted(self):
        text = ('(defpkg "FOO" nil)\n(local (include-book "std/lists/take" :dir :system))\n'
                '(include-book "std/lists/rev" :dir :system)\n(defthm g t)\n')
        hoisted, body = proof_repl.encapsulated(text, proof_repl.ROOT / "books", set())
        self.assertEqual(hoisted, ['(defpkg "FOO" nil)',
                                   '(include-book "std/lists/rev" :dir :system)'])
        self.assertEqual(body, '(encapsulate ()\n(local (include-book "std/lists/take" '
                               ':dir :system))\n(defthm g t)\n)')

    def test_with_a_limit_each_event_inside_is_limited_and_includes_are_not(self):
        text = ('(local (include-book "a"))\n(local (defthm l t))\n(defun f (x) x)\n'
                '(defttag :x)\n')
        _, body = proof_repl.encapsulated(text, proof_repl.ROOT / "books", set(), 30)
        self.assertIn('\n(local (include-book "a"))\n', body)
        self.assertIn("(with-prover-time-limit 30 (local (defthm l t)))", body)
        self.assertIn("(with-prover-time-limit 30 (defun f (x) x))", body)
        self.assertIn("\n(defttag :x)\n", body)


class LoadLimitTests(unittest.TestCase):
    """start's forms run under the per-form prover limit, as send's do."""

    class Recorder:
        def __init__(self, answers):
            self.sent, self.answers = [], list(answers)

        def send(self, form, timeout):
            self.sent.append((form, timeout))
            return (self.answers.pop(0) if self.answers else "ok"), False

    def test_each_event_of_the_book_is_limited_and_a_time_limit_is_named(self):
        scratch = proof_repl.ROOT / "build" / "proof-repl-limit-test"
        scratch.mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, scratch, True)
        (scratch / "b.lisp").write_text('(in-package "ACL2")\n(defun f (x) x)\n'
                                        "(defthm slow (equal (f x) x))\n(defthm after t)\n")
        timeout_answer = ("*** Key checkpoint at the top level: ***\n(EQUAL (F X) X)\n"
                          "ACL2 Error [Time-limit] in ( DEFTHM SLOW ...):  Out of time in "
                          "the rewriter.\nSummary\nForm:  ( DEFTHM SLOW ...)\n"
                          # What ACL2 8.7 prints after it (hbox, 2026-09-28).
                          "\nACL2 Error [Failure] in ( DEFTHM SLOW ...):  See :DOC "
                          "failure.\n\n******** FAILED ********\n")
        acl2 = self.Recorder(["", "", "", timeout_answer])
        state = {"name": None, "loaded": [], "ld_loaded": {}}
        ok = proof_repl.load_book(acl2, "build/proof-repl-limit-test/b", state, 600.0,
                                  set(), limit=20)
        self.assertFalse(ok)
        forms = [form for form, _ in acl2.sent]
        self.assertEqual(forms[1], '(in-package "ACL2")')
        self.assertEqual(forms[2], "(with-prover-time-limit 20 (defun f (x) x))")
        self.assertEqual(forms[3], "(with-prover-time-limit 20 (defthm slow (equal (f x) x)))")
        self.assertEqual(len(forms), 4)  # stopped at the refusal
        self.assertEqual(state["stopped_at"], "slow")
        self.assertTrue(state["load_time_limited"])
        self.assertTrue(state["error"].startswith("over the per-form prover limit (20 s"))
        self.assertIn("(EQUAL (F X) X)", state["error"])

    def test_no_limit_sends_the_forms_as_written(self):
        scratch = proof_repl.ROOT / "build" / "proof-repl-limit-test-0"
        scratch.mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, scratch, True)
        (scratch / "b.lisp").write_text("(defun f (x) x)\n")
        acl2 = self.Recorder([])
        state = {"name": None, "loaded": [], "ld_loaded": {}}
        self.assertTrue(proof_repl.load_book(acl2, "build/proof-repl-limit-test-0/b", state,
                                             600.0, set(), limit=None))
        self.assertEqual(acl2.sent[1][0], "(defun f (x) x)")


import contextlib  # noqa: E402
import io  # noqa: E402
import re  # noqa: E402
from pathlib import Path  # noqa: E402


class LaneAskTests(unittest.TestCase):
    """lane-tools-1 (2026-09-28): the asks fourteen lanes wrote in their LANEDUMPs."""

    MUST_FAIL_CAUGHT = ("NIL\nACL2 !>\n\nHARD ACL2 ERROR in FN-X:  boom\n\n\nSummary\n"
                        "Form:  ( MAKE-EVENT (QUOTE ...) ...)\nRules: NIL\n"
                        "Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)\n T\n"
                        "ACL2 !>\n")
    MUST_FAIL_FAILED = ("NIL\nACL2 !>\nSummary\nForm:  ( MAKE-EVENT (QUOTE ...) ...)\n"
                        "Rules: NIL\nTime:  0.00 seconds\n\nACL2 Error [Failure] in "
                        "( MAKE-EVENT (QUOTE ...) ...):  See :DOC failure.\n\n"
                        "******** FAILED ********\nACL2 !>\n")

    def test_a_must_fail_that_caught_a_hard_error_is_not_refused(self):
        # defkeystone: must-fail returned T over an er hard and was marked refused.
        self.assertFalse(proof_repl.errored(self.MUST_FAIL_CAUGHT))
        self.assertTrue(proof_repl.errored(self.MUST_FAIL_FAILED))
        self.assertTrue(proof_repl.errored("ACL2 Error in TOP-LEVEL:  The symbol FOO"))
        self.assertTrue(proof_repl.errored("Summary\nTime: 0.1\n\nHARD ACL2 ERROR in X: y"))
        self.assertTrue(proof_repl.errored("Summary\nx\nABORTING from raw Lisp"))
        self.assertFalse(proof_repl.errored("Summary\nForm: (DEFUN F ...)\n F\n"))

    def test_long_time_few_steps_is_named(self):
        # blake3-digest: 126-180 s at 228 steps, time spent clausifying an mv-let.
        note = proof_repl.slow_note({"time": 126.0, "steps": 228}, 130.0)
        self.assertIn("long time, few steps: 130 s for 228 prover steps", note)
        self.assertEqual(proof_repl.slow_note({"time": 126.0, "steps": 2_000_000}), "")
        self.assertEqual(proof_repl.slow_note({"time": 3.0, "steps": 12}), "")
        self.assertIn("long time", proof_repl.slow_note({"time": None, "steps": None}, 40.0))

    def test_character_literals_and_bar_symbols_do_not_unbalance_a_form(self):
        # compression-extents-2: a one-line send with quotes miscounted parens.
        text = r'''(defconst *x* '("a \"b\" (" #\( #\")) (list #\) #\; #\Space |a (b|)'''
        self.assertEqual(proof_repl.forms(text),
                         [r'''(defconst *x* '("a \"b\" (" #\( #\"))''',
                          r"(list #\) #\; #\Space |a (b|)"])
        self.assertEqual(proof_repl.commands("(cw \"~x0 (\" '(a \"b)\" c))"),
                         ["(cw \"~x0 (\" '(a \"b)\" c))"])

    def book(self, text: str) -> Path:
        directory = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, directory, True)
        path = directory / "b.lisp"
        path.write_text(text)
        return path

    def test_send_range_names_what_it_skips_and_counts_local_forms(self):
        # web-native: a local include later forms needed was absent, silently.
        path = self.book('(in-package "ACL2")\n(local (include-book "dep"))\n'
                         '(local (include-book "arithmetic-5/top" :dir :system))\n'
                         '(local (defthm l1 t))\n(defun f (x) x)\n')
        dep = str(path.parent.resolve() / "dep")
        all_forms = proof_repl.forms(path.read_text())
        items, skipped, local = proof_repl.range_items(path, all_forms, range(0, 5), {dep})
        self.assertEqual([label for label, _ in items],
                         ["#1 in-package", "#3 include-book", "#4 defthm l1", "#5 defun f"])
        self.assertEqual(skipped, ["#2 include-book (loaded from source already)"])
        self.assertEqual(local, 2)
        words = proof_repl.range_words("s", "b", range(0, 5), items, skipped, local, False)
        self.assertIn("2 of them (local ...)", words)
        self.assertIn("STAY in this session", words)
        self.assertIn("skipped 1 form(s): #2 include-book (loaded from source already)", words)

    def test_send_range_ld_local_sends_one_encapsulate_after_the_hoisted_includes(self):
        path = self.book('(include-book "std/lists/top" :dir :system)\n'
                         '(local (defthm l1 t))\n(defun f (x) x)\n')
        sent = []

        def fake_send_many(name, items, limit, full, keep_going):
            sent.extend(items)
            return 0
        args = proof_repl.argparse.Namespace(
            name="s", book=str(path), start=None, until=None, through=None,
            skip_includes=False, ld_local=True, limit=None, full=False, keep_going=False)
        with mock.patch.object(proof_repl, "send_many", fake_send_many), \
                mock.patch.object(proof_repl, "read_state", lambda name: {}), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(proof_repl.send_range(args), 0)
        self.assertEqual(sent[0][1], '(include-book "std/lists/top" :dir :system)')
        self.assertTrue(sent[1][1].startswith("(encapsulate ()"))
        self.assertIn("(local (defthm l1 t))", sent[1][1])
        self.assertEqual(len(sent), 2)
        self.assertIn("inside one encapsulate", out.getvalue())

    def test_resync_undoes_what_is_there_and_resends_from_the_first_missing(self):
        # web-native: :ubt! then send-range --from X left earlier definitions missing.
        path = self.book("(defun a (x) x)\n(defun b (x) x)\n(defthm c t)\n(defun d (x) x)\n")
        world = {"a", "c", "d"}  # b was lost; c and d are stale copies
        calls = []

        def asker(name, request):
            form = request["form"]
            calls.append(form)
            if form.startswith(":ubt! "):
                order = ["a", "b", "c", "d"]
                world.difference_update(order[order.index(form.split()[1]):])
                return {"output": "ok"}
            names = re.findall(r"logical-namep '([a-z]+)", form)
            flags = [one in world for one in names]
            want = form.startswith("(position t")
            return {"output": "ACL2 !>" + (str(flags.index(want)) if want in flags
                                           else "NIL") + "\n"}
        sent = []
        args = proof_repl.argparse.Namespace(
            name="s", book=str(path), start="c", until=None, through=None,
            limit=None, full=False, keep_going=False)
        with mock.patch.object(proof_repl, "send_many",
                               lambda name, items, *rest: sent.extend(items) or 0), \
                mock.patch.object(proof_repl, "read_state", lambda name: {}), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(proof_repl.resync(args, asker), 0)
        self.assertIn(":ubt! c", calls)
        self.assertEqual(world, {"a"})
        self.assertEqual([label for label, _ in sent],
                         ["#2 defun b", "#3 defthm c", "#4 defun d"])
        self.assertIn("#2 b (before c) was missing", out.getvalue())

    def test_status_warns_that_a_form_by_form_dependency_leaks_its_local_theory(self):
        # feed-queue: 6.9M steps over --source-deps against 1.76M certified.
        sessions = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, sessions, True)
        (sessions / "w").mkdir()
        (sessions / "w" / "state.json").write_text(json.dumps({
            "name": "w", "book": "books/x", "loaded": [], "sends": 0,
            "ld_loaded": {"books/dep": 12}, "stopped_at": None, "error": None}))
        with mock.patch.object(proof_repl, "SESSIONS", sessions), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            proof_repl.status(proof_repl.argparse.Namespace(name="w"))
        self.assertIn("WARNING: 1 from-source book(s) loaded form by form", out.getvalue())
        self.assertIn("--ld-leak", out.getvalue())


class RemoteTests(unittest.TestCase):
    def test_remote_options_stay_on_this_side(self):
        argv = ["start", "s", "books/x", "--host", "hbox", "--remote-tree=/t", "--no-sync",
                "--upto", "y", "--host=persvati"]
        self.assertEqual(proof_repl.strip_remote_options(argv),
                         ["start", "s", "books/x", "--upto", "y"])

    def test_each_box_runs_with_its_own_toolchain_cache_and_wrapper(self):
        import farm
        self.assertEqual(proof_repl.farm_hosts(), farm.HOSTS)
        hbox = proof_repl.remote_script("hbox", "/tank/fn/gates/l-repl", "l",
                                        ["start", "s", "books/x"])
        self.assertIn("cd /tank/fn/gates/l-repl && export ", hbox)
        self.assertIn(f"FN_ACL2={farm.HOSTS['hbox']['acl2']}", hbox)
        self.assertIn(f"FN_CERT_CACHE={farm.HOSTS['hbox']['cache']}", hbox)
        self.assertIn("FN_LANE=l", hbox)
        self.assertIn("swarm-build python3 tools/proof_repl.py start s books/x", hbox)
        send = proof_repl.remote_script("hbox", "/t", "l", ["send", "s", "(defthm a t)"])
        self.assertNotIn("swarm-build", send)
        self.assertIn("'(defthm a t)'", send)
        persvati = proof_repl.remote_script("persvati", "fn-gates/l-repl", "l",
                                            ["probe", "s", "e"])
        self.assertIn(f"FN_ACL2={farm.HOSTS['persvati']['acl2']}", persvati)
        self.assertNotIn("swarm-build", persvati)
        self.assertEqual(proof_repl.remote_tree("persvati", "lane"), "fn-gates/lane-repl")
        self.assertEqual(proof_repl.remote_tree("hbox", "lane"), "/tank/fn/gates/lane-repl")
        self.assertEqual(proof_repl.remote_tree("hbox", None, "/x"), "/x")
        with self.assertRaises(SystemExit):
            proof_repl.remote_tree("hbox", None)
        with self.assertRaises(SystemExit):
            proof_repl.box_settings("laptop")

    def test_acl2_flag_then_fn_acl2_choose_the_boxs_acl2(self):
        # extract-2: hbox's default ACL2 (tls 16384) died "Thread local storage
        # exhausted" under an image world; --host had no way to pick another.
        import farm
        argv = ["start", "s", "books/x", "--host", "hbox", "--acl2", "/tank/tls64k"]
        self.assertEqual(proof_repl.strip_remote_options(argv), ["start", "s", "books/x"])
        args = proof_repl.argparse.Namespace(acl2="/tank/tls64k")
        self.assertEqual(proof_repl.remote_acl2(args, {"FN_ACL2": "/other"}), "/tank/tls64k")
        none = proof_repl.argparse.Namespace(acl2=None)
        self.assertEqual(proof_repl.remote_acl2(none, {"FN_ACL2": "/other"}), "/other")
        self.assertIsNone(proof_repl.remote_acl2(none, {}))
        script = proof_repl.remote_script("hbox", "/t", "l", ["start", "s", "books/x"],
                                          "/tank/tls64k")
        self.assertIn("FN_ACL2=/tank/tls64k ", script)
        self.assertNotIn(farm.HOSTS["hbox"]["acl2"], script)

    def test_no_sync_refuses_when_the_boxs_copy_is_not_this_one(self):
        # defprotocol: --no-sync read the remote copy, so a local edit after
        # the last sync silently did not run.
        relative = "tools/proof_repl.py"
        here = proof_repl.hashlib.sha256((proof_repl.ROOT / relative).read_bytes()).hexdigest()
        proof_repl.refuse_stale_remote("hbox", "/t", relative, lambda *_: here)
        with self.assertRaises(SystemExit) as refused:
            proof_repl.refuse_stale_remote("hbox", "/t", relative, lambda *_: "0" * 64)
        self.assertIn("sha256 0000000000000000", str(refused.exception))
        self.assertIn(f"sha256 {here[:16]}", str(refused.exception))
        with self.assertRaises(SystemExit) as absent:
            proof_repl.refuse_stale_remote("hbox", "/t", relative, lambda *_: None)
        self.assertIn("sha256 absent", str(absent.exception))

    def test_host_auto_follows_the_session_else_picks_the_least_loaded(self):
        name = "auto-host-test"
        directory = proof_repl.session_dir(name)
        directory.mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, directory, True)
        ns = proof_repl.argparse.Namespace
        start = ns(command="start", name=name)
        no_laptop = lambda: None  # noqa: E731
        self.assertEqual(proof_repl.resolve_auto_host(start, lambda: "persvati", no_laptop),
                         "persvati")
        # A session directory here with no remote.json is this machine's session.
        self.assertEqual(proof_repl.resolve_auto_host(ns(command="send", name=name),
                                                      lambda: "hbox", no_laptop), "laptop")
        with self.assertRaises(SystemExit):
            proof_repl.resolve_auto_host(ns(command="send", name=name + "-absent"),
                                         lambda: "hbox", no_laptop)
        (directory / "remote.json").write_text(json.dumps({"host": "hbox"}))
        self.assertEqual(proof_repl.resolve_auto_host(ns(command="send", name=name),
                                                      lambda: "persvati", no_laptop), "hbox")
        with self.assertRaises(SystemExit):
            proof_repl.resolve_auto_host(start, lambda: "", no_laptop)

    def test_host_auto_starts_on_the_laptop_only_when_it_is_less_loaded(self):
        start = proof_repl.argparse.Namespace(command="start", name="auto-laptop-test")
        box = lambda: ("hbox", 0.50)  # noqa: E731
        self.assertEqual(proof_repl.resolve_auto_host(start, box, lambda: (0.25, 3)), "laptop")
        self.assertEqual(proof_repl.resolve_auto_host(start, box, lambda: (0.75, 3)), "hbox")
        # No qualified launcher, or no free slot: laptop_offer says None.
        self.assertEqual(proof_repl.resolve_auto_host(start, box, lambda: None), "hbox")
        # No box answered: the laptop, when it offers, rather than a refusal.
        self.assertEqual(proof_repl.resolve_auto_host(start, lambda: ("", None),
                                                      lambda: (2.0, 1)), "laptop")
        # Only start considers the laptop; list/reap stay on the boxes.
        listing = proof_repl.argparse.Namespace(command="list", name=None)
        self.assertEqual(proof_repl.resolve_auto_host(listing, box, lambda: (0.1, 6)), "hbox")

    def test_host_auto_skips_the_laptop_when_its_cache_lacks_the_closure(self):
        # operations, auth-tls-bugs: auto took the laptop with 76/87 books uncached.
        start = proof_repl.argparse.Namespace(command="start", name="gap", book="books/x")
        box = lambda: ("hbox", 0.50)  # noqa: E731
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(proof_repl.resolve_auto_host(
                start, box, lambda: (0.25, 3), lambda book: (76, 90)), "hbox")
        self.assertIn("lacks 76 of books/x's 90 dependencies", out.getvalue())
        self.assertEqual(proof_repl.resolve_auto_host(
            start, box, lambda: (0.25, 3), lambda book: (0, 90)), "laptop")
        # No box answered: the laptop still, whatever its cache (the start says why).
        self.assertEqual(proof_repl.resolve_auto_host(
            start, lambda: ("", None), lambda: (0.25, 3), lambda book: (5, 9)), "laptop")

    def test_local_cache_gap_counts_dependencies_without_an_entry(self):
        with tempfile.TemporaryDirectory() as temporary:
            cache = pathlib.Path(temporary)
            book = "books/account-list"  # a real book with a closure
            graph = proof_repl.include_graph(proof_repl.ROOT, book)
            wanted = len(graph) - 1
            self.assertEqual(proof_repl.local_cache_gap(book, cache), (wanted, wanted))
            if wanted:
                name = next(one for one in graph if one != book)
                key = proof_repl.certs.closure_key(proof_repl.ROOT, name)[0]
                with mock.patch.object(proof_repl.certs, "cached_entries",
                                       lambda c, k: [(c, {"toolchain_identity": "t"})]
                                       if k == key else []):
                    self.assertEqual(proof_repl.local_cache_gap(book, cache, "t"),
                                     (wanted - 1, wanted))
                    self.assertEqual(proof_repl.local_cache_gap(book, cache, "other"),
                                     (wanted, wanted))
        self.assertEqual(proof_repl.local_cache_gap("books/no-such-book", cache), (1, 1))

    def test_a_reserved_host_is_named_at_once_and_a_long_lease_refused(self):
        # config-and-legacy, operations: 10 and 13 silent minutes in boxes.sh wait.
        line = "boxes: persvati reserved by chain-scheduler until 22:54Z (40 min left): curve"
        held = lambda: (4, line + "\n")  # noqa: E731
        waited = []
        with contextlib.redirect_stderr(io.StringIO()) as err:
            with self.assertRaises(SystemExit) as refused:
                proof_repl.refuse_or_wait_for_lease("persvati", 2, held,
                                                    lambda: waited.append(1) or 0)
        self.assertEqual(waited, [])
        self.assertIn("reserved by chain-scheduler until 22:54Z (40 min left)", err.getvalue())
        self.assertIn("--host auto", str(refused.exception))
        self.assertIn("--lease-wait 41", str(refused.exception))
        with contextlib.redirect_stderr(io.StringIO()) as err:
            proof_repl.refuse_or_wait_for_lease("persvati", 60, held,
                                                lambda: waited.append(1) or 0)
        self.assertEqual(waited, [1])
        self.assertIn("chain-scheduler", err.getvalue())
        proof_repl.refuse_or_wait_for_lease("persvati", 2, lambda: (0, ""),
                                            lambda: self.fail("waited on a free box"))

    def test_a_session_remembers_its_host_for_later_commands(self):
        # full-vs-uncertain: send-range after a failed start needed --host again.
        name = "remember-host-test"
        self.addCleanup(shutil.rmtree, proof_repl.session_dir(name), True)
        proof_repl.remember_host(name, "persvati", "/t", "books/x", "l")
        self.assertEqual(proof_repl.recorded_host(name), "persvati")
        seen = []
        with mock.patch.object(proof_repl, "run_remote",
                               lambda args, argv: seen.append((args.host, argv)) or 0), \
                contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(proof_repl.main(["status", name]), 0)
        self.assertEqual(seen[0][0], "persvati")
        proof_repl.remember_host(name, None)
        self.assertIsNone(proof_repl.recorded_host(name))
        self.assertIsNone(proof_repl.recorded_host(None))

    def test_laptop_offer_needs_a_qualified_launcher(self):
        with tempfile.TemporaryDirectory() as temporary:
            unqualified = pathlib.Path(temporary) / "acl2"
            unqualified.write_text('#!/bin/sh\nexec /bin/sbcl --core /x ${SBCL_USER_ARGS} "$@"\n')
            unqualified.chmod(0o755)
            with mock.patch.object(proof_repl.socket, "gethostname", return_value="laptop"):
                self.assertIsNone(proof_repl.laptop_offer({"FN_ACL2": str(unqualified)}))
                self.assertIsNone(proof_repl.laptop_offer({"FN_REPL_LAPTOP": "0"}))
            with mock.patch.object(proof_repl.socket, "gethostname", return_value="hbox"):
                self.assertIsNone(proof_repl.laptop_offer({"FN_ACL2": str(unqualified)}))

    def test_the_local_launcher_file_is_the_default_acl2_off_the_boxes(self):
        with tempfile.TemporaryDirectory() as temporary:
            named = pathlib.Path(temporary) / "acl2-file"
            named.write_text("/opt/fn/acl2-literal\n")
            env = {"FN_ACL2_FILE": str(named)}
            self.assertEqual(proof_repl.apply_local_defaults(env), "/opt/fn/acl2-literal")
            self.assertEqual(env["FN_ACL2"], "/opt/fn/acl2-literal")
            mine = {"FN_ACL2_FILE": str(named), "FN_ACL2": "/mine"}
            self.assertIsNone(proof_repl.apply_local_defaults(mine))
            self.assertEqual(mine["FN_ACL2"], "/mine")
            absent = {"FN_ACL2_FILE": str(named) + ".absent"}
            self.assertIsNone(proof_repl.apply_local_defaults(absent))
            self.assertNotIn("FN_ACL2", absent)

    def test_the_sync_is_tools_and_the_closure_never_planning(self):
        files = proof_repl.sync_files(["books/wildmat"], ["tests/acl2/extra.lisp"])
        self.assertIn("tools/proof_repl.py", files)
        self.assertIn("books/wildmat.lisp", files)
        self.assertIn("tests/acl2/extra.lisp", files)
        # The host files a session may `ld` (item 14).
        self.assertIn("host/owner-host.lisp", files)
        self.assertFalse(any(name.startswith("planning/") for name in files))
        self.assertFalse(any("__pycache__" in name or name.endswith(".pyc") for name in files))
        closure = proof_repl.include_graph(proof_repl.ROOT, "books/wildmat")
        self.assertEqual({name for name in files if name.startswith("books/")},
                         {f"{name}.lisp" for name in closure})

    def test_a_farm_box_defaults_its_own_acl2_and_cache(self):
        import farm
        env = {}
        self.assertEqual(proof_repl.apply_box_defaults(env, "persvati.local"), "persvati")
        self.assertEqual(env["FN_ACL2"], farm.HOSTS["persvati"]["acl2"])
        self.assertEqual(env["FN_CERT_CACHE"],
                         os.path.expanduser(farm.HOSTS["persvati"]["cache"]))
        mine = {"FN_ACL2": "/mine"}
        proof_repl.apply_box_defaults(mine, "hbox")
        self.assertEqual(mine["FN_ACL2"], "/mine")
        self.assertEqual(mine["FN_CERT_CACHE"], farm.HOSTS["hbox"]["cache"])
        laptop = {}
        self.assertIsNone(proof_repl.apply_box_defaults(laptop, "embers-laptop"))
        self.assertEqual(laptop, {})


class SourceDependencyTests(unittest.TestCase):
    def test_ld_takes_a_dependency_and_its_includers_out_of_the_certificate_set(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            with mock.patch.object(proof_repl, "ROOT", root), \
                 mock.patch.dict(os.environ, {"FN_ACL2": temporary + "/acl2"}), \
                 mock.patch.object(proof_repl.certs, "cache_directory",
                                   return_value=pathlib.Path(temporary) / "cache"):
                ok, detail, order = proof_repl.install_closure(
                    "tests/acl2/mid-tests", ["books/base.lisp"])
                refused, why, _ = proof_repl.install_closure(
                    "books/mid", ["tests/acl2/mid-tests"])
        self.assertTrue(ok, detail)
        self.assertEqual(order, ["books/base", "books/mid"])
        self.assertIn("from source, in this order: books/base, books/mid", detail)
        self.assertFalse(refused)
        self.assertIn("--ld takes a DEPENDENCY of books/mid", why)
        self.assertIn("books/mid does not include tests/acl2/mid-tests", why)

    def test_ld_of_the_session_book_itself_says_it_takes_a_dependency(self):
        # obstructions-5 item 42 (bp-remainder-2 read the old text the other way).
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            with mock.patch.object(proof_repl, "ROOT", root):
                refused, why, _ = proof_repl.install_closure(
                    "tests/acl2/mid-tests", ["tests/acl2/mid-tests"])
        self.assertFalse(refused)
        self.assertIn("not the book itself", why)
        self.assertIn("--ld books/X", why)

    def test_a_bare_book_name_resolves_under_books(self):
        # obstructions-9 item 78: `--source-deps base` lost three sessions.
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            (root / "books" / "sub").mkdir()
            (root / "books" / "sub" / "deep.lisp").write_text("(in-package \"ACL2\")\n")
            with mock.patch.object(proof_repl, "ROOT", root), \
                 mock.patch.dict(os.environ, {"FN_ACL2": temporary + "/acl2"}), \
                 mock.patch.object(proof_repl.certs, "cache_directory",
                                   return_value=pathlib.Path(temporary) / "cache"):
                names = [proof_repl.normalize_book(one)
                         for one in ("base", "base.lisp", "deep", "books/mid", "nowhere")]
                ok, detail, order = proof_repl.install_closure("tests/acl2/mid-tests", ["base"])
        self.assertEqual(names, ["books/base", "books/base", "books/sub/deep", "books/mid",
                                 "nowhere"])
        self.assertTrue(ok, detail)
        self.assertEqual(order, ["books/base", "books/mid"])


class RefusalHeadlineTests(unittest.TestCase):
    """Item 27: a refused start says `--ld books/X` on its first line."""

    GRAPH = {"tests/acl2/mid-tests": ["books/mid", "books/base"],
             "books/mid": ["books/base"], "books/base": []}

    def test_the_headline_names_the_root_cause_and_the_ld_command(self):
        line = proof_repl.refusal_headline(self.GRAPH, ["books/base", "books/mid"])
        self.assertTrue(line.startswith("proof-repl: REFUSED"), line)
        self.assertIn("books/base.lisp (and 1 book(s) that include it)", line)
        self.assertIn("`--ld books/base`", line)
        self.assertNotIn("--ld books/mid", line)
        self.assertIn("--certify-missing", line)

    def test_install_closure_refusal_leads_with_it(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            cache = pathlib.Path(temporary) / "cache"
            cache.mkdir()
            fake_acl2 = pathlib.Path(temporary) / "acl2"
            fake_acl2.write_text("#!/bin/sh\nexit 0\n")
            fake_acl2.chmod(0o755)
            with mock.patch.object(proof_repl, "ROOT", root), \
                 mock.patch.dict(os.environ, {"FN_ACL2": str(fake_acl2)}), \
                 mock.patch.object(proof_repl.certs, "cache_directory", return_value=cache), \
                 mock.patch.object(proof_repl.acl2_toolchain, "fingerprint",
                                   return_value=SimpleNamespace(
                                       qualified=True,
                                       identity=proof_repl.certs.stable_identity(
                                           TEST_COMPATIBILITY), reason="")), \
                 mock.patch.object(proof_repl.acl2_slots, "slot",
                                   side_effect=lambda label: nullcontext()):
                ok, detail, _ = proof_repl.install_closure("tests/acl2/mid-tests")
        self.assertFalse(ok)
        first = detail.splitlines()[0]
        self.assertTrue(first.startswith("proof-repl: REFUSED"), detail)
        self.assertIn("--ld books/base", first)


class CertifyMissingTestBookTests(unittest.TestCase):
    """Item 30: `start --certify-missing` on a tests/acl2 book whose
    dependency is uncertified certifies it and then starts (bp-remainder saw a
    refusal "no cached certificate" after the certify run said nothing left)."""

    def run_start(self, temporary, break_install_set=False):
        from tests.test_certs import SERIALIZED
        root = worktree(temporary + "/tree", certified=["books/base"])
        cache = pathlib.Path(temporary) / "cache"
        base_manifest = manifest_for(root, ["books/base"], write=False)
        base_manifest["compiled_digests_sha256"] = {
            "books/base": proof_repl.certs.content_hash(root / "books/base.fasl")}
        proof_repl.certs.publish(root, cache, [base_manifest], ["books/base"],
                                 origin="/farm/run-base", origin_kind="run")
        fake_acl2 = pathlib.Path(temporary) / "acl2"
        fake_acl2.write_text("#!/bin/sh\nexit 0\n")
        fake_acl2.chmod(0o755)
        certified = []

        def certify(command, cwd=None, stdout=None, stderr=None):
            # What certify_books.py --incremental does for books/mid: a
            # compiled pair in the tree, published under this worktree.
            books = [word for word in command if word.startswith("books/")]
            certified.extend(books)
            for name in books:
                (root / f"{name}.cert").write_bytes(SERIALIZED + name.encode())
                (root / f"{name}.port").write_text("; port\n")
                (root / f"{name}.fasl").write_bytes(b"FASL " + name.encode())
                manifest = manifest_for(root, [name], write=False)
                manifest["compiled_digests_sha256"] = {
                    name: proof_repl.certs.content_hash(root / f"{name}.fasl")}
                proof_repl.certs.publish(root, cache, [manifest], [name], origin=str(root))
            return subprocess.CompletedProcess(command, 0)

        real_sets = proof_repl.certs.artifact_sets
        calls = {"n": 0}

        def sets(*args, **kwargs):
            calls["n"] += 1
            return [] if break_install_set and certified else real_sets(*args, **kwargs)

        with mock.patch.object(proof_repl, "ROOT", root), \
             mock.patch.dict(os.environ, {"FN_ACL2": str(fake_acl2)}), \
             mock.patch.object(proof_repl.certs, "cache_directory", return_value=cache), \
             mock.patch.object(proof_repl.acl2_toolchain, "fingerprint",
                               return_value=SimpleNamespace(
                                   qualified=True,
                                   identity=proof_repl.certs.stable_identity(TEST_COMPATIBILITY),
                                   reason="")), \
             mock.patch.object(proof_repl.acl2_slots, "slot",
                               side_effect=lambda label: nullcontext()), \
             mock.patch.object(proof_repl.certs.cert_alists, "acl2_certificate_pairs",
                               side_effect=lambda paths, pairs, acl2, root:
                                   {pair: (True, True) for pair in pairs}), \
             mock.patch.object(proof_repl.certs, "artifact_sets", sets), \
             mock.patch.object(proof_repl.subprocess, "run", certify):
            ok, detail, order = proof_repl.install_closure(
                "tests/acl2/mid-tests", auto="certify")
        return root, ok, detail, certified

    def test_the_certified_dependency_installs_and_the_session_starts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, ok, detail, certified = self.run_start(temporary)
            self.assertEqual(certified, ["books/mid"])
            self.assertTrue(ok, detail)
            self.assertNotIn("REFUSED", detail)
            self.assertTrue((root / "books/mid.cert").is_file())
            self.assertTrue((root / "books/base.fasl").is_file())

    def test_install_set_short_after_the_certify_takes_the_runners_install(self):
        with tempfile.TemporaryDirectory() as temporary:
            root, ok, detail, certified = self.run_start(temporary, break_install_set=True)
            self.assertEqual(certified, ["books/mid"])
            self.assertTrue(ok, detail)
            self.assertIn("install-partial) covers the closure", detail)
            self.assertTrue((root / "books/base.cert").is_file())
            self.assertTrue((root / "books/mid.cert").is_file())


class GraphTests(unittest.TestCase):
    GRAPH = {"t": ["m", "b"], "m": ["b"], "b": [], "z": []}

    def test_dependents_and_order(self):
        self.assertEqual(proof_repl.dependents_of(self.GRAPH, ["b"]), {"t", "m", "b"})
        self.assertEqual(proof_repl.dependents_of(self.GRAPH, ["z"]), {"z"})
        self.assertEqual(proof_repl.dependency_order(self.GRAPH, {"m", "b", "t"}),
                         ["b", "m", "t"])

    def test_diagnosis_names_the_root_cause_and_what_follows_it(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            (root / "books" / "base.cert").write_text("stale")
            cache = pathlib.Path(temporary) / "cache"
            cache.mkdir()
            with mock.patch.object(proof_repl, "ROOT", root):
                graph = proof_repl.include_graph(root, "tests/acl2/mid-tests")
                lines = proof_repl.diagnose(graph, ["books/base", "books/mid"], cache)
                fixes = proof_repl.fixes(["books/base", "books/mid"], 2)
        text = "\n".join(lines)
        self.assertIn("2 of this book's dependencies", text)
        self.assertIn("books/base.lisp sha256 ", text)
        self.assertIn("was ever published to this cache", text)
        self.assertIn("a local books/base.cert exists", text)
        self.assertIn("include one of the above (1): books/mid", text)
        self.assertNotIn("books/mid.lisp sha256", text)
        self.assertIn("tools/certify_books.py --incremental --jobs 2 books/base books/mid",
                      "\n".join(fixes))

    def test_diagnosis_names_a_toolchain_mismatch(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            cache = pathlib.Path(temporary) / "cache"
            with mock.patch.object(proof_repl, "ROOT", root):
                key = proof_repl.certs.closure_key(root, "books/base")[0]
                entry = cache / key / "0123456789abcdef"
                entry.mkdir(parents=True)
                (entry / "meta.json").write_text(json.dumps({"toolchain_identity": "d5f2b9f0" * 8}))
                graph = proof_repl.include_graph(root, "books/mid")
                text = "\n".join(proof_repl.diagnose(graph, ["books/base"], cache, "1b4169e9" * 8))
        self.assertIn("only for ACL2 toolchain(s) d5f2b9f0, and this ACL2 is 1b4169e9", text)


class UncompiledDiagnosisTests(unittest.TestCase):
    def test_diagnosis_names_a_cache_entry_without_its_fasl(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = worktree(temporary + "/tree")
            cache = pathlib.Path(temporary) / "cache"
            with mock.patch.object(proof_repl, "ROOT", root):
                key = proof_repl.certs.closure_key(root, "books/base")[0]
                entry = cache / key / "0123456789abcdef"
                entry.mkdir(parents=True)
                (entry / "meta.json").write_text(json.dumps(
                    {"toolchain_identity": "1b4169e9" * 8, "fasl_sha256": None}))
                graph = proof_repl.include_graph(root, "books/mid")
                text = "\n".join(proof_repl.diagnose(graph, ["books/base"], cache, "1b4169e9" * 8))
        self.assertIn("only without their compiled file (.fasl)", text)


class CacheStartupTests(unittest.TestCase):
    def test_incompatible_cached_parent_and_child_refuse_without_session(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            older = worktree(str(base / "older"), certified=["books/base"])
            parent = worktree(str(base / "parent"), certified=["books/mid"])
            target = worktree(str(base / "target"), certified=["books/base", "books/mid"])
            cache = base / "cache"
            toolchain = proof_repl.certs.stable_identity(TEST_COMPATIBILITY)
            for source, name, origin in (
                    (older, "books/base", "/farm/base"),
                    (parent, "books/mid", "/farm/parent")):
                proof_repl.certs.publish(
                    source, cache, [manifest_for(source, [name], write=False)],
                    [name], origin=origin, origin_kind="run")
            fake_acl2 = base / "acl2"
            fake_acl2.write_text("#!/bin/sh\nexit 0\n")
            fake_acl2.chmod(0o755)
            sessions = base / "sessions"
            args = SimpleNamespace(name="bad-cache", book="tests/acl2/mid-tests")
            with mock.patch.object(proof_repl, "ROOT", target), \
                 mock.patch.object(proof_repl, "SESSIONS", sessions), \
                 mock.patch.dict(os.environ, {"FN_ACL2": str(fake_acl2)}), \
                 mock.patch.object(proof_repl.certs, "cache_directory",
                                   return_value=cache), \
                 mock.patch.object(proof_repl.acl2_toolchain, "fingerprint",
                                   return_value=SimpleNamespace(
                                       qualified=True, identity=toolchain,
                                       reason="")), \
                 mock.patch.object(proof_repl.acl2_slots, "slot",
                                   side_effect=lambda label: nullcontext()), \
                 mock.patch.object(proof_repl.certs.cert_alists,
                                   "acl2_certificate_pairs",
                                   side_effect=lambda paths, pairs, acl2, root:
                                       {pair: (True, False) for pair in pairs}), \
                 mock.patch.object(proof_repl.subprocess, "Popen") as launched:
                self.assertEqual(proof_repl.start(args), 1)
                launched.assert_not_called()
            self.assertFalse((sessions / "bad-cache").exists())
            self.assertFalse((target / "books/base.cert").exists())
            self.assertFalse((target / "books/mid.cert").exists())


class ProcessLifetimeTests(unittest.TestCase):
    def test_start_preserves_an_old_live_json_server(self):
        with tempfile.TemporaryDirectory() as temporary:
            sessions = pathlib.Path(temporary)
            directory = sessions / "old-session"
            directory.mkdir()
            listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            listener.bind(str(directory / "sock"))
            listener.listen(1)
            received = []

            def answer():
                connection, _ = listener.accept()
                with connection:
                    received.append(json.loads(proof_repl.read_all(connection)))
                    connection.sendall(b'{"state":{"ready":true}}')

            worker = threading.Thread(target=answer)
            worker.start()
            try:
                args = SimpleNamespace(name="old-session", book="books/irrelevant")
                with mock.patch.object(proof_repl, "SESSIONS", sessions), \
                     mock.patch.object(proof_repl, "install_closure") as acquire:
                    self.assertEqual(proof_repl.start(args), 2)
                    acquire.assert_not_called()
                self.assertTrue(worker.is_alive(), "start must not touch the old socket")
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                    client.connect(str(directory / "sock"))
                    client.sendall(b'{"op":"status"}')
                    client.shutdown(socket.SHUT_WR)
                    self.assertEqual(json.loads(proof_repl.read_all(client)),
                                     {"state": {"ready": True}})
                worker.join(timeout=2)
                self.assertEqual(received, [{"op": "status"}])
                self.assertTrue((directory / "sock").exists())
            finally:
                listener.close()

    def test_stopping_busy_session_stops_descendants_and_releases_output(self):
        # A busy prover can have its own child holding the output pipe open.
        # The old wrapper-only kill left both alive until their sleep ended.
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "busy-acl2"
            child = "import time; print('DESCENDANT_READY', flush=True); time.sleep(60)"
            fake.write_text("#!" + sys.executable + "\nimport subprocess, sys, time\n"
                            + "subprocess.Popen([sys.executable, '-c', " + repr(child) + "])\n"
                            + "time.sleep(60)\n")
            fake.chmod(0o755)
            with mock.patch.dict(os.environ, {"FN_ACL2": str(fake),
                    "FN_ACL2_SLOT_DIR": str(base / "slots"), "FN_ACL2_SLOTS": "1"}):
                session = proof_repl.Acl2("busy-test", base / "log")
                try:
                    self.assertEqual(session.lines.get(timeout=10).strip(), "DESCENDANT_READY")
                    session.kill()
                    self.assertIsNotNone(session.process.returncode)
                    self.assertFalse(session.reader.is_alive())
                    self.assertTrue(session.log.closed)
                    # Stop is idempotent after the owned process group is gone.
                    session.kill()
                finally:
                    if not session._terminated:
                        session.kill()

    def test_duplicate_start_cannot_detach_an_older_server(self):
        # The first start holds the name while its fake ACL2 is still loading.
        # A retry must not replace its socket and leave its child behind.
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "slow-acl2"
            heartbeat = base / "heartbeat"
            child = (
                "import os,time; from pathlib import Path; "
                "p=Path(os.environ['FN_REPL_TEST_HEARTBEAT']); "
                "\nwhile True:\n"
                " with p.open('a') as stream: stream.write('x')\n"
                " time.sleep(.05)\n"
            )
            fake.write_text(
                "#!" + sys.executable + "\nimport subprocess,sys,time\n"
                + "subprocess.Popen([sys.executable, '-c', " + repr(child) + "])\n"
                + "time.sleep(1)\n"
                + "for line in sys.stdin:\n"
                + " if '(good-bye)' in line: break\n"
                + " if 'FN-REPL-DONE ' in line:\n"
                + "  print('FN-REPL-DONE ' + line.split('FN-REPL-DONE ')[1].split('~%')[0], flush=True)\n"
            )
            fake.chmod(0o755)
            scratch = ROOT / "build" / ("proof-repl-lock-test-" + str(os.getpid()))
            scratch.mkdir(parents=True, exist_ok=True)
            (scratch / "tiny.lisp").write_text('(in-package "ACL2")\n')
            name = "lock-test-" + str(os.getpid())
            env = {**os.environ, "FN_ACL2": str(fake),
                   "FN_ACL2_SLOT_DIR": str(base / "slots"),
                   "FN_ACL2_SLOTS": "1",
                   "FN_REPL_TEST_HEARTBEAT": str(heartbeat)}
            command = [sys.executable, str(ROOT / "tools" / "proof_repl.py")]
            first = subprocess.Popen(
                command + ["start", name, str((scratch / "tiny").relative_to(ROOT)),
                           "--load-timeout", "10"],
                cwd=ROOT, env=env, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, text=True,
            )
            try:
                lock = proof_repl.session_lock_path(name)
                deadline = time.monotonic() + 5
                while not lock.exists() and time.monotonic() < deadline:
                    time.sleep(.01)
                self.assertTrue(lock.exists())
                second = subprocess.run(
                    command + ["start", name,
                               str((scratch / "tiny").relative_to(ROOT)),
                               "--load-timeout", "10"],
                    cwd=ROOT, env=env, capture_output=True, text=True, timeout=5,
                )
                self.assertEqual(second.returncode, 2, second.stdout + second.stderr)
                self.assertIn("starting or live", second.stdout)
                out, err = first.communicate(timeout=15)
                self.assertEqual(first.returncode, 0, out + err)
                self.assertTrue(heartbeat.exists())
                stopped = subprocess.run(command + ["stop", name], cwd=ROOT,
                                         env=env, capture_output=True, text=True,
                                         timeout=15)
                self.assertEqual(stopped.returncode, 0,
                                 stopped.stdout + stopped.stderr)
                count = len(heartbeat.read_text())
                time.sleep(.2)
                self.assertEqual(len(heartbeat.read_text()), count)
                self.assertFalse((proof_repl.session_dir(name) / "sock").exists())
            finally:
                if first.poll() is None:
                    first.terminate()
                    first.wait(timeout=5)
                if (proof_repl.session_dir(name) / "sock").exists():
                    subprocess.run(command + ["stop", name], cwd=ROOT, env=env,
                                   capture_output=True, timeout=15)
                shutil.rmtree(proof_repl.session_dir(name), ignore_errors=True)
                shutil.rmtree(scratch, ignore_errors=True)


class SessionTests(unittest.TestCase):
    """The protocol against a fake ACL2, end to end through the command line."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        fake = pathlib.Path(cls.tmp.name) / "fake-acl2"
        fake.write_text(FAKE_ACL2)
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        cls.env = {**os.environ, "FN_ACL2": str(fake)}
        cls.scratch = ROOT / "build" / "proof-repl-test"
        cls.scratch.mkdir(parents=True, exist_ok=True)
        (cls.scratch / "scratch.lisp").write_text(
            '(in-package "ACL2")\n(defun f (x) x)\n(defthm bad (equal 1 2))\n'
            "(defthm never (equal 2 2))\n")
        cls.name = "test-%d" % os.getpid()

    @classmethod
    def tearDownClass(cls):
        cls.cli("stop", cls.name)
        shutil.rmtree(proof_repl.SESSIONS / cls.name, ignore_errors=True)
        shutil.rmtree(cls.scratch, ignore_errors=True)
        cls.tmp.cleanup()

    @classmethod
    def cli(cls, *words, timeout=120):
        return subprocess.run([sys.executable, str(ROOT / "tools" / "proof_repl.py"), *words],
                              capture_output=True, text=True, env=cls.env, cwd=ROOT,
                              timeout=timeout)

    def test_1_start_loads_up_to_the_first_refused_form_and_reports_it(self):
        result = self.cli("start", self.name, "build/proof-repl-test/scratch",
                          "--limit", "5", "--load-timeout", "20")
        self.assertEqual(result.returncode, proof_repl.PARTIAL_LOAD,
                         result.stdout + result.stderr)
        self.assertIn("stopped at bad", result.stdout)
        self.assertIn("PARTIAL LOAD -- stopped at bad",
                      result.stdout.strip().splitlines()[-1])
        state = json.loads((proof_repl.SESSIONS / self.name / "state.json").read_text())
        self.assertEqual(state["loaded"], ["in-package", "f"])
        self.assertTrue(state["ready"])

    def test_2_send_answers_with_the_trimmed_output_and_the_exit_says_error(self):
        ok = self.cli("send", self.name, "(defthm good t)", "--limit", "5")
        self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)
        self.assertIn("*** Key checkpoint", ok.stdout)
        self.assertNotIn("Subgoal *1/50", ok.stdout)
        full = self.cli("send", self.name, "(defthm good t)", "--full")
        self.assertIn("Subgoal *1/50", full.stdout)
        bad = self.cli("send", self.name, "(defthm bad t)")
        self.assertEqual(bad.returncode, 1)
        self.assertIn("ACL2 Error", bad.stdout)
        two = self.cli("send", self.name, "(a) (b)")
        self.assertEqual(two.returncode, 0, two.stdout)
        self.assertIn("ok      #1 a", two.stdout)
        self.assertIn("[total: 2 forms, 0 refused", two.stdout)
        broken = self.cli("send", self.name, "(a (b)")
        self.assertEqual(broken.returncode, 1)
        self.assertIn("not one complete form", broken.stdout)
        log = (proof_repl.SESSIONS / self.name / "log").read_text()
        self.assertIn(">>> (with-prover-time-limit 5 (defthm good t))", log)

    def test_2b_send_range_reports_each_forms_cost_and_stops_at_a_refusal(self):
        listing = self.cli("forms", "build/proof-repl-test/scratch")
        self.assertEqual(listing.stdout.splitlines(),
                         ["#1 in-package", "#2 defun f", "#3 defthm bad", "#4 defthm never"])
        ranged = self.cli("send-range", self.name, "build/proof-repl-test/scratch",
                          "--from", "f", "--until", "never")
        self.assertEqual(ranged.returncode, 1, ranged.stdout)
        self.assertIn("forms #2-#3 of build/proof-repl-test/scratch (2 to send)", ranged.stdout)
        self.assertIn("ok      #2 defun f: ACL2 time 0.50 s; prover steps 1,234", ranged.stdout)
        self.assertIn("REFUSED #3 defthm bad", ranged.stdout)
        self.assertIn("resume with --from #3", ranged.stdout)
        self.assertIn("[total: 2 forms, 1 refused; ACL2 time 0.50 s; prover steps 1,234",
                      ranged.stdout)
        onward = self.cli("send-range", self.name, "build/proof-repl-test/scratch",
                          "--from", "#3", "--keep-going")
        self.assertIn("REFUSED #3 defthm bad", onward.stdout)
        self.assertIn("ok      #4 defthm never", onward.stdout)
        one = self.cli("send", self.name, "(defthm good t)")
        self.assertIn("[ACL2 time 0.50 s; prover steps 1,234]", one.stdout)
        self.assertIn("lines cut", one.stdout)
        self.assertTrue((proof_repl.SESSIONS / self.name / "last-output.txt").is_file())

    def test_2c_probe_proves_a_copy_beside_the_session(self):
        (self.scratch / "probe.lisp").write_text(
            '(in-package "ACL2")\n(defun f (x) x)\n(defthm g1 (equal 1 1))\n'
            '(defthm g2 (equal (f x) x) :hints (("Goal" :in-theory (enable f))))\n')
        before = json.loads((proof_repl.SESSIONS / self.name / "state.json").read_text())
        probe = self.name + ".probe"
        try:
            first = self.cli("probe", self.name, "g2", "--book",
                             "build/proof-repl-test/probe", "--hints", "(nil)")
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            self.assertIn("loading build/proof-repl-test/probe up to #4", first.stdout)
            self.assertIn("[probe #4 defthm g2 of build/proof-repl-test/probe: admitted",
                          first.stdout)
            again = self.cli("probe", self.name, "g2", "--book",
                             "build/proof-repl-test/probe", "--stop")
            self.assertIn("reusing", again.stdout)
            self.assertIn("world at its checkpoint: clean", again.stdout)
            log = (proof_repl.SESSIONS / probe / "log").read_text()
            self.assertIn('(defthm g2-probe (equal (f x) x) :hints (nil))', log)
            self.assertIn("(ubu! 'fn-probe-base)", log)
            self.assertIn("[probe undone: world back at its checkpoint", first.stdout)
            state = json.loads((proof_repl.SESSIONS / probe / "state.json").read_text())
            self.assertEqual(state["loaded"], ["in-package", "f", "g1"])
        finally:
            self.cli("stop", probe)
            shutil.rmtree(proof_repl.SESSIONS / probe, ignore_errors=True)
        after = json.loads((proof_repl.SESSIONS / self.name / "state.json").read_text())
        self.assertEqual(after["sends"], before["sends"])

    def test_2d_a_probe_undoes_what_was_left_above_its_checkpoint_and_takes_several_forms(self):
        (self.scratch / "probe2.lisp").write_text(
            '(in-package "ACL2")\n(defun f (x) x)\n(defthm g2 (equal (f x) x))\n')
        probe = self.name + ".probe"
        book = "build/proof-repl-test/probe2"
        try:
            first = self.cli("probe", self.name, "g2", "--book", book)
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            # A trial sent by hand to the probe session stays as a rule...
            self.assertEqual(self.cli("send", probe, "(defthm trial t)").returncode, 0)
            # ...until the next probe undoes it before it runs.
            again = self.cli("probe", self.name, "g2", "--book", book,
                             "--form", "(defthm helper t)\n(defthm g2 (equal (f x) x))",
                             "--hints", "(nil)")
            self.assertEqual(again.returncode, 0, again.stdout + again.stderr)
            self.assertIn("undid 1 command(s) above the checkpoint", again.stdout)
            self.assertIn("ok      #1 defthm helper", again.stdout)
            self.assertIn("ok      #2 defthm g2-probe", again.stdout)
            self.assertIn("(2 forms): admitted", again.stdout)
            log = (proof_repl.SESSIONS / probe / "log").read_text()
            self.assertIn("(defthm g2-probe (equal (f x) x) :hints (nil))", log)
            self.assertIn("(defthm helper t)", log)
            refused = self.cli("probe", self.name, "g2", "--book", book, "--stop",
                               "--form", "(defthm bad t) (defthm g2 t)")
            self.assertEqual(refused.returncode, 1)
            self.assertIn("REFUSED #1 defthm bad", refused.stdout)
            self.assertNotIn("#2 defthm g2", refused.stdout)
            self.assertIn("[probe undone", refused.stdout)
        finally:
            self.cli("stop", probe)
            shutil.rmtree(proof_repl.SESSIONS / probe, ignore_errors=True)

    def test_2e_keyword_commands_and_raw_lisp_aborts_do_not_hang_the_session(self):
        started = time.monotonic()
        ubt = self.cli("send", self.name, ":ubt!", "--limit", "60",
                       "--allow-undo")
        self.assertEqual(ubt.returncode, 0, ubt.stdout)
        self.assertLess(time.monotonic() - started, 30)
        one = self.cli("send", self.name, ":ubt! foo", "--allow-undo")
        self.assertEqual(one.returncode, 0, one.stdout)
        self.assertNotIn("#1", one.stdout)  # one command, not two forms
        abort = self.cli("send", self.name, "(raw-abort)")
        self.assertEqual(abort.returncode, 1, abort.stdout)
        self.assertIn("raw-Lisp abort", abort.stdout)
        after = self.cli("send", self.name, "(+ 1 2)")
        self.assertEqual(after.returncode, 0, after.stdout)
        self.assertIn("GOT (+ 1 2)", after.stdout)
        self.assertNotIn("FN-REPL-DONE", after.stdout)

    def test_3_status_and_stop(self):
        status = self.cli("status", self.name)
        self.assertIn("live", status.stdout)
        self.assertIn("sends", status.stdout)
        stopped = self.cli("stop", self.name)
        self.assertEqual(stopped.returncode, 0, stopped.stdout)
        self.assertFalse((proof_repl.SESSIONS / self.name / "sock").exists())
        again = self.cli("send", self.name, "(defthm x t)")
        self.assertEqual(again.returncode, 1)


@unittest.skipUnless(shutil.which(os.environ.get("FN_ACL2", "acl2")), "no ACL2 on PATH")
class RealAcl2Tests(unittest.TestCase):
    def test_a_true_theorem_is_admitted_and_a_false_one_is_refused(self):
        scratch = ROOT / "build" / "proof-repl-real"
        scratch.mkdir(parents=True, exist_ok=True)
        (scratch / "tiny.lisp").write_text(
            '(in-package "ACL2")\n(defun f (x) x)\n(defthm f-id (equal (f x) x))\n')
        name = "real-%d" % os.getpid()
        cli = lambda *w: subprocess.run(  # noqa: E731
            [sys.executable, str(ROOT / "tools" / "proof_repl.py"), *w],
            capture_output=True, text=True, cwd=ROOT, timeout=300)
        try:
            started = cli("start", name, "build/proof-repl-real/tiny", "--upto", "f-id",
                          "--limit", "20")
            self.assertEqual(started.returncode, 0, started.stdout + started.stderr)
            self.assertIn("last loaded: f", started.stdout)
            good = cli("send", name, "(defthm f-id (equal (f x) x))")
            self.assertEqual(good.returncode, 0, good.stdout)
            self.assertIn("Summary", good.stdout)
            bad = cli("send", name, "(defthm f-wrong (equal (f x) 1))")
            self.assertEqual(bad.returncode, 1)
            self.assertIn("ACL2 Error", bad.stdout)
        finally:
            cli("stop", name)
            shutil.rmtree(proof_repl.SESSIONS / name, ignore_errors=True)
            shutil.rmtree(scratch, ignore_errors=True)

    def test_ld_local_takes_a_book_with_a_non_local_include_and_start_is_limited(self):
        scratch = ROOT / "build" / "proof-repl-real-ld"
        scratch.mkdir(parents=True, exist_ok=True)
        (scratch / "dep.lisp").write_text(
            '(in-package "ACL2")\n(include-book "std/lists/rev" :dir :system)\n'
            "(local (defthm dep-local (equal (car (cons x y)) x)))\n"
            "(defun dep-f (x) (rev x))\n")
        (scratch / "top.lisp").write_text(
            '(in-package "ACL2")\n(include-book "dep")\n(defun top-f (x) (dep-f x))\n'
            "(defthm slow (equal (len (append x y y x)) (+ (len x) (len x) (len y) "
            "(len y))))\n(defthm after (equal (car (cons a b)) a))\n")
        name = "real-ld-%d" % os.getpid()
        cli = lambda *w: subprocess.run(  # noqa: E731
            [sys.executable, str(ROOT / "tools" / "proof_repl.py"), *w],
            capture_output=True, text=True, cwd=ROOT, timeout=300)
        try:
            started = cli("start", name, "build/proof-repl-real-ld/top",
                          "--ld", "build/proof-repl-real-ld/dep",
                          "--load-limit", "0.001")  # encapsulated by default (item 32)
            # Stopped at `slow`: a partial load (item 25).
            self.assertEqual(started.returncode, proof_repl.PARTIAL_LOAD,
                             started.stdout + started.stderr)
            self.assertIn("in one encapsulate", started.stdout)
            self.assertIn("stopped at slow", started.stdout)
            self.assertIn("over the per-form prover limit (0.001 s", started.stdout)
            state = json.loads((proof_repl.SESSIONS / name / "state.json").read_text())
            self.assertEqual(state["loaded"], ["in-package", "top-f"])
            self.assertTrue(state["ready"])
            # The include came along, the local lemma did not.
            self.assertEqual(cli("send", name, "(defthm uses-rev (true-listp (rev x)))")
                             .returncode, 0)
            self.assertEqual(cli("send", name, ":pe dep-local").returncode, 1)
        finally:
            cli("stop", name)
            shutil.rmtree(proof_repl.SESSIONS / name, ignore_errors=True)
            shutil.rmtree(scratch, ignore_errors=True)


class OwnershipTests(unittest.TestCase):
    """PKT-346: a session carries its lane and an idle deadline; list and reap."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        fake = pathlib.Path(cls.tmp.name) / "fake-acl2"
        fake.write_text(FAKE_ACL2)
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)
        cls.env = {**os.environ, "FN_ACL2": str(fake),
                   "FN_ACL2_SLOT_DIR": str(pathlib.Path(cls.tmp.name) / "slots"),
                   "FN_ACL2_SLOTS": "4"}
        cls.scratch = ROOT / "build" / ("proof-repl-own-" + str(os.getpid()))
        cls.scratch.mkdir(parents=True, exist_ok=True)
        (cls.scratch / "tiny.lisp").write_text('(in-package "ACL2")\n(defun f (x) x)\n')
        cls.book = str((cls.scratch / "tiny").relative_to(ROOT))
        cls.names = []

    @classmethod
    def tearDownClass(cls):
        for name in cls.names:
            cls.cli("stop", name)
            shutil.rmtree(proof_repl.SESSIONS / name, ignore_errors=True)
        shutil.rmtree(cls.scratch, ignore_errors=True)
        cls.tmp.cleanup()

    @classmethod
    def cli(cls, *words, timeout=60):
        return subprocess.run([sys.executable, str(ROOT / "tools" / "proof_repl.py"), *words],
                              capture_output=True, text=True, env=cls.env, cwd=ROOT,
                              timeout=timeout)

    def start(self, suffix, *extra):
        name = f"own-{suffix}-{os.getpid()}"
        self.names.append(name)
        answer = self.cli("start", name, self.book, "--load-timeout", "20", *extra)
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        return name

    def state(self, name):
        return json.loads((proof_repl.SESSIONS / name / "state.json").read_text())

    def test_a_session_records_its_lane_and_stops_itself_when_idle(self):
        name = self.start("idle", "--lane", "lane-idle", "--idle-seconds", "1.5")
        state = self.state(name)
        self.assertEqual(state["lane"], "lane-idle")
        self.assertEqual(state["idle_seconds"], 1.5)
        self.assertIsInstance(state["acl2_pgid"], int)
        deadline = time.monotonic() + 20
        while time.monotonic() < deadline and (proof_repl.SESSIONS / name / "sock").exists():
            time.sleep(0.2)
        self.assertFalse((proof_repl.SESSIONS / name / "sock").exists())
        state = self.state(name)
        self.assertIn("idle", state["ended"])
        self.assertFalse(state["ready"])
        # The name, and with it the slot, is free again.
        fd = proof_repl.open_session_lock(name)
        self.assertIsNotNone(fd)
        os.close(fd)

    def test_stop_ends_a_start_stuck_in_its_load_and_the_refusal_names_it(self):
        (self.scratch / "slow.lisp").write_text('(in-package "ACL2")\n(sleep-form)\n')
        name = f"own-stuck-{os.getpid()}"
        self.names.append(name)
        book = str((self.scratch / "slow").relative_to(ROOT))
        starter = subprocess.Popen(
            [sys.executable, str(ROOT / "tools" / "proof_repl.py"), "start", name, book,
             "--load-timeout", "120"], env=self.env, cwd=ROOT,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                if proof_repl.lock_holder(name).get("role") == "serve":
                    break
                time.sleep(0.2)
            again = self.cli("start", name, book)
            self.assertEqual(again.returncode, 2)
            self.assertIn("held by pid", again.stdout)
            self.assertIn("still running", again.stdout)
            stopped = self.cli("stop", name)
            self.assertEqual(stopped.returncode, 0, stopped.stdout)
            self.assertIn("held the lock with no socket", stopped.stdout)
            fd = proof_repl.open_session_lock(name)
            self.assertIsNotNone(fd)
            os.close(fd)
        finally:
            starter.kill()
            starter.wait()

    def test_a_send_postpones_the_idle_deadline_and_a_status_does_not(self):
        name = self.start("busy", "--lane", "lane-busy", "--idle-seconds", "3")
        for _ in range(4):
            time.sleep(1)
            self.assertEqual(self.cli("send", name, "(+ 1 2)").returncode, 0)
        self.assertTrue((proof_repl.SESSIONS / name / "sock").exists())
        for _ in range(8):
            time.sleep(1)
            if not (proof_repl.SESSIONS / name / "sock").exists():
                break
            self.cli("status", name)
        self.assertFalse((proof_repl.SESSIONS / name / "sock").exists())

    def test_list_names_the_lane_and_reap_by_lane_stops_only_that_lane(self):
        mine = self.start("reap-a", "--lane", f"lane-a-{os.getpid()}")
        other = self.start("reap-b", "--lane", f"lane-b-{os.getpid()}")
        listing = self.cli("list")
        self.assertEqual(listing.returncode, 0, listing.stderr)
        row = next(line for line in listing.stdout.splitlines() if line.startswith(mine))
        self.assertIn(f"lane-a-{os.getpid()}", row)
        self.assertIn("live", row)
        self.assertIn("20m00s", row)  # the default deadline, stated
        dry = self.cli("reap", "--lane", f"lane-a-{os.getpid()}", "--dry-run")
        self.assertIn(f"would reap {mine}", dry.stdout)
        self.assertTrue((proof_repl.SESSIONS / mine / "sock").exists())
        reaped = self.cli("reap", "--lane", f"lane-a-{os.getpid()}")
        self.assertIn(f"reaped {mine}", reaped.stdout)
        self.assertIn("stopped through its socket", reaped.stdout)
        self.assertNotIn(other, reaped.stdout)
        self.assertFalse((proof_repl.SESSIONS / mine / "sock").exists())
        self.assertTrue((proof_repl.SESSIONS / other / "sock").exists())
        self.assertEqual(self.cli("stop", other).returncode, 0)

    def test_reap_signals_only_pids_that_are_still_the_session(self):
        # A dead server whose recorded PIDs now belong to unrelated processes:
        # reap removes the stale socket and signals nobody.
        with tempfile.TemporaryDirectory() as temporary:
            sessions = pathlib.Path(temporary)
            stranger = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
            try:
                directory = sessions / "ghost"
                directory.mkdir()
                (directory / "state.json").write_text(json.dumps({
                    "name": "ghost", "book": "books/x", "pid": stranger.pid,
                    "acl2_pgid": stranger.pid, "loaded": [], "sends": 0,
                    "lane": "gone", "idle_seconds": 1, "last_active": 0}))
                (directory / "sock").write_text("")
                with mock.patch.object(proof_repl, "SESSIONS", sessions):
                    rows = proof_repl.session_rows()
                    self.assertFalse(rows[0]["server"])
                    self.assertEqual(proof_repl.reap_reason(rows[0], None, None), "dead server")
                    self.assertEqual(proof_repl.reap_one(rows[0]), "removed a stale socket")
                self.assertIsNone(stranger.poll())
                self.assertFalse((directory / "sock").exists())
            finally:
                stranger.kill()
                stranger.wait()

    def test_an_older_sessions_idle_time_is_its_state_files_age(self):
        with tempfile.TemporaryDirectory() as temporary:
            sessions = pathlib.Path(temporary)
            directory = sessions / "old"
            directory.mkdir()
            state_path = directory / "state.json"
            state_path.write_text(json.dumps({"name": "old", "book": "books/x",
                                              "pid": 999999, "loaded": [], "sends": 0}))
            os.utime(state_path, (time.time() - 7200, time.time() - 7200))
            with mock.patch.object(proof_repl, "SESSIONS", sessions):
                row = proof_repl.session_rows()[0]
            self.assertGreaterEqual(row["idle"], 7199)
            self.assertIsNone(row["deadline"])
            self.assertIsNone(proof_repl.reap_reason(row, None, None))  # dead, nothing held

    def test_the_default_lane_is_the_trees_lane(self):
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("FN_LANE", None)
            self.assertEqual(proof_repl.default_lane(pathlib.Path("/x/build/lanes/tv")), "tv")
            self.assertEqual(proof_repl.default_lane(pathlib.Path("/h/fn-gates/reader-2-repl")), "reader-2")
            self.assertEqual(proof_repl.default_lane(pathlib.Path("/h/fn-gates/operator-walk-r1")), "operator-walk")
            self.assertIsNone(proof_repl.default_lane(pathlib.Path("/Users/e/dev/fn")))
            os.environ["FN_LANE"] = "given"
            self.assertEqual(proof_repl.default_lane(pathlib.Path("/x/build/lanes/tv")), "given")

    def test_list_reads_other_trees_with_root(self):
        with tempfile.TemporaryDirectory() as temporary:
            tree = pathlib.Path(temporary) / "lane-tree"
            directory = tree / "build" / "proof-repl" / "far"
            directory.mkdir(parents=True)
            (directory / "state.json").write_text(json.dumps(
                {"name": "far", "book": "books/y", "pid": 999999, "loaded": [],
                 "sends": 0, "lane": "far-lane", "idle_seconds": 60}))
            rows = proof_repl.session_rows([str(tree)])
            self.assertEqual([row["name"] for row in rows], ["far"])
            listing = subprocess.run(
                [sys.executable, str(ROOT / "tools" / "proof_repl.py"), "list", "--root", str(tree)],
                capture_output=True, text=True, cwd=ROOT, timeout=30)
            self.assertIn("far-lane", listing.stdout)
            self.assertIn(str(tree), listing.stdout)



class UntilIsExclusiveTests(unittest.TestCase):
    """obstructions-6 item 53: --until's exclusion is said, in the help and the run."""

    def test_the_head_line_says_until_excludes_its_event(self):
        words = proof_repl.range_words("s", "books/b", range(0, 3), [("a", "(x)")], [], 0,
                                       False, until="fn-target")
        self.assertIn("--until fn-target is EXCLUSIVE: fn-target itself is NOT sent "
                      "(--through fn-target sends it)", words)
        self.assertNotIn("EXCLUSIVE", proof_repl.range_words(
            "s", "books/b", range(0, 3), [], [], 0, False))

    def test_the_help_and_usage_say_it(self):
        self.assertIn("--until EXCLUDES its event", proof_repl.__doc__)
        parser_help = subprocess.run([sys.executable, str(ROOT / "tools" / "proof_repl.py"),
                                      "send-range", "--help"], capture_output=True,
                                     text=True).stdout
        self.assertIn("EXCLUSIVE", parser_help)
        self.assertIn("INCLUSIVE", parser_help)


class LeaveLoopTests(unittest.TestCase):
    """obstructions-6 item 49: forms that leave the ACL2 loop are refused by name."""

    def test_leaving_forms_are_named(self):
        for form in (":q", "(value :q)", "(er-progn (value-triple 1) (value :q))",
                     "(mv nil :q state)", "(good-bye)", "(exit 0)", "(quit)",
                     "(sb-ext:exit)", "(set-raw-mode t)", "(set-raw-mode-on! state)"):
            self.assertIsNotNone(proof_repl.leaves_loop(form), form)
        for form in ("(value-triple :q)", "(progn! (set-raw-mode t) (load \"x\"))",
                     "(defthm q-lemma (equal (car (cons :q b)) :q))", ":pe car",
                     "(set-raw-mode nil)", "(value :quiet)"):
            self.assertIsNone(proof_repl.leaves_loop(form), form)

    def test_send_refuses_before_anything_is_sent(self):
        asked = []
        with mock.patch.object(proof_repl, "ask", lambda *a, **k: asked.append(a) or {}), \
                contextlib.redirect_stderr(io.StringIO()) as said:
            code = proof_repl.send(argparse.Namespace(name="s", form="(+ 1 2) (value :q)",
                                                      limit=None, full=False))
        self.assertEqual(code, 2)
        self.assertEqual(asked, [])
        self.assertIn("exits LP into raw Lisp", said.getvalue())
        self.assertIn("proof_repl.py stop s", said.getvalue())


class ObstructionsTwoTests(unittest.TestCase):
    """obstructions-2 item 5: suffix, argument order, values, undo, fallback."""

    def test_undo_commands_are_refused_without_allow_undo(self):
        for form in ("(u)", ":u", "(ubt 'x)", ":ubt! foo", "(ubu! 3)"):
            self.assertTrue(proof_repl.undoes(form), form)
        for form in ("(disabledp 'zp)", "(defthm u t)", ":pe car"):
            self.assertFalse(proof_repl.undoes(form), form)
        asked = []
        with mock.patch.object(proof_repl, "ask", lambda *a, **k: asked.append(a) or {}), \
                contextlib.redirect_stderr(io.StringIO()) as said:
            code = proof_repl.send(argparse.Namespace(name="s", form="(+ 1 2) (u)",
                                                      limit=None, full=False,
                                                      allow_undo=False))
        self.assertEqual((code, asked), (2, []))
        self.assertIn("--allow-undo", said.getvalue())

    def test_several_forms_keep_a_diagnostic_value(self):
        answers = iter([{"output": "ACL2 !>\nT\nACL2 !>"},
                        {"output": "Summary\nForm: ( DEFTHM X ...)\n"}])
        out = io.StringIO()
        with mock.patch.object(proof_repl, "ask", lambda *a, **k: next(answers)), \
                mock.patch.object(proof_repl, "save_output", lambda *a, **k: "log"), \
                contextlib.redirect_stdout(out):
            proof_repl.send_many("s", [("#1 disabledp", "(disabledp 'zp)"),
                                       ("#2 defthm x", "(defthm x t)")], None)
        lines = out.getvalue().splitlines()
        self.assertIn("        T", lines)
        self.assertNotIn("        Summary", lines)

    def test_a_book_named_with_its_suffix_is_normalised_and_no_sync_may_lead(self):
        seen = []
        with mock.patch.object(proof_repl, "run_remote",
                               lambda args, argv: seen.append((args.book, argv)) or 0), \
                mock.patch.object(proof_repl, "remember_host", lambda *a: None), \
                contextlib.redirect_stderr(io.StringIO()):
            proof_repl.main(["--host", "persvati", "start", "n", "books/x.lisp"])
        self.assertEqual(seen[0][0], "books/x")
        self.assertIn("books/x", seen[0][1])
        self.assertNotIn("books/x.lisp", seen[0][1])
        sent = []
        with mock.patch.object(proof_repl, "run_remote",
                               lambda args, argv: sent.append(argv) or 0), \
                contextlib.redirect_stderr(io.StringIO()):
            proof_repl.main(["--no-sync", "--host", "hbox", "send", "n", "(+ 1 2)"])
            proof_repl.main(["send", "n", "(+ 1 2)", "--host", "hbox", "--no-sync"])
        self.assertEqual(len(sent), 2)

    def test_checkpoints_are_the_last_refused_forms(self):
        log = "\n".join([
            ">>> (defthm a t)", "Summary", ">>> (defthm b (foo x))",
            "*** Key checkpoint at the top level: ***", "Goal'", "(FOO X)", "",
            "*** Key checkpoint under a top-level induction: ***", "Subgoal *1/2",
            "(BAR X)", "Summary", "******** FAILED ********",
            ">>> (disabledp 'zp)", "T"])
        form, found = proof_repl.last_checkpoints(log)
        self.assertEqual(form, "(defthm b (foo x))")
        self.assertEqual(len(found), 2)
        self.assertEqual(found[0], ["*** Key checkpoint at the top level: ***", "Goal'",
                                    "(FOO X)"])
        self.assertEqual(proof_repl.last_checkpoints(">>> (defthm a t)\nSummary"),
                         (None, []))
        self.assertIn("checkpoints", proof_repl.SESSION_COMMANDS)

    def test_an_empty_range_is_refused_and_says_until_is_exclusive(self):
        forms = ["(defun a () 1)", "(defthm b t)", "(defthm c t)"]
        with self.assertRaises(SystemExit) as refused:
            proof_repl.select_range(forms, "b", "b")
        self.assertIn("--through includes it", str(refused.exception))
        self.assertEqual(proof_repl.select_range(forms, "b", None, "b"), range(1, 2))
        self.assertEqual(proof_repl.select_range(forms, "a", "c"), range(0, 2))

    def test_a_failed_source_dependency_retries_only_with_explicit_certification(self):
        calls = []

        def fake_start(args):
            calls.append((args.certify_missing, args.source_deps))
            return proof_repl.SOURCE_DEPS_FAILED if len(calls) == 1 else 0
        args = argparse.Namespace(name="s", certify_missing=True, source_deps="*",
                                  ld_missing=False, ld=[])
        with mock.patch.object(proof_repl, "_start", fake_start), \
                mock.patch.object(proof_repl, "stop", lambda args: 0), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(proof_repl.start(args), 0)
        self.assertEqual(calls, [(True, "*"), (True, None)])
        self.assertIn("retrying with --certify-missing", out.getvalue())

    def test_source_refusal_does_not_launch_certification_or_change_requested_loading(self):
        for source_deps, ld_missing, ld in (("*", False, []),
                                          ("books/near", False, []),
                                          (None, True, []),
                                          (None, False, ["books/near"])):
            with self.subTest(source_deps=source_deps, ld_missing=ld_missing, ld=ld):
                args = argparse.Namespace(name="s", certify_missing=False,
                                          source_deps=source_deps, ld_missing=ld_missing,
                                          ld=list(ld))
                before = vars(args).copy()
                with mock.patch.object(proof_repl, "_start",
                                       return_value=proof_repl.SOURCE_DEPS_FAILED) as start, \
                        mock.patch.object(proof_repl, "stop", return_value=0) as stop, \
                        contextlib.redirect_stdout(io.StringIO()) as out:
                    self.assertEqual(proof_repl.start(args), proof_repl.SOURCE_DEPS_FAILED)
                start.assert_called_once_with(args)
                stop.assert_called_once_with(args)
                self.assertEqual(vars(args), before)
                self.assertIn("no certification launched", out.getvalue())


class SessionIncludeTests(unittest.TestCase):
    """obstructions-3 item 23: a tests/acl2 book included from a books/ session."""

    def tree(self, directory: str) -> pathlib.Path:
        root = pathlib.Path(directory).resolve()
        (root / "books").mkdir()
        (root / "tests" / "acl2").mkdir(parents=True)
        (root / "books" / "model.lisp").write_text('(in-package "ACL2")\n')
        (root / "books" / "near.lisp").write_text('(in-package "ACL2")\n')
        (root / "tests" / "acl2" / "fixture-tests.lisp").write_text(
            '(in-package "ACL2")\n(include-book "../../books/model")\n')
        return root

    def test_a_root_relative_include_is_made_relative_to_the_session(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            with mock.patch.object(proof_repl, "ROOT", root):
                books = root / "books"
                form, target = proof_repl.rooted_include(
                    '(include-book "tests/acl2/fixture-tests")', books)
                self.assertEqual(form, '(include-book "../tests/acl2/fixture-tests")')
                self.assertEqual(target, "tests/acl2/fixture-tests")
                # Already relative to the session, a local include, a system book.
                for sent, named in (('(include-book "near")', "books/near"),
                                    ('(local (include-book "near"))', "books/near"),
                                    ('(include-book "std/lists/rev" :dir :system)', None)):
                    self.assertEqual(proof_repl.rooted_include(sent, books), (sent, named))

    def test_send_rewrites_and_acquires_an_uncertified_included_book(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            acquired, sent = [], []
            with mock.patch.object(proof_repl, "ROOT", root), \
                    mock.patch.object(proof_repl, "read_state",
                                      lambda name: {"book": "books/model"}), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                forms, ready = proof_repl.prepare_includes(
                    "s", ['(include-book "tests/acl2/fixture-tests")', "(+ 1 2)"],
                    acquire=lambda book: acquired.append(book) or (True, "installed", []))
                self.assertTrue(ready)
                self.assertEqual(forms, ['(include-book "../tests/acl2/fixture-tests")',
                                         "(+ 1 2)"])
                self.assertEqual(acquired, ["tests/acl2/fixture-tests"])
                self.assertIn("made relative to the session's directory books/",
                              out.getvalue())
                # A certified include is sent as it is, nothing acquired.
                (root / "tests/acl2/fixture-tests.cert").write_text(
                    '(IN-PACKAGE "ACL2")\n:BEGIN-PORTCULLIS-CMDS\n')
                acquired.clear()
                with mock.patch.object(proof_repl.certs, "valid_looking", lambda p: True):
                    proof_repl.prepare_includes(
                        "s", ['(include-book "../tests/acl2/fixture-tests")'],
                        acquire=lambda book: acquired.append(book))
                self.assertEqual(acquired, [])
                # One that cannot be acquired is not sent: send answers 1.
                with mock.patch.object(proof_repl, "install_closure",
                                       lambda *a, **k: (False, "no certificate", [])), \
                        mock.patch.object(proof_repl, "ask",
                                          lambda *a, **k: sent.append(a) or {}):
                    code = proof_repl.send(argparse.Namespace(
                        name="s", form='(include-book "tests/acl2/fixture-tests")',
                        limit=None, full=False, allow_undo=False))
                self.assertEqual((code, sent), (1, []))

    def test_sent_include_cache_miss_does_not_certify_or_send_any_form(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.tree(directory)
            with mock.patch.object(proof_repl, "ROOT", root), \
                    mock.patch.object(proof_repl, "read_state",
                                      return_value={"book": "books/model"}), \
                    mock.patch.object(proof_repl.certs, "valid_looking", return_value=False), \
                    mock.patch.object(proof_repl, "install_closure",
                                      return_value=(False, "cache miss", [])) as acquire, \
                    mock.patch.object(proof_repl, "ask") as ask, \
                    contextlib.redirect_stdout(io.StringIO()):
                code = proof_repl.send(argparse.Namespace(
                    name="s", form='(include-book "tests/acl2/fixture-tests")',
                    limit=None, full=False, allow_undo=False))
            self.assertEqual(code, 1)
            self.assertEqual(acquire.call_args.args[:3],
                             ("tests/acl2/fixture-tests", (), None))
            self.assertTrue(acquire.call_args.kwargs["include_self"])
            ask.assert_not_called()


class PartialLoadTests(unittest.TestCase):
    """obstructions-3 item 25: a start that stopped at a refused form says where."""

    def state(self, **fields) -> dict:
        state = {"name": "s", "book": "books/model", "loaded": ["a", "b"],
                 "stopped_at": None, "ready": True, "upto": None, "through": None}
        state.update(fields)
        return state

    def test_a_load_that_stops_early_names_the_form_and_book_and_is_partial(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            (root / "books").mkdir()
            (root / "books/model.lisp").write_text(
                '(in-package "ACL2")\n(defun a (x) x)\n(defun b (x) x)\n'
                '(defthm c (equal (a x) (b x)))\n(defthm d t)\n')
            with mock.patch.object(proof_repl, "ROOT", root):
                line, partial = proof_repl.load_verdict(self.state(stopped_at="c"))
                self.assertTrue(partial)
                self.assertIn("PARTIAL LOAD -- stopped at c in books/model after 2 of 5 "
                              "forms; the session is live just before it", line)
                line, partial = proof_repl.load_verdict(
                    self.state(stopped_at="books/dep: lemma-7", ready=False))
                self.assertTrue(partial)
                self.assertIn("stopped at lemma-7 in books/dep (a from-source dependency)",
                              line)
                self.assertIn("not live", line)
                line, partial = proof_repl.load_verdict(self.state())
                self.assertEqual((line, partial), ("proof-repl s: LOADED books/model: 2 forms",
                                                   False))
                line, partial = proof_repl.load_verdict(self.state(through="b"))
                self.assertFalse(partial)
                self.assertIn("as asked, through b", line)

    def test_start_exits_non_zero_on_a_partial_load_with_the_verdict_last(self):
        state = self.state(stopped_at="c")
        with tempfile.TemporaryDirectory() as directory:
            sessions = pathlib.Path(directory)
            (sessions / "s").mkdir()

            def serve(*args, **kwargs):
                # What the server writes once its load stopped at `c`.
                (sessions / "s" / "state.json").write_text(json.dumps(state))
                (sessions / "s" / "sock").write_text("")
            args = argparse.Namespace(
                name="s", book="books/model", upto=None, through=None, limit=60.0,
                load_timeout=5.0, lane=None, idle_seconds=60, ld=[], ld_missing=False,
                certify_missing=False, certify_jobs=4, load_limit=None, ld_local=False,
                source_deps=None)
            with mock.patch.object(proof_repl, "SESSIONS", sessions), \
                    mock.patch.object(proof_repl, "session_dir", lambda n: sessions / n), \
                    mock.patch.object(proof_repl, "open_session_lock", lambda *a: os.open(
                        os.devnull, os.O_RDONLY)), \
                    mock.patch.object(proof_repl, "install_closure",
                                      lambda *a, **k: (True, "no dependencies", [])), \
                    mock.patch.object(proof_repl.subprocess, "Popen", serve), \
                    mock.patch.object(proof_repl, "status", lambda args: 0), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                code = proof_repl._start(args)
            self.assertEqual(code, proof_repl.PARTIAL_LOAD)
            self.assertIn("PARTIAL LOAD -- stopped at c", out.getvalue().splitlines()[-1])


class SessionRecordLaneTests(unittest.TestCase):
    """obstructions-5 item 31: a --host subcommand finds its lane and tree in
    the record `start` wrote, with no FN_LANE in the environment."""

    def setUp(self):
        self.sessions = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.sessions, ignore_errors=True)
        patcher = mock.patch.object(proof_repl, "SESSIONS", self.sessions)
        patcher.start()
        self.addCleanup(patcher.stop)
        env = mock.patch.dict(os.environ, {}, clear=False)
        env.start()
        self.addCleanup(env.stop)
        os.environ.pop("FN_LANE", None)
        # From the main checkout: the tree's path names no lane.
        lane = mock.patch.object(proof_repl, "ROOT", pathlib.Path("/main/fn"))
        lane.start()
        self.addCleanup(lane.stop)

    def args(self, command, **extra):
        return SimpleNamespace(command=command, name="s31", lane=None, remote_tree=None, **extra)

    def test_send_reads_the_lane_and_tree_start_recorded(self):
        proof_repl.remember_host("s31", "persvati", "fn-gates/mylane-repl", "books/x", "mylane")
        lane, tree = proof_repl.remote_lane_and_tree(self.args("send"), "persvati")
        self.assertEqual((lane, tree), ("mylane", "fn-gates/mylane-repl"))

    def test_without_a_record_it_still_refuses_to_guess(self):
        with self.assertRaises(SystemExit):
            proof_repl.remote_lane_and_tree(self.args("status"), "persvati")

    def test_a_record_for_another_box_is_not_used(self):
        proof_repl.remember_host("s31", "hbox", "/tank/fn/gates/mylane-repl", "books/x", "mylane")
        with self.assertRaises(SystemExit):
            proof_repl.remote_lane_and_tree(self.args("stop"), "persvati")

    def test_explicit_lane_wins_over_the_record(self):
        proof_repl.remember_host("s31", "persvati", "fn-gates/mylane-repl", "books/x", "mylane")
        args = self.args("send")
        args.lane = "other"
        self.assertEqual(proof_repl.remote_lane_and_tree(args, "persvati"),
                         ("other", "fn-gates/other-repl"))

    def test_start_never_reads_an_old_record(self):
        proof_repl.remember_host("s31", "persvati", "fn-gates/old-repl", "books/x", "old")
        with self.assertRaises(SystemExit):
            proof_repl.remote_lane_and_tree(self.args("start"), "persvati")

    def test_run_remote_sends_status_to_the_recorded_tree(self):
        proof_repl.remember_host("s31", "persvati", "fn-gates/mylane-repl", "books/x", "mylane")
        seen = []
        with mock.patch.object(proof_repl, "box_settings",
                               lambda host: {"acl2": "acl2", "cache": "/c"}), \
                mock.patch.object(proof_repl.subprocess, "run",
                                  lambda command, **kw: seen.append(command)
                                  or SimpleNamespace(returncode=0)):
            proof_repl.run_remote(SimpleNamespace(command="status", name="s31", lane=None,
                                                  remote_tree=None, host="persvati"),
                                  ["status", "s31", "--host", "persvati"])
        script = seen[-1][-1]
        self.assertIn("cd fn-gates/mylane-repl ", script)
        self.assertIn("FN_LANE=mylane", script)


class LdHonoursLocalTests(unittest.TestCase):
    """obstructions-5 item 32: `start --ld` loads inside one encapsulate by
    default (store-log-extend's local lemmas turned global form by form)."""

    def parsed(self, *words):
        seen = []
        with mock.patch.object(proof_repl, "start", lambda args: seen.append(args) or 0):
            proof_repl.main(["start", "n", "books/x", *words])
        return seen[0]

    def test_ld_is_encapsulated_by_default(self):
        self.assertTrue(self.parsed("--ld", "books/store-log-extend").ld_local)

    def test_ld_local_is_still_accepted(self):
        self.assertTrue(self.parsed("--ld", "books/y", "--ld-local").ld_local)

    def test_ld_leak_loads_form_by_form(self):
        self.assertFalse(self.parsed("--ld", "books/y", "--ld-leak").ld_local)

    def test_an_encapsulated_refusal_names_ld_leak(self):
        class Refusing:
            def send(self, form, timeout):
                return ("ACL2 Error in ( ENCAPSULATE NIL ...): failed\n"
                        if form.startswith("(encapsulate") else ""), False
        scratch = ROOT / "build" / "proof-repl-ld32"
        scratch.mkdir(parents=True, exist_ok=True)
        self.addCleanup(shutil.rmtree, scratch, True)
        (scratch / "dep.lisp").write_text('(in-package "ACL2")\n(local (defthm l (equal x x)))\n')
        state = {"ld_loaded": {}}
        ok = proof_repl.load_book(Refusing(), "build/proof-repl-ld32/dep", state, 10, set(),
                                  record=False, encapsulate=True)
        self.assertFalse(ok)
        self.assertIn("--ld-leak", state["stopped_at"])


class FailedDependencyTests(unittest.TestCase):
    """obstructions-7 item 57: a from-source dependency that fails to load is
    named with its first error line, and the session is not reported live."""

    def test_the_verdict_names_the_dependency_and_its_error(self):
        state = {"name": "s", "book": "books/b", "loaded": [], "ready": True,
                 "stopped_at": "books/dep: fn-lemma-7",
                 "error": "\nACL2 Error in ( DEFTHM FN-LEMMA-7 ...): the proof failed\nmore",
                 "failed_dependency": "books/dep",
                 "dependency_error": "ACL2 Error in ( DEFTHM FN-LEMMA-7 ...): the proof failed"}
        line, partial = proof_repl.load_verdict(state)
        self.assertTrue(partial)
        self.assertIn("NOT LIVE -- the dependency books/dep failed", line)
        self.assertIn("ACL2 Error in ( DEFTHM FN-LEMMA-7", line)
        self.assertNotIn("is live", line)
        self.assertIn(f"exit {proof_repl.SOURCE_DEPS_FAILED}", line)

    def test_serve_records_the_first_error_line_and_start_exits_with_it(self):
        import inspect
        serve = inspect.getsource(proof_repl.serve)
        self.assertIn('state["failed_dependency"] = one', serve)
        self.assertIn('state["dependency_error"]', serve)
        start = inspect.getsource(proof_repl)
        self.assertIn('if final.get("failed_dependency"):', start)


class FreeExpandTests(unittest.TestCase):
    """obstructions-8 item 65: `:expand (:free ...)' over a recursion's controller warns."""

    BOOK = """
(defun countdown (x n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) x (countdown (cons n x) (1- n))))
(defun walk (x acc)
  (if (atom x) acc (walk (cdr x) (cons (car x) acc))))
(defun plain (x n) (+ x n))
"""

    def test_freeing_the_measured_argument_warns(self):
        form = ("(defthm c1 (equal (countdown x n) (countdown x n)) :hints "
                "((\"Goal\" :expand ((:free (n) (countdown x n))))))")
        lines = proof_repl.free_expand_warnings(form, [self.BOOK])
        self.assertEqual(len(lines), 1, lines)
        self.assertIn("countdown's controlling argument n", lines[0])

    def test_freeing_an_argument_the_recursive_call_changes_warns(self):
        form = "(thm (equal (walk x a) (walk x a)) :hints ((\"Goal\" :expand (:free (x) (walk x a)))))"
        lines = proof_repl.free_expand_warnings(form, [self.BOOK])
        self.assertEqual(len(lines), 1, lines)
        self.assertIn("walk's controlling argument x", lines[0])

    def test_freeing_only_a_non_controller_is_quiet(self):
        form = "(thm t :hints ((\"Goal\" :expand ((:free (x) (countdown x n)) (walk y a)))))"
        self.assertEqual(proof_repl.free_expand_warnings(form, [self.BOOK]), [])
        # walk's controller is x (it changes); acc changes too, so freeing acc warns:
        form = "(thm t :hints ((\"Goal\" :expand ((:free (a) (walk y a))))))"
        self.assertEqual(len(proof_repl.free_expand_warnings(form, [self.BOOK])), 1)

    def test_a_non_recursive_function_is_quiet(self):
        form = "(thm t :hints ((\"Goal\" :expand ((:free (n) (plain x n))))))"
        self.assertEqual(proof_repl.free_expand_warnings(form, [self.BOOK]), [])
        self.assertEqual(proof_repl.controller_positions(
            ["defun", "plain", ["x", "n"], ["+", "x", "n"]]), [])

    def test_an_unknown_function_is_quiet(self):
        form = "(thm t :hints ((\"Goal\" :expand ((:free (n) (no-such-fn-o8 x n))))))"
        self.assertEqual(proof_repl.free_expand_warnings(form, []), [])

    def test_send_prints_the_warning_and_still_sends(self):
        form = "(thm t :hints ((\"Goal\" :expand ((:free (n) (countdown x n))))))"
        args = SimpleNamespace(name="s", form=form, limit=None, full=False)
        err = io.StringIO()
        with mock.patch.object(proof_repl, "prepare_includes", return_value=([form], True)), \
                mock.patch.object(proof_repl, "read_state", return_value={}), \
                mock.patch.object(proof_repl, "find_definition",
                                  return_value=proof_repl._theory_check().forms(self.BOOK)[0]), \
                mock.patch.object(proof_repl, "send_one", return_value=0) as sent, \
                contextlib.redirect_stderr(err):
            self.assertEqual(proof_repl.send(args), 0)
        sent.assert_called_once()
        self.assertIn("proof-repl: warning: :expand (:free (n) (countdown x n))", err.getvalue())


class GuardNotesTests(unittest.TestCase):
    """obstructions-8 (item 56's proof_repl note): send-range names each
    verification's same-book callees and the form each is verified at."""

    BOOK = """(in-package "ACL2")
(defun g (x) (declare (xargs :guard t :verify-guards nil)) x)
(defun f (x) (declare (xargs :guard t)) (g x))
(verify-guards g)
(defun h (x) (declare (xargs :guard t)) (g x))
"""

    def test_a_later_callee_is_flagged_and_an_earlier_one_named(self):
        notes = proof_repl.guard_notes(self.BOOK, range(0, 5))
        self.assertEqual(len(notes), 2, notes)
        self.assertIn("form #3 verifies f's guards", notes[0])
        self.assertIn("LATER: g #4", notes[0])
        self.assertIn("form #5 verifies h's guards", notes[1])
        self.assertIn("verified at g #4", notes[1])
        self.assertNotIn("LATER", notes[1])

    def test_numbers_match_the_forms_send_range_counts(self):
        forms = proof_repl.forms(self.BOOK)
        self.assertTrue(forms[2].lstrip().startswith("(defun f"))
        self.assertTrue(forms[3].lstrip().startswith("(verify-guards g"))

    def test_only_the_chosen_forms_are_noted(self):
        notes = proof_repl.guard_notes(self.BOOK, range(4, 5))
        self.assertEqual(len(notes), 1)
        self.assertIn("form #5", notes[0])


class SentEventsTests(unittest.TestCase):
    """obstructions-8 item 72: what `send` adds by hand is recorded for the probe."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = pathlib.Path(self.tmp.name)
        self.state = {"started_at": 100.0}
        patches = [mock.patch.object(proof_repl, "session_dir", return_value=self.dir),
                   mock.patch.object(proof_repl, "read_state", side_effect=lambda n: self.state)]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def test_events_are_recorded_and_other_forms_are_not(self):
        proof_repl.record_sent("s", ["(defthm l1 (equal x x))", "(pe 'l1)",
                                     "(defun f (x) x)"])
        self.assertEqual(proof_repl.sent_events("s"),
                         ["(defthm l1 (equal x x))", "(defun f (x) x)"])

    def test_a_restarted_session_starts_empty(self):
        proof_repl.record_sent("s", ["(defthm l1 (equal x x))"])
        self.state = {"started_at": 200.0}
        self.assertEqual(proof_repl.sent_events("s"), [])

    def test_send_records_only_an_accepted_send(self):
        args = SimpleNamespace(name="s", form="(defthm l2 (equal y y))", limit=None, full=False)
        for code, expected in ((1, []), (0, ["(defthm l2 (equal y y))"])):
            with mock.patch.object(proof_repl, "prepare_includes",
                                   return_value=([args.form], True)), \
                    mock.patch.object(proof_repl, "send_one", return_value=code):
                proof_repl.send(args)
            self.assertEqual(proof_repl.sent_events("s"), expected)


class HostLoadTests(unittest.TestCase):
    """obstructions-9 item 84: one host load per session (a session with
    several behind it died in a fasl load); a --host send of one syncs it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = pathlib.Path(self.tmp.name)
        self.state = {"started_at": 100.0}
        patches = [mock.patch.object(proof_repl, "session_dir", return_value=self.dir),
                   mock.patch.object(proof_repl, "read_state", side_effect=lambda n: self.state)]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def send(self, form):
        args = SimpleNamespace(name="s", form=form, limit=None, full=False)
        err = io.StringIO()
        with mock.patch.object(proof_repl, "prepare_includes", side_effect=lambda n, f: (f, True)), \
                mock.patch.object(proof_repl, "send_one", return_value=0), \
                mock.patch.object(proof_repl, "send_many", return_value=0), \
                contextlib.redirect_stderr(err):
            return proof_repl.send(args), err.getvalue()

    def test_the_target_is_a_repository_host_file_only(self):
        self.assertEqual(proof_repl.host_load_target('(ld "host/owner-host.lisp")', None),
                         "host/owner-host.lisp")
        self.assertEqual(proof_repl.host_load_target('(load "host/native/mux.lisp")', None),
                         "host/native/mux.lisp")
        self.assertIsNone(proof_repl.host_load_target('(ld "books/base.lisp")', None))
        self.assertIsNone(proof_repl.host_load_target('(ld "host/no-such.lisp")', None))
        self.assertIsNone(proof_repl.host_load_target("(defun f (x) x)", None))

    def test_a_second_host_load_is_refused_by_name_and_a_restart_clears_it(self):
        code, _ = self.send('(ld "host/owner-host.lisp" :ld-error-action :error)')
        self.assertEqual(code, 0)
        self.assertEqual(proof_repl.session_host_loads("s"), ["host/owner-host.lisp"])
        self.assertEqual(self.send("(defthm t1 (equal x x))")[0], 0)  # not a host load
        code, err = self.send('(ld "host/store-host.lisp")')
        self.assertEqual(code, 2)
        self.assertIn("session 's' already loaded host file host/owner-host.lisp; a second "
                      "host load (host/store-host.lisp)", err)
        self.state = {"started_at": 200.0}
        self.assertEqual(self.send('(ld "host/store-host.lisp")')[0], 0)

    def test_two_host_loads_in_one_send_are_refused(self):
        code, err = self.send('(ld "host/owner-host.lisp") (ld "host/store-host.lisp")')
        self.assertEqual(code, 2)
        self.assertIn("a second host load (host/store-host.lisp)", err)
        self.assertEqual(proof_repl.session_host_loads("s"), [])

    def test_a_host_send_syncs_the_loaded_host_file_first(self):
        record = self.dir / "remote.json"
        record.write_text(json.dumps({"host": "hbox", "tree": "/t", "book": "books/base",
                                      "lane": "l"}))
        synced, seen = [], []
        with mock.patch.object(proof_repl, "box_settings",
                               lambda host: {"acl2": "acl2", "cache": "/c"}), \
                mock.patch.object(proof_repl, "sync_to",
                                  lambda host, tree, files: synced.extend(files) or 0.0), \
                mock.patch.object(proof_repl.subprocess, "run",
                                  lambda command, **kw: seen.append(command)
                                  or SimpleNamespace(returncode=0)), \
                contextlib.redirect_stdout(io.StringIO()):
            proof_repl.run_remote(SimpleNamespace(command="send", name="s", lane=None,
                                                  remote_tree=None, host="hbox",
                                                  form='(ld "host/owner-host.lisp")'),
                                  ["send", "s", '(ld "host/owner-host.lisp")', "--host", "hbox"])
        self.assertIn("host/owner-host.lisp", synced)


class SendFileTests(unittest.TestCase):
    """obstructions-8 item 75: send-file sends every form of a test file in
    order, its includes rewritten for the session's directory."""

    def run_send_file(self, text, keep_going=False, session_dir="books"):
        with tempfile.TemporaryDirectory(dir=proof_repl.ROOT / "tests" / "acl2") as directory:
            path = pathlib.Path(directory) / "o8-send-file-tests.lisp"
            path.write_text(text)
            args = SimpleNamespace(name="s", file=str(path), limit=None, full=False,
                                   keep_going=keep_going, allow_undo=False)
            sent = []

            def fake_many(name, items, limit, full, keep):
                sent.extend(items)
                return 0

            out = io.StringIO()
            with mock.patch.object(proof_repl, "session_directory",
                                   return_value=proof_repl.ROOT / session_dir), \
                    mock.patch.object(proof_repl.certs, "valid_looking", return_value=True), \
                    mock.patch.object(proof_repl, "send_many", side_effect=fake_many), \
                    mock.patch.object(proof_repl, "record_sent") as recorded, \
                    contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
                code = proof_repl.send_file(args)
            return code, sent, out.getvalue(), recorded

    def test_every_form_in_order_with_the_includes_made_the_sessions(self):
        text = ('(in-package "ACL2")\n(include-book "../../../books/wire")\n'
                '(defthm o8-a (equal x x))\n(assert-event t)\n')
        code, sent, out, recorded = self.run_send_file(text)
        self.assertEqual(code, 0, out)
        self.assertEqual([label.split()[0] for label, _ in sent], ["#1", "#2", "#3", "#4"])
        self.assertEqual(sent[1][1], '(include-book "wire")')  # books/ is the session's dir
        self.assertIn("4 form(s) of tests/acl2/", out)
        recorded.assert_called_once()

    def test_a_form_leaving_the_loop_refuses_the_whole_file(self):
        code, sent, _, _ = self.run_send_file("(defthm o8-b (equal x x))\n(value :q)\n")
        self.assertEqual(code, 2)
        self.assertEqual(sent, [])


class SameLaneTreeTests(unittest.TestCase):
    """obstructions-9 item 79: a second live session of the lane on one box
    takes its own tree instead of racing the first's sync and load."""

    def args(self, **extra):
        return SimpleNamespace(command="start", name="s2", remote_tree=None, **extra)

    def runner(self, stdout, code=0):
        seen = []

        def run(command, **kwargs):
            seen.append(command)
            return subprocess.CompletedProcess(command, code, stdout=stdout, stderr="")
        return run, seen

    def test_no_live_sibling_keeps_the_lane_tree(self):
        run, seen = self.runner("")
        self.assertEqual(proof_repl.own_remote_tree(self.args(), "hbox", "l",
                                                    "/tank/fn/gates/l-repl", run),
                         "/tank/fn/gates/l-repl")
        self.assertIn("/tank/fn/gates/l-repl s2", seen[0][-1])

    def test_a_live_sibling_suffixes_the_tree_and_says_why(self):
        run, _ = self.runner("s1\n")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            tree = proof_repl.own_remote_tree(self.args(), "hbox", "l", "/tank/fn/gates/l-repl",
                                              run)
        self.assertEqual(tree, "/tank/fn/gates/l-repl-s2")
        self.assertIn("session(s) s1 of lane l are live in /tank/fn/gates/l-repl; session "
                      "'s2' gets its own tree /tank/fn/gates/l-repl-s2", out.getvalue())

    def test_an_explicit_remote_tree_with_a_live_sibling_is_refused_by_name(self):
        run, _ = self.runner("s1\n")
        args = self.args()
        args.remote_tree = "/x/t"
        with self.assertRaises(SystemExit) as refused:
            proof_repl.own_remote_tree(args, "hbox", "l", "/x/t", run)
        self.assertIn("session(s) s1 are live in /x/t", str(refused.exception))

    def test_a_box_that_does_not_answer_keeps_the_tree(self):
        run, _ = self.runner("", code=255)
        self.assertEqual(proof_repl.own_remote_tree(self.args(), "hbox", "l", "/t", run), "/t")

    @unittest.skipUnless(os.path.isdir("/proc/self"), "the box-side script reads /proc")
    def test_the_box_script_names_a_live_holder_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            locks = pathlib.Path(temporary, "build", "proof-repl", ".locks")
            locks.mkdir(parents=True)
            holder = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)",
                                       "proof_repl.py", "serve", "s1"])
            try:
                (locks / "s1").write_text(json.dumps({"pid": holder.pid}))
                (locks / "gone").write_text(json.dumps({"pid": 999999999}))
                (locks / "s2").write_text(json.dumps({"pid": holder.pid}))
                done = subprocess.run([sys.executable, "-", temporary, "s2"],
                                      input=proof_repl.LIVE_SIBLINGS_SCRIPT, text=True,
                                      capture_output=True)
            finally:
                holder.kill()
                holder.wait()
        self.assertEqual(done.stdout.split(), ["s1"], done.stderr)


class ChangedDependencyTests(unittest.TestCase):
    """obstructions-9 item 82 (operability-7): a --host start on a book whose
    closure holds a book this branch changed loads it from source, and says
    so BEFORE the sync, instead of the box refusing after it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = worktree(self.tmp.name + "/tree")

        def g(*words):
            subprocess.run(["git", "-C", str(self.root), "-c", "commit.gpgsign=false",
                            "-c", "user.name=t", "-c", "user.email=t@t", *words],
                           check=True, capture_output=True)
        g("init", "-q", "-b", "lane")
        g("add", ".")
        g("commit", "-q", "-m", "base")
        g("update-ref", "refs/remotes/origin/dev", "HEAD")
        (self.root / "books" / "base.lisp").write_text(
            (self.root / "books" / "base.lisp").read_text() + "; changed on the lane\n")
        self.patch = mock.patch.object(proof_repl, "ROOT", self.root)
        self.patch.start()

    def tearDown(self):
        self.patch.stop()
        self.tmp.cleanup()

    def test_the_changed_dependency_is_named_and_a_named_one_is_not(self):
        self.assertEqual(proof_repl.changed_dependencies("tests/acl2/mid-tests"), ["books/base"])
        self.assertEqual(proof_repl.changed_dependencies("tests/acl2/mid-tests", ["base"]), [])
        # The session's own book is never a dependency of itself.
        self.assertEqual(proof_repl.changed_dependencies("books/base"), [])

    def test_a_host_start_forwards_it_as_ld_before_syncing(self):
        seen, events, real_run = [], [], subprocess.run
        args = SimpleNamespace(command="start", name="s82", lane="l", remote_tree=None,
                               host="hbox", book="tests/acl2/mid-tests", ld=[],
                               source_deps=None, ld_missing=False, certify_missing=False,
                               no_sync=False, acl2=None)
        out = io.StringIO()
        with mock.patch.object(proof_repl, "box_settings",
                               lambda host: {"acl2": "acl2", "cache": "/c"}), \
                mock.patch.object(proof_repl, "refuse_or_wait_for_lease", lambda *a: None), \
                mock.patch.object(proof_repl, "own_remote_tree", lambda a, h, l, t: t), \
                mock.patch.object(proof_repl, "remember_host", lambda *a: None), \
                mock.patch.object(proof_repl, "sync_to",
                                  lambda host, tree, files: events.append(("sync", files)) or 0.0), \
                mock.patch.object(proof_repl.subprocess, "run",
                                  lambda command, **kw: real_run(command, **kw)
                                  if command[0] == "git" else seen.append(command)
                                  or SimpleNamespace(returncode=0)), \
                contextlib.redirect_stdout(out):
            proof_repl.run_remote(args, ["start", "s82", "tests/acl2/mid-tests",
                                         "--host", "hbox"])
        self.assertIn("1 dependency of tests/acl2/mid-tests changed on this branch (no box has "
                      "their certificates): books/base; loading them from source", out.getvalue())
        self.assertIn("books/base.lisp", events[0][1])
        self.assertIn("--ld books/base", seen[-1][-1])

    def test_certify_missing_or_bare_source_deps_leave_it_to_the_box(self):
        for extra in ({"certify_missing": True}, {"source_deps": "*"}, {"ld_missing": True}):
            args = dict(source_deps=None, ld_missing=False, certify_missing=False)
            args.update(extra)
            seen = []
            with mock.patch.object(proof_repl, "box_settings",
                                   lambda host: {"acl2": "acl2", "cache": "/c"}), \
                    mock.patch.object(proof_repl, "refuse_or_wait_for_lease", lambda *a: None), \
                    mock.patch.object(proof_repl, "own_remote_tree", lambda a, h, l, t: t), \
                    mock.patch.object(proof_repl, "remember_host", lambda *a: None), \
                    mock.patch.object(proof_repl, "sync_to", lambda *a: 0.0), \
                    mock.patch.object(proof_repl.subprocess, "run",
                                      lambda command, **kw: seen.append(command)
                                      or SimpleNamespace(returncode=0)), \
                    contextlib.redirect_stdout(io.StringIO()):
                proof_repl.run_remote(SimpleNamespace(
                    command="start", name="s82", lane="l", remote_tree=None, host="hbox",
                    book="tests/acl2/mid-tests", ld=[], no_sync=False, acl2=None, **args),
                    ["start", "s82", "tests/acl2/mid-tests", "--host", "hbox"])
            self.assertNotIn("--ld books/base", seen[-1][-1], extra)


if __name__ == "__main__":
    unittest.main()
