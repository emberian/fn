"""The `tools/proof_profile.py` parser, against real ACL2 8.7 logs.

Both fixtures in `tests/vectors/` were produced by the driver the tool writes
(`(accumulated-persistence t)`, the form, three `show-accumulated-persistence`
listings behind `FN-PROFILE-SECTION` markers) running under
`$HOME/fn-tools/acl2-8.7/saved_acl2` on persvati, one for a form that closed
and one for a form that did not.  A parser tested against a log someone typed
would only prove that the parser reads what its author imagined ACL2 prints.
"""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import proof_profile  # noqa: E402

VECTORS = ROOT / "tests" / "vectors"
CLOSED = (VECTORS / "proof-profile-closed.log").read_text(encoding="utf-8")
CHECKPOINT = (VECTORS / "proof-profile-checkpoint.log").read_text(encoding="utf-8")


class ParseSections(unittest.TestCase):
    def test_three_marked_listings(self):
        sections = proof_profile.parse_sections(CLOSED)
        self.assertEqual(sorted(sections), ["frames-a", "tries-a", "useless"])
        self.assertTrue(sections["frames-a"])

    def test_frames_are_sorted_and_numeric(self):
        frames = proof_profile.parse_sections(CLOSED)["frames-a"]
        counts = [entry.frames for entry in frames]
        self.assertEqual(counts, sorted(counts, reverse=True))
        self.assertTrue(all(count > 0 for count in counts))

    def test_rune_is_class_and_name(self):
        runes = {entry.rune for entry in
                 proof_profile.parse_sections(CLOSED)["frames-a"]}
        self.assertIn("(:DEFINITION MYREV)", runes)
        self.assertTrue(all(rune.startswith("(:") and rune.endswith(")")
                            for rune in runes))

    def test_dashed_separators_and_nil_are_not_entries(self):
        self.assertNotIn("-", {entry.rune[:1] for entry in
                               proof_profile.parse_sections(CLOSED)["frames-a"]})

    def test_useless_is_a_subset_of_frames(self):
        sections = proof_profile.parse_sections(CLOSED)
        useless = proof_profile.useless_runes(sections)
        self.assertTrue(useless)
        self.assertTrue(useless <= {entry.rune for entry in sections["frames-a"]})

    def test_unmarked_log_falls_back_to_driver_order(self):
        # The same log with the markers stripped: the listings still land in
        # the order the driver issues them.
        stripped = "\n".join(line for line in CLOSED.splitlines()
                             if not line.startswith("FN-PROFILE-SECTION"))
        sections = proof_profile.parse_sections(stripped)
        self.assertEqual(sorted(sections), ["frames-a", "tries-a", "useless"])
        self.assertEqual([entry.rune for entry in sections["frames-a"]],
                         [entry.rune for entry in
                          proof_profile.parse_sections(CLOSED)["frames-a"]])


class SummaryAndCheckpoint(unittest.TestCase):
    def test_summary_is_the_profiled_form(self):
        facts = proof_profile.summary(CHECKPOINT)
        self.assertIn("prove:", facts["time"])
        self.assertEqual(facts["steps"], "12512")

    def test_closed_form_has_no_checkpoint(self):
        self.assertIsNone(proof_profile.checkpoint(CLOSED))

    def test_failed_form_reports_its_checkpoint(self):
        stop = proof_profile.checkpoint(CHECKPOINT)
        self.assertIsNotNone(stop)
        self.assertIn("Key checkpoint", stop)

    def test_checkpoint_is_not_taken_from_the_listings(self):
        # A rune named in a listing must never be mistaken for a checkpoint.
        self.assertNotIn("FN-PROFILE-SECTION", proof_profile.checkpoint(CHECKPOINT))


class Report(unittest.TestCase):
    def test_report_names_the_fan(self):
        text = proof_profile.report(CLOSED)
        self.assertIn("top 10 by frames with no useful application", text)
        self.assertIn("useless", text)
        self.assertIn("SUMMARY", text)

    def test_report_says_time_is_not_per_rune(self):
        self.assertIn("never time", proof_profile.report(CLOSED))

    def test_report_prints_the_checkpoint_when_there_is_one(self):
        self.assertIn("CHECKPOINT\n", proof_profile.report(CHECKPOINT))

    def test_report_says_so_when_there_is_none(self):
        self.assertIn("CHECKPOINT  none printed", proof_profile.report(CLOSED))

    def test_a_step_limit_cut_is_not_reported_as_a_closed_form(self):
        # Measured on 2026-09-20 (w10/dtn-3): a form needing about 10M prover
        # steps ran under the 4M default, ACL2 aborted it with the step-limit
        # error and printed NO key checkpoint, and the report read "the form
        # closed, or it was cut".  A cut is not a result and must say so.
        cut = CLOSED.replace(
            "Summary",
            "ACL2 Error [Step-limit] in ( DEFTHM FOO ...):  The prover has\n"
            "been instructed to abort.\n\nSummary", 1)
        text = proof_profile.report(cut)
        self.assertIn("CUT BY THE STEP LIMIT", text)
        self.assertNotIn("the form closed", text)
        self.assertIn("--steps", text)

    def test_top_is_respected(self):
        text = proof_profile.report(CLOSED, top=2)
        head = text.split("top 2 by frames, all")[1].split("top 2 by tries")[0]
        self.assertEqual(len([line for line in head.splitlines() if line.strip()]), 2)


class Driver(unittest.TestCase):
    SOURCE = ('(in-package "ACL2")\n'
              '(include-book "acceptance-alloc")\n\n'
              '(defun f (x) (declare (xargs :guard t)) x)\n\n'
              '(defthm f-is-identity (equal (f x) x))\n\n'
              '(defthm later (equal (f (f x)) x))\n')

    def test_split_puts_the_form_last_in_the_prefix(self):
        prefix, form = proof_profile.split_at_form(self.SOURCE, "f-is-identity")
        self.assertIn("(defun f (x)", prefix)
        self.assertNotIn("f-is-identity", prefix)
        self.assertIn("(defthm f-is-identity", form)
        self.assertNotIn("later", form)

    def test_split_does_not_match_a_name_inside_another_form(self):
        with self.assertRaises(proof_profile.ProfileError):
            proof_profile.split_at_form(self.SOURCE, "acceptance-alloc")

    def test_driver_profiles_the_form_and_asks_for_three_listings(self):
        prefix, form = proof_profile.split_at_form(self.SOURCE, "later")
        text = proof_profile.driver(prefix, form, 123456)
        self.assertLess(text.index("(accumulated-persistence t)"),
                        text.index("(defthm later"))
        self.assertIn("(set-prover-step-limit 123456)", text)
        for key in ("frames-a", "useless", "tries-a"):
            self.assertIn(f"FN-PROFILE-SECTION {key}", text)
            self.assertIn(f"(show-accumulated-persistence :{key})", text)
        self.assertTrue(text.rstrip().endswith("(quit)"))


class HostChoice(unittest.TestCase):
    def test_hbox_runs_under_swarm_build(self):
        command = proof_profile.remote_command("hbox", "/tank/fn/lanes/w9", "d.lsp", 900)
        self.assertIn("swarm-build", command)
        self.assertIn("cd /tank/fn/lanes/w9", command)
        self.assertIn("ACL2_BOOK_HASH_ALISTP=NIL", command)
        self.assertIn("timeout 900", command)

    def test_persvati_runs_bare(self):
        command = proof_profile.remote_command("persvati", "/home/ember/fn-lanes/w9",
                                               "d.lsp", 60)
        self.assertNotIn("swarm-build", command)
        self.assertIn("fn-tools/acl2-8.7/saved_acl2", command)

    def test_default_host_is_the_quieter_box(self):
        loads = {"persvati": "14:02:31 up, load average: 11.15, 10.25, 7.72",
                 "hbox": "14:02:31 up, load average: 0.31, 1.53, 0.90"}

        class Answer:
            def __init__(self, text):
                self.stdout, self.returncode = text, 0

        original = proof_profile.RUN
        proof_profile.RUN = lambda command, **kw: Answer(loads[command[2]])
        try:
            self.assertEqual(proof_profile.quieter_host(), "hbox")
            loads["hbox"], loads["persvati"] = loads["persvati"], loads["hbox"]
            self.assertEqual(proof_profile.quieter_host(), "persvati")
        finally:
            proof_profile.RUN = original


if __name__ == "__main__":
    unittest.main()
