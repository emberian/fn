"""The NNTP probe's per-cut expectation, derived from the model coordinate.

Campaign 6c0626c5 finding H1: the probe judged five rows against a hand list
of pre-publication cuts that predated lane p10-k0's four new cuts.  These
tests pin the derivation rule of `post_arm` over all 23 post cuts (the five
marker cuts of lane p10-marker-model included), show each arm separates rows
the others accept, and re-judge the recorded 6c0626c5 and 47bdb9a4 runs.
Those runs predate D25 (a present repost is "already stored here"); the
judge keeps no pre-D25 rule, so `RecordedRunTests` states which rows the
wording change affects and judges the rest under today's rule.
"""
import gzip
import json
import unittest
from dataclasses import replace
from pathlib import Path
from unittest import mock

from tests.campaign import native_cuts
from tests.campaign import native_nntp_post_probe as probe

ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = ROOT / "planning/evidence"
# Recorded pre-D25 runs, and how many of their 40 rows fail today's judge.
RECORDED_RUNS = {
    "campaign-6c0626c5/nntp-probe.json.gz": 8,
    "probe-tables/nntp-probe.json.gz": 7,
    "campaign-47bdb9a4/nntp-probe.json.gz": 9,
    "campaign-47bdb9a4/nntp-probe-repeat.json.gz": 5,
}

EXPECTED_ARMS = {
    "frontier-created": "refused", "frontier-written": "refused",
    "frontier-staged-durable": "refused", "frontier-replaced": "uncertain",
    "frontier-attempted": "uncertain", "frontier-durable": "uncertain",
    "frontier-reserved": "uncertain",
    "record-created": "refused", "record-written": "refused",
    "record-staged-durable": "refused", "record-linked": "uncertain",
    "record-attempted": "uncertain", "record-durable": "uncertain",
    "record-completing": "uncertain", "record-stage-unlinked": "swallowed",
    "record-staging-cleaned": "uncertain",
    "marker-created": "uncertain", "marker-written": "uncertain",
    "marker-staged-durable": "uncertain", "marker-replaced": "uncertain",
    "marker-durable": "uncertain",
    "finish-consumed": "consumed", "finish-durable": "consumed",
}


def eio_row(cut, reply, rc, present, repost, stderr=""):
    return {"cut": cut, "action": "eio", "post": {"reply": reply},
            "owner": {"rc": rc, "stderr": stderr},
            "inspect_candidate": {"rc": 0 if present else 1, "identical": True},
            "inspect_prior": {"rc": 0, "identical": True},
            "reread_owner_ready": True,
            "repost": None if repost is None else {"reply": repost}}


SWALLOWED_LINE = ("uncertain cleanup path=staging error=EIO "
                  "message-id=<candidate@campaign.invalid>")


class PostArmDerivationTests(unittest.TestCase):
    def test_every_post_cut_has_the_arm_its_coordinate_gives(self):
        self.assertEqual(probe.verify_post_arms(), EXPECTED_ARMS)
        self.assertEqual(set(EXPECTED_ARMS), {c.name for c in native_cuts.POST_CUTS})

    def test_the_host_swallows_exactly_the_swallowed_cuts(self):
        native_cuts.verify_swallowed_cuts()

    def test_a_cut_moved_out_of_ignore_errors_is_caught(self):
        source = (ROOT / "host/native/io.lisp").read_text()
        moved = source.replace(
            "(fnn-at store :record-stage-unlinked)\n", "", 1).replace(
            "(fnn-at store :record-staging-cleaned)",
            "(fnn-at store :record-stage-unlinked) (fnn-at store :record-staging-cleaned)", 1)
        self.assertNotEqual(moved, source)
        with self.assertRaisesRegex(AssertionError, "record-stage-unlinked"):
            native_cuts.verify_swallowed_cuts(moved)

    def test_the_arm_follows_the_publication_step_not_the_name(self):
        # Move the record program's link before record-created: the cut that
        # was pre-publication becomes uncertain.
        steps = native_cuts.model_steps("fn-bs-record-program")
        link = next(s for s in steps if s.kind == "link")
        moved = (link,) + tuple(s for s in steps if s is not link)
        cut = next(c for c in native_cuts.POST_CUTS if c.name == "record-created")
        with mock.patch.object(native_cuts, "model_steps",
                               lambda program, book=None: moved):
            self.assertEqual(probe.post_arm(cut), "uncertain")
        self.assertEqual(probe.post_arm(cut), "refused")

    def test_the_marker_cuts_are_uncertain_by_program_order(self):
        # fn-bs-marker-program runs after the record program returned
        # durable, so a marker cut before the marker's own rename is still
        # uncertain, never refused.  Put the marker program first and the same
        # cut becomes pre-publication, which the table's `present' refuses.
        marker = [c for c in native_cuts.POST_CUTS if c.program == "fn-bs-marker-program"]
        self.assertEqual([c.name for c in marker],
                         ["marker-created", "marker-written", "marker-staged-durable",
                          "marker-replaced", "marker-durable"])
        self.assertEqual({probe.post_arm(c) for c in marker}, {"uncertain"})
        moved = ("fn-bs-marker-program", "fn-bs-frontier-program",
                 "fn-bs-record-program", "fn-bs-finish-program")
        with mock.patch.object(native_cuts, "POST_PROGRAMS", moved):
            self.assertEqual(probe.post_arm(marker[0]), "refused")
            with self.assertRaisesRegex(AssertionError, "marker-created: arm refused"):
                probe.verify_post_arms()

    def test_a_table_disagreeing_with_the_arm_is_refused(self):
        cuts = tuple(replace(c, candidate="either") if c.name == "record-written" else c
                     for c in native_cuts.POST_CUTS)
        with mock.patch.object(native_cuts, "POST_CUTS", cuts):
            with self.assertRaisesRegex(AssertionError, "record-written: arm refused"):
                probe.verify_post_arms()


class JudgeTeethTests(unittest.TestCase):
    def test_refused_arm(self):
        good = eio_row("record-created", probe.STORAGE_FAILED, 0, False, probe.OK_240)
        self.assertEqual(probe.judge_cut(good), [])
        for bad in (dict(good, post={"reply": probe.UNCERTAIN}),
                    dict(good, owner={"rc": 3, "stderr": ""}),
                    dict(good, inspect_candidate={"rc": 0, "identical": True}),
                    dict(good, repost=None),
                    dict(good, repost={"reply": probe.DUPLICATE})):
            self.assertTrue(probe.judge_cut(bad), bad)

    def test_the_stale_table_answer_fails_at_a_new_cut(self):
        # What the pre-H1 table demanded at frontier-created.
        stale = eio_row("frontier-created", probe.UNCERTAIN, 3, False, probe.OK_240)
        self.assertTrue(probe.judge_cut(stale))

    def test_swallowed_arm_needs_one_log_line(self):
        good = eio_row("record-stage-unlinked", probe.OK_240, 0, True,
                       probe.DUPLICATE, "accepted post path=served\n" + SWALLOWED_LINE + "\n")
        self.assertEqual(probe.judge_cut(good), [])
        silent = dict(good, owner={"rc": 0, "stderr": "accepted post path=served\n"})
        self.assertIn("0 times", " ".join(probe.judge_cut(silent)))
        twice = dict(good, owner={"rc": 0, "stderr": (SWALLOWED_LINE + "\n") * 2})
        self.assertIn("2 times", " ".join(probe.judge_cut(twice)))
        # A line naming staging and cleanup but not the error does not count.
        vague = dict(good, owner={"rc": 0, "stderr": "note cleanup path=staging\n"})
        self.assertTrue(probe.judge_cut(vague))
        for bad in (dict(good, post={"reply": probe.UNCERTAIN}),
                    dict(good, inspect_candidate={"rc": 1}),
                    # D25: the poster's own bytes again are not "a different
                    # article"; the pre-D25 conflict line now fails.
                    dict(good, repost={"reply": probe.CONFLICT})):
            self.assertTrue(probe.judge_cut(bad), bad)

    def test_consumed_and_uncertain_arms(self):
        self.assertEqual(probe.judge_cut(eio_row(
            "finish-durable", probe.OK_240, 3, True, probe.DUPLICATE)), [])
        self.assertTrue(probe.judge_cut(eio_row(
            "finish-durable", probe.STORAGE_FAILED, 3, True, probe.DUPLICATE)))
        self.assertEqual(probe.judge_cut(eio_row(
            "record-attempted", probe.UNCERTAIN, 3, True, probe.DUPLICATE)), [])
        self.assertTrue(probe.judge_cut(eio_row(
            "record-attempted", probe.OK_240, 3, True, probe.DUPLICATE)))

    def test_marker_arm(self):
        good = eio_row("marker-created", probe.UNCERTAIN, 3, True, probe.DUPLICATE)
        self.assertEqual(probe.judge_cut(good), [])
        refused = eio_row("marker-created", probe.STORAGE_FAILED, 0, False, probe.OK_240)
        self.assertTrue(probe.judge_cut(refused))
        for bad in (dict(good, post={"reply": probe.OK_240}),
                    dict(good, owner={"rc": 0, "stderr": ""}),
                    dict(good, inspect_candidate={"rc": 1}),
                    dict(good, repost={"reply": probe.CONFLICT})):
            self.assertTrue(probe.judge_cut(bad), bad)

    def test_kill_rows_take_the_table_fate(self):
        row = eio_row("record-durable", "", -9, False, probe.OK_240)
        row["action"] = "kill"
        self.assertIn("candidate present=False != True", " ".join(probe.judge_cut(row)))


WORDING = "repost {!r} not in {}".format(probe.CONFLICT, [probe.DUPLICATE])


def wording_affected(row) -> bool:
    """A row whose recorded repost D25 rewords: the article was present and
    the pre-D25 owner answered the conflict line (its key held
    Injection-Date, so a later clock second read as a different article;
    campaign 47bdb9a4, K1).  Pre-D25 the judge accepted it."""
    return (row.get("inspect_candidate") or {}).get("rc") == 0 and \
        (row.get("repost") or {}).get("reply") == probe.CONFLICT


class RecordedRunTests(unittest.TestCase):
    """The recorded runs predate D25.  Rows whose repost D25 rewords are judged
    without that one check; every other row, and every other check of those
    rows, is judged by today's rule, and the only failure left is the silent
    swallow at record-stage-unlinked eio (probe-tables S1)."""

    def test_pre_d25_runs_fail_only_on_the_silent_swallow_and_the_wording(self):
        present = [p for p in RECORDED_RUNS if (EVIDENCE / p).is_file()]
        if not present:
            self.skipTest("recorded probe runs absent")
        for path in present:
            with self.subTest(path):
                self.check_run(path)

    def check_run(self, path):
        result = json.loads(gzip.decompress((EVIDENCE / path).read_bytes()))
        verdict = probe.judge(result)
        self.assertEqual(verdict["total"], 40)
        self.assertEqual(verdict["failed"], RECORDED_RUNS[path])
        rows = result["cuts"] + result["controls"]
        affected = {"{} {}".format(r["cut"], r["action"]) if "cut" in r else r["name"]
                    for r in rows if wording_affected(r)}
        self.assertIn("record-stage-unlinked eio", affected)
        residual = {}
        for row in verdict["rows"]:
            failures = list(row["failures"])
            if row["row"] in affected:
                self.assertIn(WORDING, failures, row["row"])
                failures.remove(WORDING)
            else:
                self.assertNotIn(WORDING, failures, row["row"])
            if failures:
                residual[row["row"]] = failures
        self.assertEqual(list(residual), ["record-stage-unlinked eio"])
        self.assertEqual(len(residual["record-stage-unlinked eio"]), 1)
        self.assertIn("swallowed cleanup error 0 times",
                      residual["record-stage-unlinked eio"][0])
        # Every failing row today is the swallow or a reworded repost.
        self.assertEqual(verdict["failed"], len(affected))


if __name__ == "__main__":
    unittest.main()
