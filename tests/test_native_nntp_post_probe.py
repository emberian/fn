"""The NNTP probe's per-cut expectation, derived from the model coordinate.

Campaign 6c0626c5 finding H1: the probe judged five rows against a hand list
of pre-publication cuts that predated lane p10-k0's four new cuts.  These
tests pin the derivation rule of `post_arm`, show each arm separates rows
the others accept, and re-judge the recorded 6c0626c5 run.
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
RECORDED = ROOT / "planning/evidence/campaign-6c0626c5/nntp-probe.json.gz"
RERUN = ROOT / "planning/evidence/probe-tables/nntp-probe.json.gz"

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
                       probe.CONFLICT, "accepted post path=served\n" + SWALLOWED_LINE + "\n")
        self.assertEqual(probe.judge_cut(good), [])
        silent = dict(good, owner={"rc": 0, "stderr": "accepted post path=served\n"})
        self.assertIn("0 times", " ".join(probe.judge_cut(silent)))
        twice = dict(good, owner={"rc": 0, "stderr": (SWALLOWED_LINE + "\n") * 2})
        self.assertIn("2 times", " ".join(probe.judge_cut(twice)))
        # A line naming staging and cleanup but not the error does not count.
        vague = dict(good, owner={"rc": 0, "stderr": "note cleanup path=staging\n"})
        self.assertTrue(probe.judge_cut(vague))
        for bad in (dict(good, post={"reply": probe.UNCERTAIN}),
                    dict(good, inspect_candidate={"rc": 1})):
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

    def test_kill_rows_take_the_table_fate(self):
        row = eio_row("record-durable", "", -9, False, probe.OK_240)
        row["action"] = "kill"
        self.assertIn("candidate present=False != True", " ".join(probe.judge_cut(row)))


@unittest.skipUnless(RECORDED.is_file() and RERUN.is_file(),
                     "recorded 6c0626c5 probe runs absent")
class RecordedRunTests(unittest.TestCase):
    def test_the_6c0626c5_runs_fail_only_on_the_silent_swallow(self):
        for path in (RECORDED, RERUN):
            with self.subTest(path.parent.name):
                self.check_run(path)

    def check_run(self, path):
        verdict = probe.judge(json.loads(gzip.decompress(path.read_bytes())))
        failed = {r["row"]: r["failures"] for r in verdict["rows"] if r["failures"]}
        self.assertEqual(list(failed), ["record-stage-unlinked eio"])
        self.assertEqual(len(failed["record-stage-unlinked eio"]), 1)
        self.assertIn("swallowed cleanup error 0 times",
                      failed["record-stage-unlinked eio"][0])
        self.assertEqual(verdict["total"], 40)


if __name__ == "__main__":
    unittest.main()
