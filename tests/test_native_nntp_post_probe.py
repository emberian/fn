"""The served POST's wire reply per cut, on the record log (lane
ack-before-barrier; the per-file probe log-recovery-2 deleted in f93733f60,
rekeyed to the format-9 route).

`served_arm` derives each served cut's arm from its program's place relative
to the batch's append and barrier (tests/campaign/native_nntp_post_probe.py);
these tests pin the derivation, show a table that disagrees with an arm is
refused, and give the judge teeth: a cut before the reply never passes with
240, a kill row owes no reply, an EIO row is uncertain and stops the owner,
and the fate follows the arm.  With FN_NATIVE_CRASH_HOST (a source-matched
developer image; the production image beside it, when built, for the
controls) the probe runs every served cut, kill and EIO, and every row must
pass.
"""
import os
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest import mock

from tests.campaign import native_cuts
from tests.campaign import native_nntp_post_probe as probe

EXPECTED_ARMS = {
    "frontier-reserved": "pre-append", "record-completing": "pre-append",
    "finish-consumed": "pre-append", "finish-durable": "pre-append",
    "log-written": "appended", "log-fenced": "fenced",
    "statement-committed": "fenced",
}


def row(cut, action, reply, rc, present, repost):
    return {"cut": cut, "action": action, "post": {"reply": reply},
            "owner": {"rc": rc, "stderr": ""},
            "inspect_candidate": {"rc": 0 if present else 1, "identical": True},
            "inspect_prior": {"rc": 0, "identical": True},
            "reread_owner_ready": True,
            "repost": None if repost is None else {"reply": repost}}


class ServedArmDerivationTests(unittest.TestCase):
    def test_every_served_cut_has_the_arm_its_coordinate_gives(self):
        self.assertEqual(probe.verify_served_arms(), EXPECTED_ARMS)
        self.assertEqual({c.name for c in probe.served_cuts()},
                         set(EXPECTED_ARMS) - {"statement-committed"})

    def test_the_served_order_is_the_hosts(self):
        # START drains (reserve, place, finish) before the seal; the append
        # precedes the barrier (native_cuts.verify_post_log_cut_map reads the
        # host for both).
        native_cuts.verify_post_log_cut_map()
        native_cuts.verify_statement_cut_map()

    def test_a_table_disagreeing_with_the_arm_is_refused(self):
        for name, wrong in (("record-completing", "present"), ("log-written", "absent"),
                            ("log-fenced", "either"), ("finish-durable", "present")):
            cuts = tuple(replace(c, candidate=wrong) if c.name == name else c
                         for c in probe.served_cuts())
            with self.subTest(name), self.assertRaisesRegex(AssertionError, name + ": arm"):
                probe.verify_served_arms(cuts)

    def test_a_statement_cut_before_its_barrier_is_refused(self):
        cuts = tuple(replace(c, candidate="absent") for c in native_cuts.STATEMENT_CUTS)
        with mock.patch.object(native_cuts, "STATEMENT_CUTS", cuts):
            with self.assertRaisesRegex(AssertionError, "statement-committed"):
                probe.verify_served_arms()

    def test_the_arm_follows_the_program_not_the_name(self):
        # Were the finish run after the barrier (a batch of one's order), its
        # cut would be fenced, and the table's `absent' refused.
        moved = ("fn-lg-reserve-program", "fn-lg-order-program", "fn-lg-append-program",
                 "fn-lg-fence-program", "fn-bs-finish-program")
        cut = next(c for c in probe.served_cuts() if c.name == "finish-durable")
        self.assertEqual(probe.served_arm(cut), "pre-append")
        with mock.patch.object(probe, "SERVED_PROGRAMS", moved):
            self.assertEqual(probe.served_arm(cut), "fenced")
            with self.assertRaisesRegex(AssertionError, "finish-consumed: arm fenced"):
                probe.verify_served_arms()


class JudgeTeethTests(unittest.TestCase):
    def test_no_cut_before_the_reply_passes_with_240(self):
        for cut in probe.served_cuts():
            for action in ("kill", "eio"):
                bad = row(cut.name, action, probe.OK_240, -9 if action == "kill" else 3,
                          True, probe.DUPLICATE)
                self.assertIn("a cut before the reply answered 240",
                              probe.judge_cut(bad), (cut.name, action))

    def test_kill_rows(self):
        self.assertEqual(probe.judge_cut(row("finish-durable", "kill", "", -9, False,
                                             probe.OK_240)), [])
        self.assertTrue(probe.judge_cut(row("finish-durable", "kill", "", -9, True,
                                            probe.DUPLICATE)))
        self.assertEqual(probe.judge_cut(row("log-fenced", "kill", "", -9, True,
                                             probe.DUPLICATE)), [])
        self.assertTrue(probe.judge_cut(row("log-fenced", "kill", "", -9, False,
                                            probe.OK_240)))
        for present, repost in ((True, probe.DUPLICATE), (False, probe.OK_240)):
            self.assertEqual(probe.judge_cut(row("log-written", "kill", "", -9, present,
                                                 repost)), [])
        self.assertTrue(probe.judge_cut(row("log-written", "kill", probe.UNCERTAIN, -9,
                                            True, probe.DUPLICATE)))

    def test_eio_rows(self):
        good = row("record-completing", "eio", probe.UNCERTAIN, 3, False, probe.OK_240)
        self.assertEqual(probe.judge_cut(good), [])
        self.assertEqual(probe.judge_cut(dict(good, post={"reply": ""})), [])
        for bad in (dict(good, post={"reply": probe.STORAGE_FAILED}),
                    dict(good, owner={"rc": 0, "stderr": ""}),
                    dict(good, inspect_candidate={"rc": 0, "identical": True}),
                    dict(good, repost={"reply": probe.DUPLICATE}),
                    dict(good, repost=None)):
            self.assertTrue(probe.judge_cut(bad), bad)
        fenced = row("log-fenced", "eio", probe.UNCERTAIN, 3, True, probe.DUPLICATE)
        self.assertEqual(probe.judge_cut(fenced), [])
        self.assertTrue(probe.judge_cut(dict(fenced, inspect_candidate={"rc": 1})))

    def test_controls(self):
        ok = {"name": "dev-accepted-then-sigkill", "post": {"reply": probe.OK_240},
              "inspect_candidate": {"rc": 0, "identical": True},
              "repost": {"reply": probe.DUPLICATE}}
        self.assertEqual(probe.judge_control(ok), [])
        self.assertTrue(probe.judge_control(dict(ok, post={"reply": probe.UNCERTAIN})))
        refused = {"name": "dev-refused-no-from", "post": {"reply": probe.NO_FROM},
                   "inspect_candidate": {"rc": 1}}
        self.assertEqual(probe.judge_control(refused), [])
        self.assertTrue(probe.judge_control(dict(refused, inspect_candidate={"rc": 0})))


DEV = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))


@unittest.skipUnless(DEV.is_file() and os.access(DEV, os.X_OK),
                     "set FN_NATIVE_CRASH_HOST to a source-matched developer image")
class NativeServedWireProbeTests(unittest.TestCase):
    def test_every_served_cut_answers_as_its_coordinate_says(self):
        selected = os.environ.get("FN_NATIVE_SERVED_CUT")
        with tempfile.TemporaryDirectory(prefix="fn-nntp-probe-") as tmp:
            base = Path(tmp)
            images = base / "images"
            images.mkdir()
            (images / "fn-host-developer").symlink_to(DEV.resolve())
            prod = DEV.parent / "fn-host"
            if prod.is_file():
                (images / "fn-host").symlink_to(prod.resolve())
            result = probe.run(images, base / "work", base / "probe.json",
                               cuts={selected} if selected else None)
            verdict = result["judgement"]
            probe.print_judgement(verdict)
            expected = (len(probe.served_cuts()) if not selected else 1) * 2
            self.assertEqual(len(result["cuts"]), expected)
            self.assertEqual(verdict["failed"], 0,
                             [r for r in verdict["rows"] if r["failures"]])


if __name__ == "__main__":
    unittest.main()
