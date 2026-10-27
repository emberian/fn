"""The served POST's wire reply per cut, on the record log (lane
ack-before-barrier; the per-file probe log-recovery-2 deleted in f93733f60,
rekeyed to the record-log route).

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


class DeadNodeStartTests(unittest.TestCase):
    def test_cut_uses_its_own_greeting_before_sending_post(self):
        import io
        from tests.campaign.native_operator_campaign import Node
        from tests import native_harness as harness
        for greeting, alive in ((b"200 ready\r\n", True), (b"201 ready\r\n", True),
                                (b"", True), (b"400 closing\r\n", True),
                                (b"200 ready\r\n", False)):
            with self.subTest(greeting=greeting, alive=alive):
                process = mock.Mock(pid=123)
                process.poll.return_value = None
                node = object.__new__(Node)
                node.port, node.owners = 2345, [{"proc": process}]
                harness.require_node_greeting(process, node.port)
                process.poll.return_value = None if alive else 3
                conn = mock.MagicMock()
                conn.__enter__.return_value = conn
                conn.makefile.return_value = io.BytesIO(greeting + b"340 send\r\n")
                try:
                    with mock.patch.object(probe.socket, "create_connection", return_value=conn) as connect:
                        if alive and greeting[:3] in (b"200", b"201"):
                            result = probe.nntp_post(node, b"payload")
                            self.assertEqual(result["reply"], "")  # A cut after greeting can owe no reply.
                            self.assertEqual(harness.node_start_failures(self.id()), [])
                            conn.sendall.assert_any_call(b"POST\r\n")
                        else:
                            with self.assertRaisesRegex(harness.NodeDead, "node dead"):
                                probe.nntp_post(node, b"payload")
                            conn.sendall.assert_not_called()
                        connect.assert_called_once_with(("127.0.0.1", node.port), timeout=120)
                finally:
                    harness._NODE_GREETINGS.pop(self.id(), None)
                    harness._NODE_DEAD.pop(self.id(), None)

    def test_post_checks_liveness_after_greeting_credit_in_both_full_and_half_send_paths(self):
        import io
        from tests.campaign.native_operator_campaign import Node
        from tests import native_harness as harness
        for half in (False, True):
            for exits_after_greeting in (False, True):
                with self.subTest(half=half, exits_after_greeting=exits_after_greeting):
                    process = mock.Mock(pid=123)
                    process.poll.return_value = None
                    node = object.__new__(Node)
                    node.port = 2345
                    owner = {"proc": process, "ready": True}
                    node.owners = [owner]
                    node.start_owner = mock.Mock(return_value=owner)
                    node.stop_owner = mock.Mock(return_value={"rc": 0})
                    node.reap = mock.Mock()
                    harness.require_node_greeting(process, node.port)

                    def observe(greeting):
                        Node.observe_greeting(node, greeting)
                        if exits_after_greeting:
                            process.poll.return_value = 0

                    node.observe_greeting = observe
                    conn = mock.MagicMock()
                    conn.__enter__.return_value = conn
                    conn.makefile.return_value = io.BytesIO(b"200 ready\r\n340 send\r\n")
                    try:
                        with mock.patch.object(probe, "Node", return_value=node), \
                             mock.patch.object(probe, "seed"), \
                             mock.patch.object(probe, "settle") as settle, \
                             mock.patch.object(probe.socket, "create_connection", return_value=conn) as connect:
                            if exits_after_greeting:
                                with self.assertRaisesRegex(harness.NodeDead, "exited before POST"):
                                    probe.plain(Path("image"), Path("work"), Path("prior"),
                                                b"payload", "fixture", half=half)
                                conn.sendall.assert_not_called()
                                node.stop_owner.assert_not_called()
                                settle.assert_not_called()
                            else:
                                result = probe.plain(Path("image"), Path("work"), Path("prior"),
                                                     b"payload", "fixture", half=half)
                                self.assertTrue(result["owner_alive_after_post"])
                                conn.sendall.assert_any_call(b"POST\r\n")
                                settle.assert_called_once()
                            connect.assert_called_once()
                        # Crediting the received greeting and refusing a new
                        # POST after exit are separate facts about this owner.
                        self.assertEqual(harness._NODE_GREETINGS[self.id()][0]["evidence"], "NNTP greeting")
                        node.reap.assert_called_once_with()
                    finally:
                        harness._NODE_GREETINGS.pop(self.id(), None)
                        harness._NODE_DEAD.pop(self.id(), None)

    def test_dead_start_never_becomes_a_cut_or_recovery_row(self):
        from tests.native_harness import NodeDead
        node = mock.Mock()
        node.start_owner.side_effect = NodeDead("node dead: exited at start")
        with mock.patch.object(probe, "Node", return_value=node), \
             mock.patch.object(probe, "seed"), mock.patch.object(probe, "settle") as settle:
            with self.assertRaisesRegex(NodeDead, "node dead"):
                probe.faulted(Path("image"), Path("work"), Path("prior"), b"payload",
                              probe.served_cuts()[0], "kill")
        settle.assert_not_called()
        node.reap.assert_called_once_with()


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
