"""Native A3 article/receipt path over one FNBS owner per process.

The relay copies bytes only.  It does not manufacture TCPCL acknowledgement,
BP acceptance, Store commitment, or an application receipt.
"""

import os
from pathlib import Path
import select
import shutil
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement
from tests.test_bp_contact_relay_native import ByteRelay
from tools import run_bp_ingress, run_store


ROOT = Path(os.environ.get(
    "FN_NATIVE_SOURCE_ROOT", Path(__file__).resolve().parent.parent))
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


class NativeBpNodeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(f"native developer image missing: {IMAGE}")

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-bp-node-a3-"))
        self.addCleanup(shutil.rmtree, self.tmp)
        self.env = environment()
        self.relay = ByteRelay()
        self.addCleanup(self.relay.close)
        self.receiver_store = self.tmp / "receiver-store"
        self.receiver_journal = self.tmp / "receiver-fnbs"
        self.receiver_receipts = self.tmp / "receiver-fnrj"
        self.sender_store = self.tmp / "sender-store"
        self.sender_journal = self.tmp / "sender-fnbs"
        self.sender_workflow = self.tmp / "sender-fnwf"
        self.request_path = self.tmp / "request.adu"
        self.msgid = b"<bp-node-a3@example.invalid>"
        self.article = (
            b"Path: sender.bp.gate.invalid!not-for-mail\r\n"
            b"From: sender@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: native BP node A3\r\n"
            b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
            b"Message-ID: " + self.msgid + b"\r\n"
            b"Xref: sender.bp.gate.invalid fn.test:1\r\n\r\nA3 body\r\n"
        )
        for store in (self.receiver_store, self.sender_store):
            initialized = self.invoke("store", store, "init", "fn.test")
            self.assertEqual(initialized.returncode, 0, initialized.stderr)
        self.author_request()
        self.prepare_sender_obligation()

    def invoke(self, *args, env=None, timeout=120):
        return subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False,
        )

    def author_request(self):
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-adu")')
            self.assertEqual(bridge.extract_message_id(self.article), self.msgid)
            _archive, subject, _provenance = run_store.metadata(
                self.msgid, self.article)

            def text(value):
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = [
                b"work-bp-node", subject, b"dtn://sender/",
                b"dtn://receiver/", b"native-policy", b"origin-native",
                b"wire-auth", b"terms-native",
            ]
            form = (
                "(fn-bpa-encode (fn-bpa-make-request "
                + " ".join(text(value) for value in fields)
                + " '" + bridge.literal(self.article) + "))"
            )
            self.request_path.write_bytes(run_store.acl2_octets(bridge.call(form)))
        finally:
            bridge.close()

    def prepare_sender_obligation(self):
        article_path = self.tmp / "sender-article"
        article_path.write_bytes(self.article)
        posted = self.invoke(
            "store", self.sender_store, "post", self.msgid.decode(),
            article_path, "-", "-", "fn.test",
        )
        self.assertEqual(posted.returncode, 0, posted.stderr)
        for args in (
            ("app-journal", "workflow-init", self.sender_store,
             self.sender_workflow, "dtn://sender/", "dtn://receiver/",
             "native-policy", "dtn://receiver/", 3600000,
             "origin-native", "wire-auth"),
            ("app-journal", "workflow-enqueue", self.sender_store,
             self.sender_workflow, 1, 0, "work-bp-node", self.msgid.decode(),
             "forward-bp-node", "dtn://receiver/", "native-policy",
             "terms-native"),
            ("bp-obligation", "undertake", self.sender_store,
             self.sender_workflow, "work-bp-node", 3),
        ):
            result = self.invoke(*args)
            self.assertEqual(result.returncode, 0, result.stderr)
        unrelated_id = b"<bp-node-unrelated@example.invalid>"
        unrelated_article = self.article.replace(self.msgid, unrelated_id)
        unrelated_path = self.tmp / "unrelated-article"
        unrelated_path.write_bytes(unrelated_article)
        for args in (
            ("store", self.sender_store, "post", unrelated_id.decode(),
             unrelated_path, "-", "-", "fn.test"),
            ("app-journal", "workflow-enqueue", self.sender_store,
             self.sender_workflow, 2, 0, "work-unrelated",
             unrelated_id.decode(), "forward-unrelated", "dtn://receiver/",
             "native-policy", "terms-native"),
            ("bp-obligation", "undertake", self.sender_store,
             self.sender_workflow, "work-unrelated", 2),
        ):
            result = self.invoke(*args)
            self.assertEqual(result.returncode, 0, result.stderr)

    def start_node(self, receiver, *, once=True, extra_env=None, trust=True,
                   inbound=True):
        node = "dtn://receiver/" if receiver else "dtn://sender/"
        peer = "dtn://sender/" if receiver else "dtn://receiver/"
        journal = self.receiver_journal if receiver else self.sender_journal
        store = self.receiver_store if receiver else self.sender_store
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as reservation:
            reservation.bind(("127.0.0.1", 0))
            listen_port = reservation.getsockname()[1]
        config = self.tmp / ("receiver-fn.toml" if receiver else "sender-fn.toml")
        config.write_text(f'[store]\npath = "{store}"\n', encoding="ascii")
        admitted_name = "sender-boundary" if receiver else "receiver-boundary"
        if trust:
            local_path = "receiver.bp.gate.invalid" if receiver else "sender.bp.gate.invalid"
            remote_path = "sender.bp.gate.invalid" if receiver else "receiver.bp.gate.invalid"
            policy = self.invoke(
                "operator", config, "policy", "set", "path-identity", local_path,
            )
            self.assertEqual(policy.returncode, 0, policy.stderr)
            installed = self.invoke(
                "operator", config, "bp-boundary", "add", admitted_name,
                remote_path, peer, listen_port,
                *(["fn.test", "32768", "16"] if inbound else []),
            )
            self.assertEqual(installed.returncode, 0, installed.stderr)
        receipts = self.receiver_receipts if receiver else self.tmp / "sender-fnrj"
        workflow = self.tmp / "receiver-fnwf" if receiver else self.sender_workflow
        env = dict(self.env)
        if extra_env:
            env.update(extra_env)
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "bp-node", "serve", str(listen_port),
             str(journal), str(store), str(receipts), str(workflow),
             node, peer, node, "native-policy", node,
             "127.0.0.1", str(self.relay.port),
             "1" if once else "0", "3600000", "2", "32", "1048576",
             "0", "0"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0,
        )
        self.addCleanup(self.stop_process, process)
        line = wait_for_announcement(process, b"BP NODE LISTENING ", timeout=45)
        if not line.startswith(b"BP NODE LISTENING "):
            self.fail(f"node failed: {line!r} {stop_and_diagnostics(process)}")
        return process, int(line.rsplit(b" ", 1)[1])

    @staticmethod
    def stop_process(process):
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=5)
        process.stdout.close()
        process.stderr.close()

    def send_request(self, port, work, *, lifetime=3600000):
        return self.invoke(
            "bp-service", "run", "127.0.0.1", port,
            self.request_path, self.sender_journal,
            "dtn://sender/", "dtn://receiver/", work, work + "-attempt", 0,
            lifetime, 2, 32, 1048576, 0, 0,
        )

    def tick_receiver(self):
        return self.invoke(
            "bp-contact", "tick", self.receiver_journal,
            "dtn://receiver/", "dtn://sender/", 0, 60000,
            3600000, 2, 32, 1048576, 0, 0,
        )

    def dispatch_receiver(self, *, env=None):
        return self.invoke(
            "bp-node", "dispatch", self.receiver_journal,
            self.receiver_store, self.receiver_receipts,
            self.tmp / "receiver-fnwf", "dtn://receiver/",
            "dtn://sender/", "dtn://receiver/", "native-policy",
            "dtn://receiver/", "127.0.0.1", self.relay.port,
            1, 3600000, 2, 32, 1048576, 0, 0, env=env,
        )

    def sender_status(self):
        return self.invoke(
            "bp-obligation", "status", self.sender_store,
            self.sender_workflow, "work-bp-node",
        )

    def unrelated_status(self):
        return self.invoke(
            "bp-obligation", "status", self.sender_store,
            self.sender_workflow, "work-unrelated",
        )

    def receiver_counts(self):
        store, bridge, records = run_bp_ingress.open_live_bp_store(
            self.receiver_store, False)
        try:
            return len(records), bridge.article_count(), bridge.pin_count()
        finally:
            bridge.close()
            store.close()

    def test_request_retry_queues_distinct_receipt_carriers_and_releases_pin(self):
        before = self.sender_status()
        self.assertEqual(before.returncode, 0, before.stderr)
        self.assertIn(b"pinned=yes", before.stdout)

        first, port = self.start_node(True)
        sent = self.send_request(port, "carrier-one")
        out, err = first.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(first.returncode, 0, err)
        self.assertIn(b"BP application handoff durable", out)
        self.assertIn(b"BP node receipt queued", out)
        first_count = len(tuple((self.receiver_journal / "lifecycle").glob("*.fnb")))

        second, port = self.start_node(True)
        retry = self.send_request(port, "carrier-two")
        out, err = second.communicate(timeout=120)
        self.assertEqual(retry.returncode, 0, retry.stderr)
        self.assertEqual(second.returncode, 0, err)
        self.assertIn(b"BP node receipt queued", out)
        self.assertGreater(
            len(tuple((self.receiver_journal / "lifecycle").glob("*.fnb"))),
            first_count,
        )
        self.assertEqual(self.receiver_counts()[1], 1,
                         "the second carrier must not accept a second article")
        store, bridge, _ = run_bp_ingress.open_live_bp_store(
            self.receiver_store, False)
        try:
            relayed = bridge.lookup(self.msgid)
            self.assertNotEqual(relayed, self.article)
            self.assertIn(b"Path: receiver.bp.gate.invalid", relayed)
            self.assertNotIn(b"Xref:", relayed)
        finally:
            bridge.close()
            store.close()

        sender, port = self.start_node(False, once=False)
        self.relay.route(port)
        delivered = self.tick_receiver()
        self.assertEqual(delivered.returncode, 0, delivered.stderr)
        self.assertIn(b"BP contact open", delivered.stdout)
        self.wait_for_output(
            sender, b"BP node delivery receipt-accepted", timeout=120)
        self.stop_process(sender)
        after = self.sender_status()
        self.assertEqual(after.returncode, 0, after.stderr)
        self.assertIn(b"pinned=no", after.stdout)
        unrelated = self.unrelated_status()
        self.assertEqual(unrelated.returncode, 0, unrelated.stderr)
        self.assertIn(b"pinned=yes", unrelated.stdout)

    def test_absent_bp_trust_keeps_custody_but_refuses_request_application(self):
        receiver, port = self.start_node(True, trust=False)
        sent = self.send_request(port, "untrusted-request")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(receiver.returncode, 0, err)
        self.assertIn(b"BP node delivery request-refused", out)
        self.assertEqual(self.receiver_counts()[1], 0)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

    def test_admitted_channel_without_inbound_scope_refuses_store_request(self):
        receiver, port = self.start_node(True, inbound=False)
        sent = self.send_request(port, "no-inbound-scope")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(receiver.returncode, 0, err)
        self.assertIn(b"BP node delivery request-refused", out)
        self.assertEqual(self.receiver_counts()[1], 0)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

    def test_absent_bp_trust_refuses_receipt_release(self):
        receiver, port = self.start_node(True)
        sent = self.send_request(port, "untrusted-return")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(receiver.returncode, 0, err)
        self.assertIn(b"BP node receipt queued", out)
        sender, port = self.start_node(False, once=False, trust=False)
        self.relay.route(port)
        delivered = self.tick_receiver()
        self.assertEqual(delivered.returncode, 0, delivered.stderr)
        self.wait_for_output(sender, b"BP node delivery receipt-refused", timeout=120)
        self.stop_process(sender)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

    @staticmethod
    def wait_for_output(process, marker, timeout=45):
        deadline = time.monotonic() + timeout
        captured = bytearray()
        while time.monotonic() < deadline:
            if process.poll() is not None:
                break
            ready = select.select([process.stdout], [], [], 0.2)[0]
            if ready:
                line = process.stdout.readline()
                captured.extend(line)
                if marker in captured:
                    return bytes(captured)
        raise AssertionError(
            f"native marker {marker!r} absent: {bytes(captured)!r}; "
            f"{stop_and_diagnostics(process)}"
        )

    def test_conflicting_return_job_fences_after_request_commit(self):
        conflict = self.tmp / "conflict.adu"
        conflict.write_bytes(b"not the FNRJ receipt ADU")
        # The new first held request will have arrival zero.  The conflicting
        # job is durable in the same FNBS base before that request arrives.
        planted = self.invoke(
            "bp-service", "run", "127.0.0.1", 1, conflict,
            self.receiver_journal, "dtn://receiver/", "dtn://sender/",
            "bp-receipt:receipt:work-bp-node:0", "return", 0,
            3600000, 2, 32, 1048576, 0, 0,
        )
        self.assertIn(b"BP queue accepted", planted.stdout)
        receiver, port = self.start_node(True)
        sent = self.send_request(port, "conflict-request")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(receiver.returncode, 3, (out, err))
        self.assertIn(b"conflicting durable bytes", err)
        self.assertIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_exact_receipt_with_wrong_carrier_peer_fences(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN",
            b"BP NODE KIND7 DURABLE",
        )
        replay = self.invoke(
            "app-journal", "receipt-replay", self.receiver_store,
            self.receiver_receipts, self.request_path,
        )
        self.assertEqual(replay.returncode, 0, replay.stderr)
        receipt = self.tmp / "exact-receipt-wrong-peer.adu"
        receipt.write_bytes(bytes.fromhex(
            replay.stdout.split(b"hex=", 1)[1].strip().decode("ascii")))
        planted = self.invoke(
            "bp-service", "run", "127.0.0.1", 1, receipt,
            self.receiver_journal, "dtn://receiver/", "dtn://other/",
            "bp-receipt:receipt:work-bp-node:0", "return", 0,
            3600000, 2, 32, 1048576, 0, 0,
        )
        self.assertIn(b"BP queue accepted", planted.stdout)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 3, restarted.stderr)
        self.assertIn(b"conflicting durable bytes", restarted.stderr)
        self.assertEqual(self.receiver_counts()[1], 1)

    def kill_at_durable_cut(self, selector, marker):
        receiver, port = self.start_node(True, extra_env={selector: "1"})
        sent = self.send_request(port, "cut-request")
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.wait_for_output(receiver, marker, timeout=120)
        receiver.kill()
        receiver.wait(timeout=15)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_death_after_fnrj_receipt_decision_replays_one_article(self):
        self.kill_at_durable_cut(
            "FN_BP_APP_TEST_PAUSE_AFTER_DECISION",
            b"BP APP DECISION DURABLE",
        )
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP application handoff durable", restarted.stdout)
        self.assertIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_death_after_kind_seven_replays_owed_outbox(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN",
            b"BP NODE KIND7 DURABLE",
        )
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_death_after_durable_outbox_does_not_allocate_second_sequence(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX",
            b"BP NODE OUTBOX DURABLE",
        )
        before_records = len(tuple(
            (self.receiver_journal / "lifecycle").glob("*.fnb")))
        frontier = self.receiver_journal / "sequence" / "frontier.fnb"
        before_frontier = frontier.read_bytes()
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertNotIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(frontier.read_bytes(), before_frontier)
        self.assertEqual(len(tuple(
            (self.receiver_journal / "lifecycle").glob("*.fnb"))), before_records)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_ambiguous_outbox_publication_is_uncertain_not_refused(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN",
            b"BP NODE KIND7 DURABLE",
        )
        fault_env = dict(self.env)
        fault_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        ambiguous = self.dispatch_receiver(env=fault_env)
        self.assertEqual(ambiguous.returncode, 3,
                         (ambiguous.stdout, ambiguous.stderr))
        self.assertIn(b"uncertain", ambiguous.stderr.lower())
        self.assertNotIn(b"BP node receipt queued", ambiguous.stdout)

        # Reopen fences the uncertain publication by reading FNBS and its
        # sequence frontier.  The earlier Store/FNRJ decision is not replayed
        # into a second accepted article or a fresh return-job sequence.
        frontier = self.receiver_journal / "sequence" / "frontier.fnb"
        after_fault_frontier = frontier.read_bytes()
        recovered = self.dispatch_receiver()
        self.assertEqual(recovered.returncode, 0,
                         (recovered.stdout, recovered.stderr))
        self.assertEqual(frontier.read_bytes(), after_fault_frontier)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_kind_five_ambiguous_publication_never_delivers_to_store(self):
        seed = self.dispatch_receiver()
        self.assertEqual(seed.returncode, 0, seed.stderr)
        receiver, port = self.start_node(
            True, extra_env={"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"})
        sent = self.send_request(port, "kind-five-cut")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(receiver.returncode, 3, (out, err))
        self.assertNotIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_counts()[1], 0)
        self.assertIn(sent.returncode, (1, 3), sent.stderr)

    def test_ambiguous_fnrj_decision_fences_until_cold_replay(self):
        receiver, port = self.start_node(
            True,
            extra_env={
                "FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE": "1",
            },
        )
        sent = self.send_request(port, "fnrj-uncertain")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(receiver.returncode, 3, (out, err))
        self.assertIn(b"BP node application uncertain", out)
        self.assertNotIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_counts()[1], 1)

        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP application handoff durable", restarted.stdout)
        self.assertIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_expired_recovered_kind_five_never_enters_store(self):
        receiver, port = self.start_node(
            True,
            extra_env={"FN_BP_NODE_TEST_PAUSE_AFTER_KIND_FIVE": "1"},
        )
        sent = self.send_request(port, "short-lived", lifetime=1500)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.wait_for_output(receiver, b"BP NODE KIND5 DURABLE", timeout=120)
        receiver.kill()
        receiver.wait(timeout=15)
        time.sleep(1.8)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertNotIn(b"BP application handoff durable", restarted.stdout)
        self.assertNotIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 0)


if __name__ == "__main__":
    unittest.main()
