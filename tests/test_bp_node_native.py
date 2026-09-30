"""Native A3 article/receipt path over one FNBS owner per process.

The relay copies bytes only.  It does not manufacture TCPCL acknowledgement,
BP acceptance, Store commitment, or an application receipt.
"""

import collections
import os
from pathlib import Path
import re
import socket
import time
import unittest

from tests.native_harness import (
    Acl2Session,
    EXIT, Node, acl2_nat, acl2_octets, acl2_result, environment, free_port, native_image,
    requires, run, scratch, start)
from tests.test_bp_contact_relay_native import ByteRelay
from tests.bp_producer import post_articles
from tests.native_image_provenance import assert_same_published_source

# specs/host.md "BP run classes" (books/bp-run-class.lisp, PRF-131): a
# connection lost after it existed is EXIT.INTERRUPTED (connection-local:
# the job stays and is re-offered; no recovery); EXIT.UNCERTAIN stays the fence.
LOST = EXIT.INTERRUPTED



ROOT = Path(os.environ.get(
    "FN_NATIVE_SOURCE_ROOT", Path(__file__).resolve().parent.parent))
# The node runs on either developer image: FN_NATIVE_BP_NODE_HOST names the one
# under test (the DTN developer image, whose profile ships the node), and it
# falls back to the default developer image.
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
IMAGE = native_image("FN_NATIVE_BP_NODE_HOST", DEVELOPER)
# The DTN image omits the NNTP surface; a Store's groups are read back through
# the reader port of an image that has it (the default developer image).
READER_IMAGE = native_image("FN_NATIVE_READER_HOST", DEVELOPER)
PRODUCER = native_image("FN_NATIVE_HOST")


@requires(IMAGE, PRODUCER)
class NativeBpNodeTests(unittest.TestCase):
    def setUp(self):
        if self._testMethodName == (
                "test_disconnected_delivery_restarts_and_releases_only_matching_obligation"):
            self.image_source = assert_same_published_source(self, PRODUCER, IMAGE)
        self.tmp = scratch(self, "fn-bp-node-a3-")
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
            b"\r\nA3 body\r\n"
        )
        for store in (self.receiver_store, self.sender_store):
            initialized = self.invoke("store", store, "init", "fn.test")
            self.assertEqual(initialized.returncode, EXIT.OK, initialized.stderr)
        self.prepare_sender_obligation()
        self.author_request()

    def invoke(self, *args, env=None, timeout=120):
        return run([IMAGE, "--fn", *args], cwd=ROOT, env=environment(env), timeout=timeout)

    def author_request(self):
        with Acl2Session(IMAGE) as bridge:
            fields = [
                b"work-bp-node", bridge.subject(self.msgid, self.article), b"dtn://sender/",
                b"dtn://receiver/", b"native-policy", b"origin-native",
                b"wire-auth", b"terms-native",
            ]
            self.request_path.write_bytes(bridge.bp_request(fields, self.article))

    def prepare_sender_obligation(self):
        unrelated_id = b"<bp-node-unrelated@example.invalid>"
        injected = post_articles(self, PRODUCER, self.sender_store,
                                 [(self.msgid, self.article),
                                  (unrelated_id, self.article.replace(self.msgid, unrelated_id))],
                                 observer=(getattr(self, "resilience_observer", None)
                                           if self._testMethodName ==
                                           "test_disconnected_delivery_restarts_and_releases_only_matching_obligation"
                                           else None))
        self.article = injected[self.msgid]
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
            self.assertEqual(result.returncode, EXIT.OK, result.stderr)
        for args in (
            ("app-journal", "workflow-enqueue", self.sender_store,
             self.sender_workflow, 2, 0, "work-unrelated",
             unrelated_id.decode(), "forward-unrelated", "dtn://receiver/",
             "native-policy", "terms-native"),
            ("bp-obligation", "undertake", self.sender_store,
             self.sender_workflow, "work-unrelated", 2),
        ):
            result = self.invoke(*args)
            self.assertEqual(result.returncode, EXIT.OK, result.stderr)

    def start_node(self, receiver, *, once=True, extra_env=None, trust=True,
                   inbound=True, transfer_mru=1048576, control=False, configured=False):
        node = "dtn://receiver/" if receiver else "dtn://sender/"
        peer = "dtn://sender/" if receiver else "dtn://receiver/"
        journal = self.receiver_journal if receiver else self.sender_journal
        store = self.receiver_store if receiver else self.sender_store
        listen_port = free_port()
        config = self.tmp / ("receiver-fn.toml" if receiver else "sender-fn.toml")
        config.write_text(f'[store]\npath = "{store}"\n', encoding="ascii")
        admitted_name = "sender-boundary" if receiver else "receiver-boundary"
        if trust:
            local_path = "receiver.bp.gate.invalid" if receiver else "sender.bp.gate.invalid"
            remote_path = "sender.bp.gate.invalid" if receiver else "receiver.bp.gate.invalid"
            policy = self.invoke(
                "operator", config, "policy", "set", "path-identity", local_path,
            )
            self.assertEqual(policy.returncode, EXIT.OK, policy.stderr)
            installed = self.invoke(
                "operator", config, "bp-boundary", "add", admitted_name,
                remote_path, peer, listen_port,
                *(["fn.test", "32768", "16"] if inbound else []),
                "contact", self.relay.port,
            )
            self.assertEqual(installed.returncode, EXIT.OK, installed.stderr)
            # Spec 4.6: the node forwards held transit only to a boundary
            # the route table names; the peer is reached through the relay.
            routed = self.invoke(
                "operator", config, "bp-route", "add", peer + "*", admitted_name,
            )
            self.assertEqual(routed.returncode, EXIT.OK, routed.stderr)
        receipts = self.receiver_receipts if receiver else self.tmp / "sender-fnrj"
        workflow = self.tmp / "receiver-fnwf" if receiver else self.sender_workflow
        process = start(
            [IMAGE, "--fn", "bp-node", "serve", "-" if configured else str(listen_port),
             str(journal), str(store), str(receipts), str(workflow),
             node, peer, node, "native-policy", node,
             "127.0.0.1", str(self.relay.port),
             "1" if once else "0", "3600000", "2", "32", str(transfer_mru),
             "0", "0", *(["--control-config", str(config)] if control else [])],
            cwd=ROOT, env=environment(extra_env))
        self.addCleanup(process.stop, 5)
        if control:
            process.announcement(b"BP NODE CONTROL ", timeout=45)
        line = process.announcement(b"BP NODE LISTENING ", timeout=45)
        return process, int(line.rsplit(b" ", 1)[1])

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

    def dispatch_receiver_args(self, *, reports=False):
        return [
            str(IMAGE), "--fn",
            "bp-node", "dispatch", str(self.receiver_journal),
            str(self.receiver_store), str(self.receiver_receipts),
            str(self.tmp / "receiver-fnwf"), "dtn://receiver/",
            "dtn://sender/", "dtn://receiver/", "native-policy",
            "dtn://receiver/", "127.0.0.1", str(self.relay.port),
            "1", "3600000", "2", "32", "1048576", "0", "0",
            "1" if reports else "0",
        ]

    def dispatch_receiver(self, *, reports=False, env=None, extra_env=None):
        return run(self.dispatch_receiver_args(reports=reports), cwd=ROOT,
                   env=environment({**(env or {}), **(extra_env or {})}), timeout=120)

    def deletion_request_bundle(self):
        with Acl2Session(IMAGE) as bridge:
            adu = bridge.literal(self.request_path.read_bytes())
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            receiver = "(cons :dtn '(47 47 114 101 99 101 105 118 101 114 47))"
            form = (
                "(let* ((bundle (fn-bpn-send-bundle "
                f"(fn-bpn-config {sender} 1500 2 32 1048576) "
                f"{receiver} '{adu} 44 "
                "(fn-clock-observation 1000 0 0 nil))) "
                "(primary (fn-bpb-bundle-primary bundle)) "
                "(requested (fn-bpb-make-bundle "
                "(update-nth 1 *fn-bpp-flag-report-deletion* primary) "
                "(fn-bpb-bundle-blocks bundle) "
                "(fn-bpb-bundle-payload bundle)))) "
                "(fn-bpb-encode requested))"
            )
            path = self.tmp / "deletion-request.bundle"
            path.write_bytes(acl2_octets(bridge.call(form)))
            return path

    def send_deletion_request(self, port):
        return self.invoke(
            "tcpcl", "send", "127.0.0.1", port,
            self.deletion_request_bundle(), self.tmp / "deletion-sender-spool",
            "dtn://sender/", "dtn://receiver/", 0, 65536, 1048576, 0,
        )

    def unrouted_transit_bundle(self):
        """ACL2 authors the older wire; Python only carries its octets."""
        with Acl2Session(IMAGE) as bridge:
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            unrouted = "(cons :dtn '(47 47 117 110 114 111 117 116 101 100 47))"
            form = (
                "(fn-bpb-encode (fn-bpn-send-bundle "
                f"(fn-bpn-config {sender} 3600000 2 32 1048576) "
                f"{unrouted} '(1 2 3 4) 77 "
                "(fn-clock-observation 0 0 0 nil)))"
            )
            path = self.tmp / "unrouted-transit.bundle"
            path.write_bytes(acl2_octets(bridge.call(form)))
            return path

    def test_older_unrouted_transit_does_not_block_younger_local_request(self):
        receiver, port = self.start_node(True, once=False)
        transit = self.unrouted_transit_bundle()
        sent_old = self.invoke(
            "tcpcl", "send", "127.0.0.1", port, transit,
            self.tmp / "unrouted-sender-spool", "dtn://sender/",
            "dtn://receiver/", 0, 65536, 1048576, 0,
        )
        self.assertEqual(sent_old.returncode, EXIT.OK, sent_old.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)

        sent_new = self.send_request(port, "after-unrouted-transit")
        self.assertEqual(sent_new.returncode, EXIT.OK, sent_new.stderr)
        delivered = self.wait_for_output(
            receiver, b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", delivered)
        receiver.stop(grace=5)

        self.assertEqual(self.receiver_articles(), 1)
        payloads = self.acl2_lifecycle_payloads(self.receiver_journal, 5)
        self.assertIn(bytes((1, 2, 3, 4)), payloads)
        self.assertIn(self.request_path.read_bytes(), payloads)
        self.assertEqual(len(payloads), 2)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP FNBS recovered held=2", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 1)

    def conflicting_transit_bundle(self):
        """The unrouted transit identity (creation 0, sequence 77) with another
        payload: same bundle ID, different immutable projection.  ACL2 authors
        the wire."""
        with Acl2Session(IMAGE) as bridge:
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            unrouted = "(cons :dtn '(47 47 117 110 114 111 117 116 101 100 47))"
            form = (
                "(fn-bpb-encode (fn-bpn-send-bundle "
                f"(fn-bpn-config {sender} 3600000 2 32 1048576) "
                f"{unrouted} '(9 9 9 9) 77 "
                "(fn-clock-observation 0 0 0 nil)))"
            )
            path = self.tmp / "conflicting-transit.bundle"
            path.write_bytes(acl2_octets(bridge.call(form)))
            return path

    @staticmethod
    def conflict_records(journal):
        """The lifecycle frames ACL2's kind-14 decoder opens, decoded."""
        with Acl2Session(IMAGE) as bridge:
            rows = []
            for frame in sorted((journal / "lifecycle").glob("*.fnb")):
                octets = "'" + bridge.literal(frame.read_bytes())
                row = bridge.call(f"(fn-bpnf-conflict-unframe {octets})")
                if row.lstrip().upper().startswith(b"(:BPNF-CONFLICT "):
                    rows.append((frame.name, row))
            return rows

    def send_transit(self, port, path, spool):
        return self.invoke(
            "tcpcl", "send", "127.0.0.1", port, path, self.tmp / spool,
            "dtn://sender/", "dtn://receiver/", 0, 65536, 1048576, 0,
        )

    def rotate_receiver(self, stop=None, observer=None):
        """`bp-node checkpoint` on the stopped receiver; with STOP, the
        developer cut stops it at that point of the publication program and
        the test kills it there with SIGKILL."""
        argv = [IMAGE, "--fn", "bp-node", "checkpoint", self.receiver_journal,
                "dtn://receiver/"]
        if not stop:
            done = run(argv, cwd=ROOT, timeout=120)
            return done.returncode, done.stdout, done.stderr
        process = start(argv, cwd=ROOT, env=environment({"FN_BP_ROTATION_TEST_STOP": stop}))
        self.addCleanup(process.stop, 5)
        seen = process.output_until(b"BP journal rotation stopped at=" + stop.encode(),
                                    timeout=120)
        process.kill()
        process.wait(timeout=15)
        process.finish()
        if observer is not None:
            observer(exit_code=process.returncode, held_stdout=seen,
                     selector="FN_BP_ROTATION_TEST_STOP", value=stop)
        return None, seen, b""

    def recovered_held(self):
        """Reopen through the node's own recovery and return its held count."""
        reopened = self.dispatch_receiver()
        self.assertEqual(reopened.returncode, EXIT.OK, reopened.stderr)
        for line in reopened.stdout.splitlines():
            if line.startswith(b"BP FNBS recovered held="):
                return int(line.split(b"=", 1)[1])
        self.fail(reopened.stdout)

    def test_rotation_killed_at_each_cut_keeps_held_rows(self):
        """N16 on the image: the journal rotates to a new generation through
        `bp-node checkpoint`.  A kill after the generation directory, after
        the staged selection, or after the rename leaves one recovery
        authority (the old selection before the rename, either after it);
        every reopen recovers the held row.  A completed rotation starts a
        generation with no records; new work lands there, arrival order kept,
        and a second rotation carries both rows.  Retirement (PKT-059): a
        kill after the second step of the removal program leaves a partly
        removed old generation and the same recovery; the next rotation
        removes every older generation directory and the killed rotation's
        stray staged selection, keeping only the selected generation."""
        receiver, port = self.start_node(True, once=False)
        sent = self.send_transit(port, self.unrouted_transit_bundle(), "r1")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)
        receiver.stop(grace=5)
        journal = self.receiver_journal
        old_records = sorted(p.name for p in (journal / "lifecycle").glob("*.fnb"))
        self.assertTrue(old_records)
        self.assertEqual(self.recovered_held(), 1)
        selection = journal / "bp-generation.fnb"
        for cut in ("directory", "stage"):
            self.rotate_receiver(cut)
            self.assertFalse(selection.exists(), cut)
            self.assertEqual(self.recovered_held(), 1, cut)
        self.rotate_receiver("replace")
        self.assertTrue(selection.exists())
        self.assertEqual(self.recovered_held(), 1)
        generations = sorted(p.name for p in journal.glob("lifecycle-g*"))
        # Unselected stagings are never reused: three distinct numbers.
        self.assertEqual(len(generations), 3, generations)
        selected = journal / generations[-1]
        self.assertEqual(sorted(p.name for p in selected.glob("*.fnb")), [])
        # The rename cut killed the program before retirement: the old
        # generation and the killed "stage" cut's staged file are still there.
        self.assertEqual(
            sorted(p.name for p in (journal / "lifecycle").glob("*.fnb")),
            old_records)
        self.assertTrue(list(journal.glob(".bp-generation-*")))
        # Killed inside the retirement program (after its second step, a
        # partly emptied "lifecycle"): recovery is unchanged.
        self.rotate_receiver("retire-2")
        self.assertEqual(self.recovered_held(), 1)
        # A clean rotation from the selected generation finishes the
        # retirement first, then retires generation 3 after selecting 4.
        code, out, err = self.rotate_receiver()
        self.assertEqual(code, EXIT.OK, (out, err))
        self.assertIn(b"BP journal generation selected generation=4", out)
        self.assertIn(b"BP journal generation retired name=lifecycle", out)
        self.assertEqual(self.recovered_held(), 1)
        self.assertFalse((journal / "lifecycle").exists())
        self.assertEqual(sorted(p.name for p in journal.glob("lifecycle-g*")),
                         ["lifecycle-g00000000000000000004"])
        self.assertEqual(list(journal.glob(".bp-generation-*")), [])
        # New work lands in the new generation, after the checkpointed row.
        current = journal / "lifecycle-g00000000000000000004"
        receiver, port = self.start_node(True, once=False)
        second = self.send_transit(port, self.conflicting_transit_bundle_free(), "r2")
        self.assertEqual(second.returncode, EXIT.OK, second.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)
        receiver.stop(grace=5)
        self.assertTrue(list(current.glob("*.fnb")))
        self.assertEqual(self.recovered_held(), 2)
        code, out, err = self.rotate_receiver()
        self.assertEqual(code, EXIT.OK, (out, err))
        self.assertEqual(self.recovered_held(), 2)
        self.assertEqual(sorted(p.name for p in journal.glob("lifecycle-g*")),
                         ["lifecycle-g00000000000000000005"])

    def conflicting_transit_bundle_free(self):
        """A second unrouted transit with its own identity."""
        with Acl2Session(IMAGE) as bridge:
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            unrouted = "(cons :dtn '(47 47 117 110 114 111 117 116 101 100 47))"
            form = (
                "(fn-bpb-encode (fn-bpn-send-bundle "
                f"(fn-bpn-config {sender} 3600000 2 32 1048576) "
                f"{unrouted} '(5 6 7 8) 78 "
                "(fn-clock-observation 0 0 0 nil)))"
            )
            path = self.tmp / "unrouted-transit-2.bundle"
            path.write_bytes(acl2_octets(bridge.call(form)))
            return path

    def test_identity_conflict_is_refused_recorded_and_replayed(self):
        """N11 on the image: a second reception whose identity names a held
        bundle with another payload is refused :identity-conflict, a durable
        kind-14 record names it, the node keeps answering, and replay
        accepts the record."""
        receiver, port = self.start_node(True, once=False)
        first = self.send_transit(port, self.unrouted_transit_bundle(), "s1")
        self.assertEqual(first.returncode, EXIT.OK, first.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)

        conflicting = self.conflicting_transit_bundle()
        refused = self.send_transit(port, conflicting, "s2")
        out = self.wait_for_output(receiver, b"reason=identity-conflict", timeout=60)
        self.assertIn(b"BP refused xfer=", out)
        self.assertEqual(refused.returncode, EXIT.REFUSED, (refused.stdout, refused.stderr, out))
        # The same conflict again: refused again, never :busy.
        again = self.send_transit(port, conflicting, "s3")
        self.assertEqual(again.returncode, EXIT.REFUSED, again.stderr)
        out = self.wait_for_output(receiver, b"reason=identity-conflict", timeout=60)
        self.assertNotIn(b"reason=busy", out)

        # The node keeps answering: a fresh request is delivered.
        sent = self.send_request(port, "after-identity-conflict")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        delivered = self.wait_for_output(
            receiver, b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", delivered)
        receiver.stop(grace=5)

        records = self.conflict_records(self.receiver_journal)
        self.assertEqual(len(records), 2, records)
        payloads = self.acl2_lifecycle_payloads(self.receiver_journal, 5)
        self.assertIn(bytes((1, 2, 3, 4)), payloads)
        self.assertNotIn(bytes((9, 9, 9, 9)), payloads)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP FNBS recovered held=2", restarted.stdout)
        self.assertEqual(self.conflict_records(self.receiver_journal), records)

    # The operator's owner-backoff row (JOURNAL/bp-node-budgets, spec
    # bp-node-machine 2.1; ACL2 validates it in fn-bpnp-configured-budgets)
    # set short, so a busy test waits half a second, not the 5000 ms default
    # (PKT-445 (b): three 5.5 s sleeps made this module the over-budget one).
    BACKOFF_MS = 500

    def configure_backoff(self):
        self.receiver_journal.mkdir(parents=True, exist_ok=True)
        (self.receiver_journal / "bp-node-budgets").write_text(
            "owner-backoff %d\n" % self.BACKOFF_MS, encoding="ascii")

    @staticmethod
    def boottime_ms():
        # host/native/bp.lisp fnn-bp-monotonic-now reads CLOCK_BOOTTIME.
        return time.clock_gettime_ns(time.CLOCK_BOOTTIME) // 1000000

    def wait_past_deferral(self, captured):
        """Wait until the node's own monotonic clock passes the `after='
        reading of the last deferral, and check that reading is the
        configured backoff from now, not the default."""
        after = int(re.findall(rb"deferred busy=[0-9]+ after=([0-9]+)", captured)[-1])
        self.assertLessEqual(after - self.boottime_ms(), self.BACKOFF_MS)
        while self.boottime_ms() <= after + 50:
            time.sleep(0.05)

    def test_busy_application_defers_and_redelivers_after_backoff(self):
        """BP-R17 on the image: the owner answers the first delivery :busy.
        The node neither refuses nor fences: the row stays held, and the
        first dispatch after the configured backoff delivers it."""
        self.configure_backoff()
        receiver, port = self.start_node(
            True, once=False, extra_env={"FN_BP_NODE_TEST_APP_BUSY": "1"})
        sent = self.send_request(port, "busy-request")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        out = self.wait_for_output(
            receiver, b"BP node delivery deferred busy=1", timeout=120)
        self.assertNotIn(b"request-refused", out)
        self.assertNotIn(b"application uncertain", out)
        self.assertNotIn(b"application result is uncertain", out)
        self.wait_past_deferral(out)
        # Any later connection runs the dispatch loop; an unrouted transit
        # consumes no application answer.
        self.send_transit(port, self.unrouted_transit_bundle(), "busy-ping")
        delivered = self.wait_for_output(
            receiver, b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", delivered)
        self.assertNotIn(b"request-refused", delivered)
        receiver.stop(grace=5)
        self.assertEqual(self.receiver_articles(), 1)

    def test_permanently_busy_application_strands_row_until_resume(self):
        """BP-R17 at the retry budget: three :busy answers strand the row,
        visibly and still held; nothing is refused or stored.  The count is
        durable (kind 20): a restart keeps it at 3 and reports the strand
        again on every pass, never redelivering; `bp-node resume' writes
        count 0 and the next pass delivers."""
        self.configure_backoff()
        receiver, port = self.start_node(
            True, once=False, extra_env={"FN_BP_NODE_TEST_APP_BUSY": "100"})
        sent = self.send_request(port, "stranded-request")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        seen = self.wait_for_output(
            receiver, b"BP node delivery deferred busy=1", timeout=120)
        transit = self.unrouted_transit_bundle()
        for spool, marker in (("p1", b"BP node delivery deferred busy=2"),
                              ("p2", b"BP node delivery stranded busy=3")):
            self.wait_past_deferral(seen)
            self.send_transit(port, transit, spool)
            seen += self.wait_for_output(receiver, marker, timeout=120)
        # A stranded row is not offered again: a later pass, one backoff
        # past the stranding, only reports it.
        time.sleep(self.BACKOFF_MS / 1000 + 0.2)
        self.send_transit(port, transit, "p3")
        time.sleep(2)
        receiver.stop(grace=15)
        seen += receiver.output_since_cursor()
        self.assertNotIn(b"busy=4", seen)
        self.assertNotIn(b"request-refused", seen)
        self.assertNotIn(b"request-accepted", seen)
        self.assertEqual(self.receiver_articles(), 0)
        # Restart twice: the durable count is what it was and the report repeats.
        arrivals = set()
        for _ in range(2):
            restarted = self.dispatch_receiver()
            self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
            self.assertNotIn(b"request-accepted", restarted.stdout)
            self.assertNotIn(b"delivery deferred", restarted.stdout)
            line = [x for x in restarted.stdout.splitlines()
                    if x.startswith(b"BP node delivery stranded busy=3 arrival=")]
            self.assertEqual(len(line), 1, restarted.stdout)
            arrivals.add(int(line[0].split(b"arrival=")[1].split()[0]))
            self.assertEqual(self.receiver_articles(), 0)
        self.assertEqual(len(arrivals), 1, arrivals)
        arrival = arrivals.pop()
        resumed = self.resume_receiver(arrival)
        self.assertEqual(resumed.returncode, EXIT.OK, resumed.stdout + resumed.stderr)
        self.assertIn(b"BP node delivery resumed", resumed.stdout)
        delivered = self.dispatch_receiver()
        self.assertEqual(delivered.returncode, EXIT.OK, delivered.stderr)
        self.assertIn(b"BP node delivery request-accepted", delivered.stdout)
        self.assertEqual(self.receiver_articles(), 1)

    def other_boot_domain_frame(self):
        """ACL2's clock-domain frame for a boot ID that is not this boot's."""
        boot = Path("/proc/sys/kernel/random/boot_id").read_text("ascii").strip()
        other = boot[:-1] + ("0" if boot[-1] != "0" else "1")
        with Acl2Session(IMAGE) as bridge:
            octets = " ".join(str(b) for b in other.encode("ascii"))
            return acl2_octets(bridge.call(f"(fn-bpcd-frame '({octets}))"))

    def test_restart_in_another_boot_fences_and_keeps_rows(self):
        """N07 on the image: the durable boot domain names another boot, so
        recovery through fn-bpnp-step answers (:restart-fault :clock-domain
        :different-boot) and no held row changes; the true domain restored,
        the same journal recovers."""
        receiver, port = self.start_node(True, once=False)
        first = self.send_transit(port, self.unrouted_transit_bundle(), "s1")
        self.assertEqual(first.returncode, EXIT.OK, first.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)
        receiver.stop(grace=5)

        domain = self.receiver_journal / "clock-domain.fnb"
        saved = domain.read_bytes()
        lifecycle = self.receiver_journal / "lifecycle"
        before = tuple((p.name, p.read_bytes()) for p in sorted(lifecycle.iterdir()))
        domain.write_bytes(self.other_boot_domain_frame())

        fenced = self.dispatch_receiver()
        self.assertEqual(fenced.returncode, EXIT.UNCERTAIN, fenced.stderr)
        self.assertIn(b"restart fenced: clock domain different-boot", fenced.stderr)
        self.assertEqual(
            tuple((p.name, p.read_bytes()) for p in sorted(lifecycle.iterdir())),
            before)

        domain.write_bytes(saved)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP FNBS recovered held=1", restarted.stdout)

    def forward_mru_bundles(self):
        """ACL2 authors the two transit wires; Python only carries octets."""
        with Acl2Session(IMAGE) as bridge:
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            paths = []
            for label, size, octet, serial, no_fragment in (
                ("older", 49152, 65, 77, True),
                ("younger", 8192, 66, 78, False),
            ):
                bundle = (
                    "(fn-bpn-send-bundle "
                    f"(fn-bpn-config {sender} 3600000 2 32 1048576) "
                    f"{sender} (make-list {size} :initial-element {octet}) "
                    f"{serial} (fn-clock-observation 0 0 0 nil))"
                )
                if no_fragment:
                    bundle = (
                        f"(let ((bundle {bundle})) "
                        "(fn-bpb-make-bundle "
                        "(update-nth 1 *fn-bpp-flag-no-fragment* "
                        "(fn-bpb-bundle-primary bundle)) "
                        "(fn-bpb-bundle-blocks bundle) "
                        "(fn-bpb-bundle-payload bundle)))"
                    )
                wire = acl2_octets(
                    bridge.call(f"(fn-bpb-encode {bundle})"))
                path = self.tmp / f"forward-{label}.bundle"
                path.write_bytes(wire)
                paths.append(path)
            self.assertGreater(paths[0].stat().st_size, 32768)
            self.assertLess(paths[1].stat().st_size, 32768)
            return paths

    def test_older_mru_wait_allows_younger_forward_and_replays(self):
        receiver, port = self.start_node(True, once=False)
        older, younger = self.forward_mru_bundles()
        for label, path in (("older", older), ("younger", younger)):
            sent = self.invoke(
                "tcpcl", "send", "127.0.0.1", port, path,
                self.tmp / f"forward-{label}-sender-spool", "dtn://sender/",
                "dtn://receiver/", 0, 65536, 1048576, 0,
            )
            if sent.returncode != EXIT.OK:
                # The sender's code alone does not name the refusal; the
                # receiving node's own line does.
                self.fail((label, sent.returncode, sent.stderr, sent.stdout,
                           receiver.output_since_cursor(),
                           receiver.stderr.since(0)))
        receiver.stop(grace=5)
        # The serving node's progress step may already dispatch a routed
        # transit carrier (kind 6 `:forward', specs/bp-node-machine.md §4.2,
        # "the routed transit arm may install a :pending :dispatch"), so the
        # receive phase leaves both kind-5 receives and zero to two kind-6
        # dispatches, and nothing else, depending on how many progress
        # events ran before the stop.
        before_forward = self.acl2_lifecycle_kinds(self.receiver_journal)
        self.assertEqual(before_forward[5], 2, before_forward)
        self.assertLessEqual(before_forward[6], 2, before_forward)
        self.assertEqual(sum(before_forward.values()),
                         before_forward[5] + before_forward[6], before_forward)

        peer, peer_port = self.start_node(False, once=False)
        self.relay.route(peer_port)
        args = self.dispatch_receiver_args()
        args[-4] = "32768"  # Negotiated outbound transfer MRU.
        dispatched = run(args, cwd=ROOT, timeout=240)
        self.assertEqual(dispatched.returncode, EXIT.OK, dispatched.stderr)
        self.assertIn(b"BP forwarding attempt durable", dispatched.stdout)
        self.assertIn(b"BP forwarding result durable", dispatched.stdout)
        # Both carriers dispatched (two kind-6 in all), and the younger one
        # alone attempted (kind 8) and settled (kind 9): the older one's image
        # exceeds the 32 KiB session MRU and waits (N04).
        after_forward = self.acl2_lifecycle_kinds(self.receiver_journal)
        self.assertEqual(after_forward, collections.Counter({5: 2, 6: 2, 8: 1, 9: 1}))
        forwarded_names = sorted(
            p.name for p in (self.receiver_journal / "lifecycle").glob("*.fnb"))

        peer.stop(grace=5)
        self.relay.route(None)
        replayed = run(args, cwd=ROOT, timeout=120)
        self.assertEqual(replayed.returncode, EXIT.OK, replayed.stderr)
        self.assertIn(b"BP FNBS recovered held=2", replayed.stdout)
        self.assertNotIn(b"BP forwarding attempt durable", replayed.stdout)
        self.assertEqual(
            sorted(p.name for p in (self.receiver_journal / "lifecycle").glob("*.fnb")),
            forwarded_names)
        self.assertEqual(self.acl2_lifecycle_kinds(self.receiver_journal), after_forward)

    def test_removed_route_keeps_transit_held_and_reports_no_route(self):
        """Spec 4.6: no route, no session; the row and its obligation stay held.

        The receiver holds one transit bundle for dtn://sender/.  With the
        route removed, dispatch opens no session to the reachable peer and
        reports ACL2's :no-route; no kind 8 is written.  With the route
        added back, the same row is forwarded and settles as sent.
        """
        receiver, port = self.start_node(True, once=False)
        _, younger = self.forward_mru_bundles()
        sent = self.invoke(
            "tcpcl", "send", "127.0.0.1", port, younger,
            self.tmp / "noroute-sender-spool", "dtn://sender/",
            "dtn://receiver/", 0, 65536, 1048576, 0,
        )
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        receiver.stop(grace=5)
        config = self.tmp / "receiver-fn.toml"
        removed = self.invoke("operator", config, "bp-route", "remove",
                              "dtn://sender/*", "sender-boundary")
        self.assertEqual(removed.returncode, EXIT.OK, removed.stderr)
        peer, peer_port = self.start_node(False, once=False)
        self.relay.route(peer_port)
        args = self.dispatch_receiver_args()
        held = run(args, cwd=ROOT, timeout=240)
        self.assertEqual(held.returncode, EXIT.OK, held.stderr)
        self.assertIn(b"BP forwarding no-route destination=dtn://sender/ "
                      b"decision=no-route", held.stdout)
        self.assertNotIn(b"BP forwarding attempt durable", held.stdout)
        kinds = self.acl2_lifecycle_kinds(self.receiver_journal)
        self.assertEqual(kinds[5], 1, kinds)
        self.assertEqual(kinds[8], 0, kinds)

        added = self.invoke("operator", config, "bp-route", "add",
                            "dtn://sender/*", "sender-boundary")
        self.assertEqual(added.returncode, EXIT.OK, added.stderr)
        routed = run(args, cwd=ROOT, timeout=240)
        self.assertEqual(routed.returncode, EXIT.OK, routed.stderr)
        self.assertIn(b"BP forwarding route hop=sender-boundary", routed.stdout)
        self.assertIn(b"BP forwarding attempt durable", routed.stdout)
        self.assertIn(b"status=sent", routed.stdout)
        peer.stop(grace=5)

    @staticmethod
    def acl2_lifecycle_kinds(journal):
        """Count the journal's lifecycle frames by the ACL2 decoder that opens each.

        Each kind's own unframe function accepts only its frame version and
        kind, so a frame counts as kind 6 only when it is a dispatch record.
        A frame no decoder here opens counts as 0.
        """
        with Acl2Session(IMAGE) as bridge:
            kinds = collections.Counter()
            for frame in sorted((journal / "lifecycle").glob("*.fnb")):
                octets = "'" + bridge.literal(frame.read_bytes())
                kinds[acl2_nat(bridge.call(
                    f"(cond ((fn-bpnf-stored-record-unframe {octets}) 5) "
                    f"((fn-bpnp-dispatch-unframe {octets}) 6) "
                    f"((fn-bpnp-attempt-unframe {octets}) 8) "
                    f"((fn-bpnp-result-unframe {octets}) 9) (t 0))"))] += 1
            return kinds

    def test_death_after_kind_eight_retries_once_and_peer_holds_one_copy(self):
        """N08 on the image: death after a durable kind 8 whose transfer ran.

        The retry policy of spec 4.3.1 (default adopted 2026-09-24, pending
        ember): recovery re-offers the same held bundle on the next session;
        the peer's bundle-id admission absorbs the duplicate; the sender
        records one kind-9 result.  Needs a developer image with the
        FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT selector; the class skips
        without an image.
        """
        receiver, port = self.start_node(True, once=False)
        _, younger = self.forward_mru_bundles()
        sent = self.invoke(
            "tcpcl", "send", "127.0.0.1", port, younger,
            self.tmp / "retry-sender-spool", "dtn://sender/",
            "dtn://receiver/", 0, 65536, 1048576, 0,
        )
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        receiver.stop(grace=5)
        payload = self.acl2_lifecycle_payloads(self.receiver_journal, 5)[-1]

        peer, peer_port = self.start_node(False, once=False)
        self.relay.route(peer_port)
        args = self.dispatch_receiver_args()
        cut = start(args, cwd=ROOT, env=environment(
            {"FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT": "1"}))
        self.addCleanup(cut.stop, 5)
        self.wait_for_output(cut, b"BP NODE KIND8 SENT", timeout=240)
        cut.kill()
        cut.wait(timeout=15)
        journal = self.receiver_journal / "lifecycle"
        after_cut = len(tuple(journal.glob("*.fnb")))
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.sender_journal, 5).count(payload), 1)

        retried = run(args, cwd=ROOT, timeout=240)
        self.assertEqual(retried.returncode, EXIT.OK, retried.stderr)
        self.assertIn(b"BP FNBS recovered", retried.stdout)
        self.assertIn(b"BP forwarding attempt durable", retried.stdout)
        self.assertIn(b"BP forwarding result durable", retried.stdout)
        self.assertIn(b"status=sent", retried.stdout)
        self.assertNotIn(b"BP forwarding stranded", retried.stdout)
        # The retry's kind 8 and its kind 9; the peer still holds one copy.
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), after_cut + 2)
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.sender_journal, 5).count(payload), 1)

        settled = run(args, cwd=ROOT, timeout=120)
        self.assertEqual(settled.returncode, EXIT.OK, settled.stderr)
        self.assertNotIn(b"BP forwarding attempt durable", settled.stdout)
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), after_cut + 2)

    def resume_receiver(self, arrival):
        return self.invoke(
            "bp-node", "resume", self.receiver_journal, "dtn://receiver/",
            arrival,
        )

    def test_uncertain_transfer_is_connection_local_and_resume_rearms(self):
        """Spec 4.3.1: an uncertain transfer costs that connection only.

        The relay severs every forwarding connection after 200 client octets,
        mid-transfer, after the sender's kind 8 is durable.  ACL2 reads the
        transfer as :uncertain; its kind 9 keeps the attempt's count and the
        node keeps serving: the same process accepts another inbound transfer
        and re-offers the row (retry 1, no restart).  Two more cut sessions
        (retries 2 and 3) strand it; `bp-node resume' re-arms it with a
        durable :resumed kind 9; the next session offers the same bundle and
        the peer holds exactly one copy.
        """
        peer, peer_port = self.start_node(False, once=False)
        self.relay.route(peer_port, cut_after=200)
        receiver, port = self.start_node(True, once=False)
        _, younger = self.forward_mru_bundles()

        def send_younger(spool):
            return self.invoke(
                "tcpcl", "send", "127.0.0.1", port, younger,
                self.tmp / spool, "dtn://sender/", "dtn://receiver/",
                0, 65536, 1048576, 0,
            )

        self.assertEqual(send_younger("u-spool-1").returncode, EXIT.OK)
        first = self.wait_for_output(
            receiver, b"BP forwarding result durable", timeout=120)
        self.assertIn(b"BP forwarding attempt durable", first)
        self.assertIn(b"BP forwarding transfer uncertain", first)
        self.assertIn(b"status=uncertain", first)
        self.assertIsNone(receiver.poll(), "node stopped after a connection fault")
        # The same process serves again, and re-offers the row in-process.
        self.assertEqual(send_younger("u-spool-2").returncode, EXIT.OK)
        second = self.wait_for_output(
            receiver, b"BP forwarding result durable", timeout=120)
        self.assertIn(b"BP forwarding attempt durable", second)
        self.assertIn(b"status=uncertain", second)
        self.assertIsNone(receiver.poll())
        receiver.stop(grace=5)

        args = self.dispatch_receiver_args()
        for _ in range(2):
            cut = run(args, cwd=ROOT, timeout=240)
            self.assertEqual(cut.returncode, EXIT.OK, cut.stdout + cut.stderr)
            self.assertIn(b"status=uncertain", cut.stdout)
        stranded = run(args, cwd=ROOT, timeout=240)
        self.assertEqual(stranded.returncode, EXIT.OK, stranded.stderr)
        self.assertNotIn(b"BP forwarding attempt durable", stranded.stdout)
        line = [x for x in stranded.stdout.splitlines()
                if x.startswith(b"BP forwarding stranded")]
        self.assertEqual(len(line), 1, stranded.stdout)
        self.assertIn(b"retries=3", line[0])
        arrival = int(line[0].split(b"arrival=")[1].split()[0])

        # Refusals carry ACL2's reason and write nothing.
        journal = self.receiver_journal / "lifecycle"
        before = len(tuple(journal.glob("*.fnb")))
        unknown = self.resume_receiver(arrival + 99)
        self.assertEqual(unknown.returncode, EXIT.REFUSED, unknown.stdout + unknown.stderr)
        self.assertIn(b"resume refused", unknown.stdout)
        self.assertIn(b"reason=no-row", unknown.stdout)
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), before)

        resumed = self.resume_receiver(arrival)
        self.assertEqual(resumed.returncode, EXIT.OK, resumed.stdout + resumed.stderr)
        self.assertIn(b"status=resumed", resumed.stdout)
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), before + 1)
        again = self.resume_receiver(arrival)
        self.assertEqual(again.returncode, EXIT.REFUSED, again.stdout)
        self.assertIn(b"reason=not-attempted", again.stdout)

        self.relay.route(peer_port)
        offered = run(args, cwd=ROOT, timeout=240)
        self.assertEqual(offered.returncode, EXIT.OK, offered.stderr)
        self.assertIn(b"BP forwarding attempt durable", offered.stdout)
        self.assertIn(b"status=sent", offered.stdout)
        peer.stop(grace=5)
        payload = self.acl2_lifecycle_payloads(self.receiver_journal, 5)[-1]
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.sender_journal, 5).count(payload), 1)

    @staticmethod
    def acl2_lifecycle_payloads(journal, kind):
        """Ask the ACL2 frame decoders for exact durable report payloads."""
        decoder = {
            5: "fn-bpnf-stored-record-unframe",
            10: "fn-bpnf-delete-unframe",
        }[kind]
        with Acl2Session(IMAGE) as bridge:
            payloads = []
            for frame in sorted((journal / "lifecycle").glob("*.fnb")):
                octets = bridge.literal(frame.read_bytes())
                if kind == 10:
                    form = (
                        f"(let ((record ({decoder} '{octets}))) "
                        "(and record (fn-bpn-nth 6 record)))"
                    )
                else:
                    form = (
                        f"(let ((record ({decoder} '{octets}))) "
                        "(and record (fn-bpb-payload "
                        "(fn-bpnf-held-bundle (fn-bpn-nth 3 record)))))"
                    )
                payload = acl2_octets(bridge.call(form))
                if payload:
                    payloads.append(payload)
            return payloads

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

    def receiver_articles(self):
        """The receiver Store's article count, from the node's own read-only
        open (`store PATH status`, books/native-live-status.lisp
        fn-nls-report's `articles=' word): it replays the record log
        the way the served path does.  The Python Store (tools/run_store.py)
        reads another layout and is not this Store's readback."""
        # Row S3: a stopped store's `status' is its checkpoint header;
        # `--replay' (the operator verb's decision, fn-omr-store-status-word)
        # asks for the report over the replayed log, whose counts these are.
        status = self.invoke("store", self.receiver_store, "status", "--replay", timeout=300)
        self.assertEqual(status.returncode, EXIT.OK, (status.stdout, status.stderr))
        counts = re.findall(rb"^transactions=[0-9]+ articles=([0-9]+) ",
                            status.stdout, re.MULTILINE)
        self.assertEqual(len(counts), 1, status.stdout)
        return int(counts[0])

    def receiver_article(self, msgid):
        """The stored octets of MSGID, from the node's lookup
        (`store PATH inspect MSGID`)."""
        inspected = self.invoke("store", self.receiver_store, "inspect",
                                msgid.decode("ascii"), timeout=300)
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr[-4000:])
        return inspected.stdout

    def receiver_listgroups(self, *groups):
        """GROUP replies of the receiver's Store, read through a reader port
        of `operator run' (ACL2's served GROUP) on READER_IMAGE, one line
        per group."""
        reader = Node(self, READER_IMAGE, root=self.tmp / "receiver-reader")
        reader.store_path = self.receiver_store
        reader.write_config()
        reader.start(timeout=60)
        with reader.session(timeout=30, greeting=(b"200",)) as client:
            replies = [client.command("GROUP " + group) for group in groups]
        reader.stop(expect=None, grace=5)
        return replies

    def test_control_article_through_bp_transit_is_filed_not_executed(self):
        """PKT-070 (control-c1 finding 5).  A control article carried in a BP
        request reaches the receiver's Store through the same
        fnn-owner-attempt-transit step as NNTP transit, whose first call is
        ACL2's fn-pa-filing-plan: it is filed in control.cancel, never in
        the fn.test its Newsgroups names, and the article it names to cancel
        is not touched (nothing is executed)."""
        config = self.tmp / "receiver-fn.toml"
        config.write_text(f'[store]\npath = "{self.receiver_store}"\n',
                          encoding="ascii")
        created = self.invoke("operator", config, "group", "create",
                              "control.cancel")
        self.assertEqual(created.returncode, EXIT.OK, created.stderr)
        self.msgid = b"<bp-node-control@example.invalid>"
        self.article = (
            b"Path: sender.bp.gate.invalid!not-for-mail\r\n"
            b"From: sender@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: cancel through BP\r\n"
            b"Control: cancel <bp-node-a3@example.invalid>\r\n"
            b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
            b"Message-ID: " + self.msgid + b"\r\n"
            b"\r\ncontrol body\r\n"
        )
        self.author_request()
        receiver, port = self.start_node(True)
        sent = self.send_request(port, "control-transit")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(receiver.returncode, EXIT.OK, err)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertIn(b"BP node delivery request-accepted", out)
        control, fn_test = self.receiver_listgroups("control.cancel", "fn.test")
        # Filed once in control.cancel; never in fn.test (its Newsgroups).
        self.assertTrue(control.startswith(b"211 1 "), control)
        self.assertTrue(fn_test.startswith(b"211 0 "), fn_test)
        self.assertEqual(self.receiver_articles(), 1)

    def test_request_above_peer_mru_is_fragmented_and_reassembled(self):
        """PKT-061: a bundle longer than the peer's Transfer MRU is cut.

        The receiver serves with a Transfer MRU below the request's bundle.
        The sender's `bp-service run` asks ACL2's fn-bpfs-plan after
        SESS_INIT and sends RFC 9171 5.8 fragments, each at most that MRU
        (fn-bpfs-plan-fragments-fit-mru), one session each.  The receiver
        holds each fragment, publishes the family once the ADU is complete,
        and hands the reassembled request to the application once.
        """
        size = self.request_path.stat().st_size
        mru = 160 + size // 3
        receiver, port = self.start_node(True, once=False, transfer_mru=mru)
        sent = self.send_request(port, "fragmented")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stdout + sent.stderr)
        self.assertIn(b"BP fragmenting length=", sent.stdout)
        planned = [line for line in sent.stdout.splitlines()
                   if line.startswith(b"BP fragmenting")][0]
        self.assertIn(b"peer-mru=%d " % mru, planned + b" ")
        pieces = int(planned.rsplit(b"fragments=", 1)[1])
        self.assertGreater(pieces, 1)
        for index in range(2, pieces + 1):
            self.assertIn(b"BP fragment %d transfer accepted" % index, sent.stdout)
        out = self.wait_for_output(
            receiver, b"BP application handoff durable", timeout=120)
        receiver.stop(grace=5)
        self.assertIn(b"BP fragment family durable", out)
        self.assertEqual(self.receiver_articles(), 1)

    def test_request_retry_queues_distinct_receipt_carriers_and_releases_pin(self):
        before = self.sender_status()
        self.assertEqual(before.returncode, EXIT.OK, before.stderr)
        self.assertIn(b"pinned=yes", before.stdout)

        first, port = self.start_node(True)
        sent = self.send_request(port, "carrier-one")
        out, err = first.communicate(timeout=120)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertEqual(first.returncode, EXIT.OK, err)
        self.assertIn(b"BP application handoff durable", out)
        self.assertIn(b"BP node receipt queued", out)
        first_count = len(tuple((self.receiver_journal / "lifecycle").glob("*.fnb")))

        second, port = self.start_node(True)
        retry = self.send_request(port, "carrier-two")
        out, err = second.communicate(timeout=120)
        self.assertEqual(retry.returncode, EXIT.OK, retry.stderr)
        self.assertEqual(second.returncode, EXIT.OK, err)
        self.assertIn(b"BP node receipt queued", out)
        self.assertGreater(
            len(tuple((self.receiver_journal / "lifecycle").glob("*.fnb"))),
            first_count,
        )
        self.assertEqual(self.receiver_articles(), 1,
                         "the second carrier must not accept a second article")
        relayed = self.receiver_article(self.msgid)
        self.assertNotEqual(relayed, self.article)
        self.assertIn(b"Path: receiver.bp.gate.invalid", relayed)
        self.assertNotIn(b"Xref:", relayed)

        sender, port = self.start_node(False, once=False)
        self.relay.route(port)
        delivered = self.tick_receiver()
        self.assertEqual(delivered.returncode, EXIT.OK, delivered.stderr)
        self.assertIn(b"BP contact open", delivered.stdout)
        self.wait_for_output(
            sender, b"BP node delivery receipt-accepted", timeout=120)
        sender.stop(grace=5)
        after = self.sender_status()
        self.assertEqual(after.returncode, EXIT.OK, after.stderr)
        self.assertIn(b"pinned=no", after.stdout)
        unrelated = self.unrelated_status()
        self.assertEqual(unrelated.returncode, EXIT.OK, unrelated.stderr)
        self.assertIn(b"pinned=yes", unrelated.stdout)

    def test_disconnected_delivery_restarts_and_releases_only_matching_obligation(self):
        """One real POST survives application, job and checkpoint death cuts.

        The source owner has already stopped after the durable NNTP POST in
        setUp. A transport result cannot release either sender obligation.
        """
        observer = getattr(self, "resilience_observer", None)

        def observe(event, **values):
            if observer is not None:
                observer(event, **values)

        pinned = self.sender_status()
        self.assertIn(b"pinned=yes", pinned.stdout)
        observe("fixture", source=self.image_source, msgid=self.msgid,
                accepted_octets=self.article, status=pinned.stdout,
                exit_code=pinned.returncode)
        decision_fault = {}
        self.kill_at_durable_cut(
            "FN_BP_APP_TEST_PAUSE_AFTER_DECISION", b"BP APP DECISION DURABLE",
            observer=lambda **fields: decision_fault.update(fields))
        accepted_octets = self.receiver_article(self.msgid)
        observe("decision-cut-readback", octets=accepted_octets, fault=decision_fault)
        replayed = self.dispatch_receiver()
        self.assertEqual(replayed.returncode, EXIT.OK, replayed.stdout + replayed.stderr)
        self.assertIn(b"BP application handoff durable", replayed.stdout)
        self.assertIn(b"BP node receipt queued", replayed.stdout)
        observe("application-replay", exit_code=replayed.returncode,
                stdout=replayed.stdout, stderr=replayed.stderr)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

        # A second carrier reaches the durable outbox. Reconfigure the live
        # node there, then kill the receipt job before its contact runs.
        receiver, port = self.start_node(
            True, control=True,
            extra_env={"FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX": "1"})
        retry = self.send_request(port, "slice-retry")
        self.assertEqual(retry.returncode, EXIT.OK, retry.stdout + retry.stderr)
        outbox_held = self.wait_for_output(receiver, b"BP NODE OUTBOX DURABLE", timeout=120)
        config = self.tmp / "receiver-fn.toml"
        for action in ("remove", "add"):
            changed = self.invoke("operator", config, "bp-route", action,
                                  "dtn://sender/*", "sender-boundary")
            self.assertEqual(changed.returncode, EXIT.OK,
                             changed.stdout + changed.stderr)
        receiver.kill()
        receiver.wait(timeout=15)
        self.assertEqual(self.receiver_articles(), 1)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

        observe("outbox-process-death", exit_code=receiver.returncode,
                retry_exit_code=retry.returncode, retry_stdout=retry.stdout,
                retry_stderr=retry.stderr, held_stdout=outbox_held,
                selector="FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX", value="1")

        sender, sender_port = self.start_node(False, once=False)
        relay_faults = []
        self.relay.route(sender_port, cut_after=80,
                         observer=lambda **fields: relay_faults.append(fields))
        interrupted = self.dispatch_receiver()
        self.assertEqual(interrupted.returncode, EXIT.OK,
                         interrupted.stdout + interrupted.stderr)
        self.assertIn(b"BP node receipt transfer uncertain", interrupted.stdout)
        attempted = [line for line in interrupted.stdout.splitlines()
                     if line.startswith(b"BP transport work=") and
                     b"status=attempted" in line]
        self.assertTrue(attempted, interrupted.stdout)
        observe("receipt-contact-uncertain", exit_code=interrupted.returncode,
                stdout=interrupted.stdout, stderr=interrupted.stderr,
                attempted=attempted, relay_faults=list(relay_faults))
        sender.stop(grace=5)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)
        self.assertIn(b"pinned=yes", self.unrelated_status().stdout)

        # Checkpoint publication dies before selection. Recovery must retain
        # the same owed receipt jobs and the accepted article.
        checkpoint_fault = {}
        cut_code, cut_out, cut_err = self.rotate_receiver(
            "stage", observer=lambda **fields: checkpoint_fault.update(fields))
        observe("checkpoint-stage-cut", exit_code=cut_code,
                stdout=cut_out, stderr=cut_err, fault=checkpoint_fault)
        sender, sender_port = self.start_node(False, once=False)
        self.relay.route(sender_port)
        resumed = self.dispatch_receiver()
        self.assertEqual(resumed.returncode, EXIT.OK, resumed.stdout + resumed.stderr)
        forwarded = [line for line in resumed.stdout.splitlines()
                     if line.startswith(b"BP transport work=") and
                     b"status=forwarded" in line]
        attempted_work = {line.split(b"work=")[1].split()[0] for line in attempted}
        forwarded_work = {line.split(b"work=")[1].split()[0] for line in forwarded}
        self.assertTrue(attempted_work <= forwarded_work, resumed.stdout)
        observe("receipt-contact-resumed", exit_code=resumed.returncode,
                stdout=resumed.stdout, stderr=resumed.stderr,
                attempted_work=sorted(attempted_work),
                forwarded_work=sorted(forwarded_work))
        self.wait_for_output(sender, b"BP node delivery receipt-accepted", timeout=120)
        sender.stop(grace=5)
        self.assertEqual(self.receiver_articles(), 1)
        self.assertEqual(self.receiver_article(self.msgid), accepted_octets)
        matching = self.sender_status()
        unrelated = self.unrelated_status()
        self.assertIn(b"pinned=no", matching.stdout)
        self.assertIn(b"pinned=yes", unrelated.stdout)
        observe("receipt-obligation-settlement", matching=matching.stdout,
                unrelated=unrelated.stdout, matching_exit=matching.returncode,
                unrelated_exit=unrelated.returncode)
        code, out, err = self.rotate_receiver()
        self.assertEqual(code, EXIT.OK, out + err)
        self.assertEqual(self.receiver_articles(), 1)
        final_octets = self.receiver_article(self.msgid)
        self.assertEqual(final_octets, accepted_octets)
        observe("checkpoint-complete-readback", exit_code=code,
                stdout=out, stderr=err, octets=final_octets)

        # Both standalone sender processes have been reaped before the
        # production owner acquires this Store. Its recovery must preserve
        # the remaining BP obligation even with no outbound NNTP feed debt.
        self.assertIsNotNone(sender.poll())
        retiring = Node(self, PRODUCER, root=self.tmp / "sender-retirement")
        retiring.store_path = self.sender_store
        retiring.write_config()
        retiring.start()
        before = retiring.operator("obligations", expect=EXIT.OK)
        unrelated_line = b"obligation id=forward-unrelated kind=forward"
        matching_line = b"obligation id=forward-bp-node kind=forward"
        self.assertIn(unrelated_line, before.stdout)
        self.assertNotIn(matching_line, before.stdout)
        retired = retiring.operator("retire", "--drain", "4", timeout=240,
                                    expect=EXIT.OK)
        retiring.exited(EXIT.OK, timeout=120)
        report = (self.sender_store / "retire-report.txt").read_bytes()
        self.assertIn(report, retired.stdout)
        self.assertIn(unrelated_line, report)
        self.assertNotIn(matching_line, report)
        self.assertIn(b"pinned=yes", self.unrelated_status().stdout)
        self.assertIn(b"pinned=no", self.sender_status().stdout)
        observe("retirement-frozen-report", exit_code=retired.returncode,
                stdout=retired.stdout, stderr=retired.stderr, report=report)

    def test_dropped_receipt_contact_is_reoffered_by_the_next_pass(self):
        """Spec 4.3.2: an uncertain receipt transfer is connection-local.

        The receiver's own `serve' pass sends the owed receipt; the relay
        severs that connection after 80 client octets, after the TCPCL
        session is up and the transfer has started.  ACL2 reads it as
        :uncertain and requeues the job under its own identity; the pass
        logs it and exits 0.  The next `dispatch' pass, over an intact
        relay, offers the same job again and the sender accepts it.
        """
        sender, sender_port = self.start_node(False, once=False)
        self.relay.route(sender_port, cut_after=80)
        receiver, port = self.start_node(True)
        # The sender node holds its own FNBS lifecycle lock, so the request
        # leaves from a separate outbound journal of the same identity.
        sent = self.invoke(
            "bp-service", "run", "127.0.0.1", port,
            self.request_path, self.tmp / "request-fnbs",
            "dtn://sender/", "dtn://receiver/", "carrier-drop",
            "carrier-drop-attempt", 0, 3600000, 2, 32, 1048576, 0, 0,
        )
        self.assertEqual(sent.returncode, EXIT.OK, sent.stdout + sent.stderr)
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(receiver.returncode, EXIT.OK, out + err)
        self.assertIn(b"BP node receipt queued", out)
        self.assertIn(b"BP node receipt contact peer=dtn://sender/", out)
        self.assertIn(b"BP node receipt transfer uncertain", out)
        dropped = [x for x in out.splitlines()
                   if x.startswith(b"BP transport work=")]
        self.assertEqual(len(dropped), 1, out)
        self.assertIn(b"status=attempted", dropped[0])
        work = dropped[0].split(b"work=")[1].split()[0]

        self.relay.route(sender_port)
        again = self.dispatch_receiver()
        self.assertEqual(again.returncode, EXIT.OK, again.stdout + again.stderr)
        self.assertIn(b"BP node receipt contact peer=dtn://sender/", again.stdout)
        self.assertNotIn(b"BP node receipt transfer", again.stdout)
        delivered = [x for x in again.stdout.splitlines()
                     if x.startswith(b"BP transport work=")]
        self.assertEqual(len(delivered), 1, again.stdout)
        self.assertEqual(delivered[0].split(b"work=")[1].split()[0], work)
        self.assertIn(b"status=forwarded", delivered[0])
        self.wait_for_output(
            sender, b"BP node delivery receipt-accepted", timeout=120)
        sender.stop(grace=5)
        after = self.sender_status()
        self.assertEqual(after.returncode, EXIT.OK, after.stderr)
        self.assertIn(b"pinned=no", after.stdout)

    def test_absent_bp_trust_refuses_custody_with_the_policy_reason(self):
        # PRF-128 (D23): a bundle over a channel whose admission is refused is
        # refused at reception with the admission's reason, before any FNBS
        # step (fn-bpaj-refused-channel-takes-no-custody).  Until
        # mission-signed the node took anonymous custody and refused only the
        # application (PKT-170).
        receiver, port = self.start_node(True, trust=False)
        sent = self.send_request(port, "untrusted-request")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, EXIT.REFUSED, sent.stderr)
        self.assertEqual(receiver.returncode, EXIT.REFUSED, err)
        self.assertIn(b"BP channel admission refused reason=no-trust-profile", out)
        self.assertIn(b"BP refused xfer=0 reason=no-trust-profile", out)
        self.assertNotIn(b"BP accepted", out)
        self.assertNotIn(b"BP node delivery", out)
        self.assertEqual(self.receiver_articles(), 0)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

    def test_admitted_channel_without_inbound_scope_refuses_store_request(self):
        receiver, port = self.start_node(True, inbound=False)
        sent = self.send_request(port, "no-inbound-scope")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertEqual(receiver.returncode, EXIT.OK, out + err)
        self.assertIn(b"BP node delivery request-refused", out)
        # PRF-224: the durable kind 7 of a refusal is reported refused by
        # name, never as a durable handoff.
        self.assertIn(b"BP application handoff refused "
                      b"disposition=request-refused", out)
        self.assertNotIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_articles(), 0)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

    def test_absent_bp_trust_refuses_the_receipt_at_reception(self):
        # PRF-128: the sender's node does not admit the channel the receipt
        # arrives on, so the receipt is refused at reception with the
        # admission's reason; it never reaches the release question and the
        # pin stays.
        receiver, port = self.start_node(True)
        sent = self.send_request(port, "untrusted-return")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertEqual(receiver.returncode, EXIT.OK, err)
        self.assertIn(b"BP node receipt queued", out)
        sender, port = self.start_node(False, once=False, trust=False)
        self.relay.route(port)
        delivered = self.tick_receiver()
        self.assertEqual(delivered.returncode, EXIT.REFUSED, delivered.stderr)
        self.wait_for_output(
            sender, b"BP refused xfer=0 reason=no-trust-profile", timeout=120)
        sender.stop(grace=5)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)

    @staticmethod
    def wait_for_output(process, marker, timeout=45):
        return process.output_until(marker, timeout=timeout)

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
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertEqual(receiver.returncode, EXIT.UNCERTAIN, (out, err))
        self.assertIn(b"conflicting durable bytes", err)
        self.assertIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_articles(), 1)

    def test_exact_receipt_with_wrong_carrier_peer_fences(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN",
            b"BP NODE KIND7 DURABLE",
        )
        replay = self.invoke(
            "app-journal", "receipt-replay", self.receiver_store,
            self.receiver_receipts, self.request_path,
        )
        self.assertEqual(replay.returncode, EXIT.OK, replay.stderr)
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
        self.assertEqual(restarted.returncode, EXIT.UNCERTAIN, restarted.stderr)
        self.assertIn(b"conflicting durable bytes", restarted.stderr)
        self.assertEqual(self.receiver_articles(), 1)

    def kill_at_durable_cut(self, selector, marker, observer=None):
        receiver, port = self.start_node(True, extra_env={selector: "1"})
        sent = self.send_request(port, "cut-request")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        held = self.wait_for_output(receiver, marker, timeout=120)
        receiver.kill()
        receiver.wait(timeout=15)
        self.assertEqual(self.receiver_articles(), 1)
        if observer is not None:
            observer(exit_code=receiver.returncode, held_stdout=held,
                     selector=selector, value="1", marker=marker)

    def test_death_after_fnrj_receipt_decision_replays_one_article(self):
        self.kill_at_durable_cut(
            "FN_BP_APP_TEST_PAUSE_AFTER_DECISION",
            b"BP APP DECISION DURABLE",
        )
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP application handoff durable", restarted.stdout)
        self.assertIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 1)

    def test_death_after_kind_seven_replays_owed_outbox(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN",
            b"BP NODE KIND7 DURABLE",
        )
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 1)

    def test_live_route_control_is_durable_and_pumped_at_receipt_hold(self):
        """SCN-218 boundary: actual operator CONFIG mutates the held owner."""
        receiver, port = self.start_node(
            True, control=True,
            extra_env={"FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX": "1"})
        sent = self.send_request(port, "control-held-request")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.wait_for_output(receiver, b"BP NODE OUTBOX DURABLE", timeout=120)
        config = self.tmp / "receiver-fn.toml"
        socket_path = self.receiver_store / "control.sock"
        self.assertTrue(socket_path.exists())
        before = len(tuple((self.receiver_store / "config").iterdir()))
        refused = self.invoke("operator", config, "group", "create", "fn.unrelated")
        self.assertEqual(refused.returncode, EXIT.REFUSED, refused.stderr)
        self.assertIn(b"unsupported-bp-control-operation", refused.stdout)
        self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before)
        removed = self.invoke("operator", config, "bp-route", "remove",
                              "dtn://sender/*", "sender-boundary")
        self.assertEqual(removed.returncode, EXIT.OK, removed.stderr)
        self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before + 1)
        restored = self.invoke("operator", config, "bp-route", "add",
                               "dtn://sender/*", "sender-boundary")
        self.assertEqual(restored.returncode, EXIT.OK, restored.stderr)
        self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before + 2)
        self.assertIsNone(receiver.poll())
        frontier = self.receiver_journal / "sequence" / "frontier.fnb"
        before_frontier = frontier.read_bytes()
        receiver.kill()
        receiver.wait(timeout=15)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertEqual(frontier.read_bytes(), before_frontier)
        self.assertNotIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 1)

    def change_receiver_boundary(self, port, *, timeout=120):
        return self.invoke(
            "operator", self.tmp / "receiver-fn.toml", "bp-boundary", "add",
            "sender-boundary", "sender.bp.gate.invalid", "dtn://sender/", port,
            "fn.test", "32768", "16", "contact", self.relay.port, timeout=timeout)

    @staticmethod
    def read_exact(connection, length):
        result = b""
        while len(result) < length:
            piece = connection.recv(length - len(result))
            if not piece:
                raise AssertionError("TCPCL session ended before its expected frame")
            result += piece
        return result

    def test_live_listener_rebind_keeps_old_session_generation_and_fd(self):
        receiver, old_port = self.start_node(True, once=False, control=True, configured=True)
        initial = receiver.announcement(b"BP NODE GENERATION ", timeout=30)
        old_generation = int(initial.split()[3])
        with Acl2Session(IMAGE) as bridge:
            contact = acl2_octets(bridge.call("(fn-tcl-encode (fn-tcl-make-contact 4 0))"))
            init = acl2_octets(bridge.call(
                "(fn-tcl-encode (fn-tcl-make-sess-init 10 1024 1048576 "
                "(fn-record-string-octets \"dtn://sender/\") nil))"))
            server_init = acl2_octets(bridge.call(
                "(fn-tcl-encode (fn-tcl-make-sess-init 10 1024 1048576 "
                "(fn-record-string-octets \"dtn://receiver/\") nil))"))
            keepalive = acl2_octets(bridge.call("(fn-tcl-encode (fn-tcl-make-keepalive))"))
        with socket.create_connection(("127.0.0.1", old_port), timeout=15) as old:
            old.settimeout(20)
            old.sendall(contact)
            self.assertEqual(self.read_exact(old, len(contact)), contact)
            self.assertEqual(self.read_exact(old, len(server_init)), server_init)
            old.sendall(init)
            active = receiver.announcement(b"BP NODE GENERATION ", timeout=30)
            self.assertTrue(active.rstrip().endswith(b"SESSION " + str(old_generation).encode()), active)
            new_port = free_port()
            changed = self.change_receiver_boundary(new_port)
            self.assertEqual(changed.returncode, EXIT.OK, changed.stderr)
            self.assertEqual(receiver.announcement(b"BP NODE LISTENING ", timeout=30).rstrip(),
                             b"BP NODE LISTENING " + str(new_port).encode())
            installed = receiver.announcement(b"BP NODE GENERATION ", timeout=30)
            self.assertNotEqual(int(installed.split()[3]), old_generation)
            self.assertIn(b"LISTENER-FDS 1 PEAK 2", installed)
            self.assertTrue(installed.rstrip().endswith(b"SESSION " + str(old_generation).encode()), installed)
            with self.assertRaises(OSError):
                socket.create_connection(("127.0.0.1", old_port), timeout=2)
            # Actual established old TCPCL FD still exchanges core-made wire
            # after its listening descriptor has been retired.
            old.sendall(keepalive)
            self.assertEqual(self.read_exact(old, len(keepalive)), keepalive)
        # The old session has closed; a new acceptance belongs to the installed generation.
        with socket.create_connection(("127.0.0.1", new_port), timeout=15) as new:
            accepted = receiver.announcement(b"BP NODE GENERATION ", timeout=30)
            self.assertTrue(accepted.rstrip().endswith(b"SESSION " + installed.split()[3]), accepted)
            new.sendall(contact)
            self.assertEqual(self.read_exact(new, len(contact)), contact)
        self.assertIsNone(receiver.poll(), receiver.diagnostics())

    def test_live_listener_occupied_port_is_uncertain_and_restart_reconciles(self):
        receiver, old_port = self.start_node(True, once=False, control=True, configured=True)
        receiver.announcement(b"BP NODE GENERATION ", timeout=30)
        before = len(tuple((self.receiver_store / "config").iterdir()))
        with socket.socket() as occupied:
            occupied.bind(("127.0.0.1", 0))
            occupied.listen(1)
            new_port = occupied.getsockname()[1]
            changed = self.change_receiver_boundary(new_port)
            self.assertEqual(changed.returncode, EXIT.UNCERTAIN, changed.stderr)
            self.assertEqual(receiver.wait(timeout=45), EXIT.UNCERTAIN, receiver.diagnostics())
            self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before + 1)
            with self.assertRaises(OSError):
                socket.create_connection(("127.0.0.1", old_port), timeout=2)
        restarted, installed = self.start_node(True, once=False, trust=False, control=True, configured=True)
        self.assertEqual(installed, new_port)
        self.assertIn(b"LISTENER-FDS 1", restarted.announcement(b"BP NODE GENERATION ", timeout=30))
        self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before + 1)
        self.assertIsNone(restarted.poll(), restarted.diagnostics())

    def test_death_at_each_live_listener_effect_recovers_published_configuration(self):
        # Each real process-death label is a book-declared crash point.
        cuts = ("configuration-published", "before-bind", "after-bind", "before-install",
                "after-install", "before-retire", "after-retire")
        for cut in cuts:
            with self.subTest(cut=cut):
                receiver, old_port = self.start_node(
                    True, once=False, control=True, configured=True,
                    extra_env={"FN_BP_LISTENER_TEST_PAUSE_CUT": cut})
                receiver.announcement(b"BP NODE GENERATION ", timeout=30)
                before = len(tuple((self.receiver_store / "config").iterdir()))
                new_port = free_port()
                client = start(
                    [IMAGE, "--fn", "operator", str(self.tmp / "receiver-fn.toml"),
                     "bp-boundary", "add", "sender-boundary", "sender.bp.gate.invalid",
                     "dtn://sender/", str(new_port), "fn.test", "32768", "16",
                     "contact", str(self.relay.port)], cwd=ROOT, env=environment())
                self.addCleanup(client.stop, 5)
                self.assertEqual(receiver.announcement(b"BP LISTENER CUT ", timeout=45).rstrip(),
                                 b"BP LISTENER CUT " + cut.encode())
                self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before + 1)
                receiver.kill()
                receiver.wait(timeout=15)
                self.assertEqual(client.wait(timeout=30), EXIT.UNCERTAIN, client.diagnostics())
                with self.assertRaises(OSError):
                    socket.create_connection(("127.0.0.1", old_port), timeout=2)
                restarted, port = self.start_node(
                    True, once=False, trust=False, control=True, configured=True)
                self.assertEqual(port, new_port)
                self.assertIn(b"LISTENER-FDS 1", restarted.announcement(b"BP NODE GENERATION ", timeout=30))
                self.assertEqual(len(tuple((self.receiver_store / "config").iterdir())), before + 1)
                restarted.stop(grace=5)

    def test_control_config_for_another_store_is_refused_before_listener(self):
        wrong = self.tmp / "wrong-control.toml"
        wrong.write_text(f'[store]\npath = "{self.sender_store}"\n', encoding="ascii")
        result = run(self.dispatch_receiver_args() + ["--control-config", str(wrong)],
                     cwd=ROOT, env=environment(), timeout=120)
        self.assertEqual(result.returncode, EXIT.REFUSED, result.stderr)
        self.assertIn(b"control-store-mismatch", result.stdout + result.stderr)
        self.assertNotIn(b"BP NODE CONTROL", result.stdout)
        self.assertFalse((self.sender_store / "control.sock").exists())
        self.assertFalse((self.receiver_store / "control.sock").exists())

    def test_control_listener_retires_after_one_normal_bp_session(self):
        peer, peer_port = self.start_node(False, once=False)
        self.relay.route(peer_port)
        receiver, port = self.start_node(True, control=True)
        socket_path = self.receiver_store / "control.sock"
        self.assertTrue(socket_path.exists())
        sent = self.send_request(port, "control-one-session")
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertEqual(receiver.wait(timeout=120), EXIT.OK, receiver.diagnostics())
        self.assertFalse(socket_path.exists())
        peer.stop(grace=5)
        self.assertEqual(self.receiver_articles(), 1)

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
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertNotIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(frontier.read_bytes(), before_frontier)
        # The pass sends the one owed receipt itself (spec 9.4); the harness
        # neighbour drops the connection, so the only new lifecycle frames are
        # that job's :attempting record and its :requeued :uncertain record
        # (spec 4.3.2) -- no second job and no second sequence.
        self.assertIn(b"BP node receipt transfer uncertain", restarted.stdout)
        self.assertEqual(len(tuple(
            (self.receiver_journal / "lifecycle").glob("*.fnb"))),
            before_records + 2)
        self.assertEqual(self.receiver_articles(), 1)

    def test_ambiguous_outbox_publication_is_uncertain_not_refused(self):
        self.kill_at_durable_cut(
            "FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN",
            b"BP NODE KIND7 DURABLE",
        )
        fault_env = {"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"}
        ambiguous = self.dispatch_receiver(env=fault_env)
        self.assertEqual(ambiguous.returncode, EXIT.UNCERTAIN,
                         (ambiguous.stdout, ambiguous.stderr))
        self.assertIn(b"uncertain", ambiguous.stderr.lower())
        self.assertNotIn(b"BP node receipt queued", ambiguous.stdout)

        # Reopen fences the uncertain publication by reading FNBS and its
        # sequence frontier.  The earlier Store/FNRJ decision is not replayed
        # into a second accepted article or a fresh return-job sequence.
        frontier = self.receiver_journal / "sequence" / "frontier.fnb"
        after_fault_frontier = frontier.read_bytes()
        recovered = self.dispatch_receiver()
        self.assertEqual(recovered.returncode, EXIT.OK,
                         (recovered.stdout, recovered.stderr))
        self.assertEqual(frontier.read_bytes(), after_fault_frontier)
        self.assertEqual(self.receiver_articles(), 1)

    def test_kind_five_ambiguous_publication_never_delivers_to_store(self):
        seed = self.dispatch_receiver()
        self.assertEqual(seed.returncode, EXIT.OK, seed.stderr)
        receiver, port = self.start_node(
            True, extra_env={"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"})
        sent = self.send_request(port, "kind-five-cut")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(receiver.returncode, EXIT.UNCERTAIN, (out, err))
        self.assertNotIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_articles(), 0)
        self.assertIn(sent.returncode, (EXIT.REFUSED, LOST), sent.stderr)

    def test_ambiguous_fnrj_decision_fences_until_cold_replay(self):
        receiver, port = self.start_node(
            True,
            extra_env={
                "FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE": "1",
            },
        )
        sent = self.send_request(port, "fnrj-uncertain")
        out, err = receiver.communicate(timeout=120)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.assertEqual(receiver.returncode, EXIT.UNCERTAIN, (out, err))
        self.assertIn(b"BP node application uncertain", out)
        self.assertNotIn(b"BP application handoff durable", out)
        self.assertEqual(self.receiver_articles(), 1)

        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP application handoff durable", restarted.stdout)
        self.assertIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 1)

    def test_expired_recovered_kind_five_never_enters_store(self):
        receiver, port = self.start_node(
            True,
            extra_env={"FN_BP_NODE_TEST_PAUSE_AFTER_KIND_FIVE": "1"},
        )
        sent = self.send_request(port, "short-lived", lifetime=1500)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.wait_for_output(receiver, b"BP NODE KIND5 DURABLE", timeout=120)
        receiver.kill()
        receiver.wait(timeout=15)
        time.sleep(1.8)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertNotIn(b"BP application handoff durable", restarted.stdout)
        self.assertNotIn(b"BP node receipt queued", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 0)

    def test_deletion_report_intent_recovers_and_observation_does_not_release(self):
        receiver, port = self.start_node(
            True, extra_env={"FN_BP_NODE_TEST_PAUSE_AFTER_KIND_FIVE": "1"},
        )
        sent = self.send_deletion_request(port)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        self.wait_for_output(receiver, b"BP NODE KIND5 DURABLE", timeout=120)
        receiver.kill()
        receiver.wait(timeout=15)
        time.sleep(1.8)

        # The kind-10 record is durable before the outbound sequence/job cut.
        candidate = start(self.dispatch_receiver_args(reports=True), cwd=ROOT,
                          env=environment({"FN_BP_NODE_TEST_PAUSE_AFTER_KIND_TEN": "1"}))
        self.addCleanup(candidate.stop, 5)
        self.wait_for_output(candidate, b"BP NODE KIND10 DURABLE", timeout=120)
        candidate.kill()
        candidate.wait(timeout=15)
        self.assertEqual(self.receiver_articles(), 0)

        report_payloads = self.acl2_lifecycle_payloads(
            self.receiver_journal, 10)
        self.assertEqual(len(report_payloads), 1)
        report_payload = report_payloads[0]
        self.assertLessEqual(len(report_payload), 4096)
        with Acl2Session(IMAGE) as bridge:
            literal = bridge.literal(report_payload)
            self.assertEqual(
                acl2_result(bridge.call(
                    "(let ((parsed (fn-bpn-report-decode '" + literal + "))) "
                    "(and (fn-cbor-result-okp parsed) "
                    "(equal (fn-bpn-report-encode "
                    "(fn-cbor-result-value parsed)) '" + literal + ")))"
                )), b"T")

        restarted = self.dispatch_receiver(reports=True)
        self.assertEqual(restarted.returncode, EXIT.OK, restarted.stderr)
        self.assertIn(b"BP queue accepted", restarted.stdout)
        self.assertEqual(self.receiver_articles(), 0)
        frontier = self.receiver_journal / "sequence" / "frontier.fnb"
        frontier_bytes = frontier.read_bytes()
        lifecycle = self.receiver_journal / "lifecycle"
        durable_frames = {
            frame.name: frame.read_bytes() for frame in lifecycle.glob("*.fnb")
        }
        repeated = self.dispatch_receiver(reports=True)
        self.assertEqual(repeated.returncode, EXIT.OK, repeated.stderr)
        self.assertEqual(frontier.read_bytes(), frontier_bytes)
        # Every durable frame is kept byte for byte.  The repeated pass offers
        # the owed report job on the node's own base contact (spec 9.4); the
        # harness neighbour drops it, so the only new frames are that job's
        # :attempting and :requeued :uncertain records (spec 4.3.2).
        after_frames = {
            frame.name: frame.read_bytes() for frame in lifecycle.glob("*.fnb")
        }
        self.assertEqual(
            {name: after_frames.get(name) for name in durable_frames},
            durable_frames,
        )
        self.assertEqual(len(after_frames), len(durable_frames) + 2,
                         repeated.stdout)
        self.assertIn(b"BP node receipt transfer uncertain", repeated.stdout)
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.receiver_journal, 10),
            [report_payload],
        )

        sender, port = self.start_node(False, once=False)
        self.relay.route(port, cut_next=True)
        interrupted = self.tick_receiver()
        self.assertEqual(interrupted.returncode, LOST, interrupted.stderr)
        self.assertIn(b"reason=uncertain", interrupted.stdout)
        sender.stop(grace=5)
        pinned = self.sender_status()
        self.assertEqual(pinned.returncode, EXIT.OK, pinned.stderr)
        self.assertIn(b"pinned=yes", pinned.stdout)

        sender, port = self.start_node(False, once=False)
        self.relay.route(port)
        delivered = self.tick_receiver()
        self.assertEqual(delivered.returncode, EXIT.OK, delivered.stderr)
        self.wait_for_output(sender, b"BP status report observed", timeout=120)
        self.assertIn(
            report_payload,
            self.acl2_lifecycle_payloads(self.sender_journal, 5),
        )
        sender.stop(grace=5)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)
        self.assertIn(b"pinned=yes", self.unrelated_status().stdout)



if __name__ == "__main__":
    unittest.main()
