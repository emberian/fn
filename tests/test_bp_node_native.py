"""Native A3 article/receipt path over one FNBS owner per process.

The relay copies bytes only.  It does not manufacture TCPCL acknowledgement,
BP acceptance, Store commitment, or an application receipt.
"""

import collections
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
# The node runs on either developer image: FN_NATIVE_BP_NODE_HOST names the one
# under test (the DTN developer image, whose profile ships the node), and it
# falls back to the default developer image.
IMAGE = Path(os.environ.get(
    "FN_NATIVE_BP_NODE_HOST",
    os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer")))


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
            b"\r\nA3 body\r\n"
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
        env = dict(self.env if env is None else env)
        if extra_env:
            env.update(extra_env)
        return subprocess.run(
            self.dispatch_receiver_args(reports=reports),
            cwd=ROOT, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=120, check=False,
        )

    def deletion_request_bundle(self):
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-node")')
            bridge.call('(include-book "books/codec-attach")')
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
            path.write_bytes(run_store.acl2_octets(bridge.call(form)))
            return path
        finally:
            bridge.close()

    def send_deletion_request(self, port):
        return self.invoke(
            "tcpcl", "send", "127.0.0.1", port,
            self.deletion_request_bundle(), self.tmp / "deletion-sender-spool",
            "dtn://sender/", "dtn://receiver/", 0, 65536, 1048576, 0,
        )

    def unrouted_transit_bundle(self):
        """ACL2 authors the older wire; Python only carries its octets."""
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-node")')
            bridge.call('(include-book "books/codec-attach")')
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            unrouted = "(cons :dtn '(47 47 117 110 114 111 117 116 101 100 47))"
            form = (
                "(fn-bpb-encode (fn-bpn-send-bundle "
                f"(fn-bpn-config {sender} 3600000 2 32 1048576) "
                f"{unrouted} '(1 2 3 4) 77 "
                "(fn-clock-observation 0 0 0 nil)))"
            )
            path = self.tmp / "unrouted-transit.bundle"
            path.write_bytes(run_store.acl2_octets(bridge.call(form)))
            return path
        finally:
            bridge.close()

    def test_older_unrouted_transit_does_not_block_younger_local_request(self):
        receiver, port = self.start_node(True, once=False)
        transit = self.unrouted_transit_bundle()
        sent_old = self.invoke(
            "tcpcl", "send", "127.0.0.1", port, transit,
            self.tmp / "unrouted-sender-spool", "dtn://sender/",
            "dtn://receiver/", 0, 65536, 1048576, 0,
        )
        self.assertEqual(sent_old.returncode, 0, sent_old.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)

        sent_new = self.send_request(port, "after-unrouted-transit")
        self.assertEqual(sent_new.returncode, 0, sent_new.stderr)
        delivered = self.wait_for_output(
            receiver, b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", delivered)
        self.stop_process(receiver)

        self.assertEqual(self.receiver_counts()[1], 1)
        payloads = self.acl2_lifecycle_payloads(self.receiver_journal, 5)
        self.assertIn(bytes((1, 2, 3, 4)), payloads)
        self.assertIn(self.request_path.read_bytes(), payloads)
        self.assertEqual(len(payloads), 2)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP FNBS recovered held=2", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 1)

    def conflicting_transit_bundle(self):
        """The unrouted transit identity (creation 0, sequence 77) with another
        payload: same bundle ID, different immutable projection.  ACL2 authors
        the wire."""
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-node")')
            bridge.call('(include-book "books/codec-attach")')
            sender = "(cons :dtn '(47 47 115 101 110 100 101 114 47))"
            unrouted = "(cons :dtn '(47 47 117 110 114 111 117 116 101 100 47))"
            form = (
                "(fn-bpb-encode (fn-bpn-send-bundle "
                f"(fn-bpn-config {sender} 3600000 2 32 1048576) "
                f"{unrouted} '(9 9 9 9) 77 "
                "(fn-clock-observation 0 0 0 nil)))"
            )
            path = self.tmp / "conflicting-transit.bundle"
            path.write_bytes(run_store.acl2_octets(bridge.call(form)))
            return path
        finally:
            bridge.close()

    @staticmethod
    def conflict_records(journal):
        """The lifecycle frames ACL2's kind-14 decoder opens, decoded."""
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-fnbs-conflict-codec")')
            bridge.call('(include-book "books/codec-attach")')
            rows = []
            for frame in sorted((journal / "lifecycle").glob("*.fnb")):
                octets = "'" + bridge.literal(frame.read_bytes())
                row = bridge.call(f"(fn-bpnf-conflict-unframe {octets})")
                if row.lstrip().upper().startswith(b"(:BPNF-CONFLICT "):
                    rows.append((frame.name, row))
            return rows
        finally:
            bridge.close()

    def send_transit(self, port, path, spool):
        return self.invoke(
            "tcpcl", "send", "127.0.0.1", port, path, self.tmp / spool,
            "dtn://sender/", "dtn://receiver/", 0, 65536, 1048576, 0,
        )

    def test_identity_conflict_is_refused_recorded_and_replayed(self):
        """N11 on the image: a second reception whose identity names a held
        bundle with another payload is refused :identity-conflict, a durable
        kind-14 record names it, the node keeps answering, and replay
        accepts the record."""
        receiver, port = self.start_node(True, once=False)
        first = self.send_transit(port, self.unrouted_transit_bundle(), "s1")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)

        conflicting = self.conflicting_transit_bundle()
        refused = self.send_transit(port, conflicting, "s2")
        out = self.wait_for_output(receiver, b"reason=identity-conflict", timeout=60)
        self.assertIn(b"BP refused xfer=", out)
        self.assertEqual(refused.returncode, 1, (refused.stdout, refused.stderr, out))
        # The same conflict again: refused again, never :busy.
        again = self.send_transit(port, conflicting, "s3")
        self.assertEqual(again.returncode, 1, again.stderr)
        out = self.wait_for_output(receiver, b"reason=identity-conflict", timeout=60)
        self.assertNotIn(b"reason=busy", out)

        # The node keeps answering: a fresh request is delivered.
        sent = self.send_request(port, "after-identity-conflict")
        self.assertEqual(sent.returncode, 0, sent.stderr)
        delivered = self.wait_for_output(
            receiver, b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", delivered)
        self.stop_process(receiver)

        records = self.conflict_records(self.receiver_journal)
        self.assertEqual(len(records), 2, records)
        payloads = self.acl2_lifecycle_payloads(self.receiver_journal, 5)
        self.assertIn(bytes((1, 2, 3, 4)), payloads)
        self.assertNotIn(bytes((9, 9, 9, 9)), payloads)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP FNBS recovered held=2", restarted.stdout)
        self.assertEqual(self.conflict_records(self.receiver_journal), records)

    def test_busy_application_defers_and_redelivers_after_backoff(self):
        """BP-R17 on the image: the owner answers the first delivery :busy.
        The node neither refuses nor fences: the row stays held, and the
        first dispatch after the 5000 ms backoff delivers it."""
        receiver, port = self.start_node(
            True, once=False, extra_env={"FN_BP_NODE_TEST_APP_BUSY": "1"})
        sent = self.send_request(port, "busy-request")
        self.assertEqual(sent.returncode, 0, sent.stderr)
        out = self.wait_for_output(
            receiver, b"BP node delivery deferred busy=1", timeout=120)
        self.assertNotIn(b"request-refused", out)
        self.assertNotIn(b"application uncertain", out)
        self.assertNotIn(b"application result is uncertain", out)
        time.sleep(5.5)
        # Any later connection runs the dispatch loop; an unrouted transit
        # consumes no application answer.
        self.send_transit(port, self.unrouted_transit_bundle(), "busy-ping")
        delivered = self.wait_for_output(
            receiver, b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", delivered)
        self.assertNotIn(b"request-refused", delivered)
        self.stop_process(receiver)
        self.assertEqual(self.receiver_counts()[1], 1)

    def test_permanently_busy_application_strands_row_until_recovery(self):
        """BP-R17 at the kind-8 retry bound: three :busy answers strand the
        row, visibly and still held; nothing is refused or stored; a cold
        recovery clears the volatile wait and delivers it."""
        receiver, port = self.start_node(
            True, once=False, extra_env={"FN_BP_NODE_TEST_APP_BUSY": "100"})
        sent = self.send_request(port, "stranded-request")
        self.assertEqual(sent.returncode, 0, sent.stderr)
        seen = self.wait_for_output(
            receiver, b"BP node delivery deferred busy=1", timeout=120)
        transit = self.unrouted_transit_bundle()
        for spool, marker in (("p1", b"BP node delivery deferred busy=2"),
                              ("p2", b"BP node delivery stranded busy=3")):
            time.sleep(5.5)
            self.send_transit(port, transit, spool)
            seen += self.wait_for_output(receiver, marker, timeout=120)
        # A stranded row is not offered again: a later dispatch is silent.
        time.sleep(5.5)
        self.send_transit(port, transit, "p3")
        time.sleep(2)
        receiver.terminate()
        receiver.wait(timeout=15)
        seen += receiver.stdout.read()
        self.assertNotIn(b"busy=4", seen)
        self.assertNotIn(b"request-refused", seen)
        self.assertNotIn(b"request-accepted", seen)
        self.assertEqual(self.receiver_counts()[1], 0)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP node delivery request-accepted", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 1)

    def other_boot_domain_frame(self):
        """ACL2's clock-domain frame for a boot ID that is not this boot's."""
        boot = Path("/proc/sys/kernel/random/boot_id").read_text("ascii").strip()
        other = boot[:-1] + ("0" if boot[-1] != "0" else "1")
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-clock-domain")')
            bridge.call('(include-book "books/codec-attach")')
            octets = " ".join(str(b) for b in other.encode("ascii"))
            return run_store.acl2_octets(bridge.call(f"(fn-bpcd-frame '({octets}))"))
        finally:
            bridge.close()

    def test_restart_in_another_boot_fences_and_keeps_rows(self):
        """N07 on the image: the durable boot domain names another boot, so
        recovery through fn-bpnp-step answers (:restart-fault :clock-domain
        :different-boot) and no held row changes; the true domain restored,
        the same journal recovers."""
        receiver, port = self.start_node(True, once=False)
        first = self.send_transit(port, self.unrouted_transit_bundle(), "s1")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.wait_for_output(
            receiver, b"BP node progress waiting reason=route", timeout=120)
        self.stop_process(receiver)

        domain = self.receiver_journal / "clock-domain.fnb"
        saved = domain.read_bytes()
        lifecycle = self.receiver_journal / "lifecycle"
        before = tuple((p.name, p.read_bytes()) for p in sorted(lifecycle.iterdir()))
        domain.write_bytes(self.other_boot_domain_frame())

        fenced = self.dispatch_receiver()
        self.assertEqual(fenced.returncode, 3, fenced.stderr)
        self.assertIn(b"restart fenced: clock domain different-boot", fenced.stderr)
        self.assertEqual(
            tuple((p.name, p.read_bytes()) for p in sorted(lifecycle.iterdir())),
            before)

        domain.write_bytes(saved)
        restarted = self.dispatch_receiver()
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP FNBS recovered held=1", restarted.stdout)

    def forward_mru_bundles(self):
        """ACL2 authors the two transit wires; Python only carries octets."""
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-node")')
            bridge.call('(include-book "books/codec-attach")')
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
                wire = run_store.acl2_octets(
                    bridge.call(f"(fn-bpb-encode {bundle})"))
                path = self.tmp / f"forward-{label}.bundle"
                path.write_bytes(wire)
                paths.append(path)
            self.assertGreater(paths[0].stat().st_size, 32768)
            self.assertLess(paths[1].stat().st_size, 32768)
            return paths
        finally:
            bridge.close()

    def test_older_mru_wait_allows_younger_forward_and_replays(self):
        receiver, port = self.start_node(True, once=False)
        older, younger = self.forward_mru_bundles()
        for label, path in (("older", older), ("younger", younger)):
            sent = self.invoke(
                "tcpcl", "send", "127.0.0.1", port, path,
                self.tmp / f"forward-{label}-sender-spool", "dtn://sender/",
                "dtn://receiver/", 0, 65536, 1048576, 0,
            )
            self.assertEqual(sent.returncode, 0, sent.stderr)
        self.stop_process(receiver)
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
        dispatched = subprocess.run(
            args, cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=240, check=False,
        )
        self.assertEqual(dispatched.returncode, 0, dispatched.stderr)
        self.assertIn(b"BP forwarding attempt durable", dispatched.stdout)
        self.assertIn(b"BP forwarding result durable", dispatched.stdout)
        # Both carriers dispatched (two kind-6 in all), and the younger one
        # alone attempted (kind 8) and settled (kind 9): the older one's image
        # exceeds the 32 KiB session MRU and waits (N04).
        after_forward = self.acl2_lifecycle_kinds(self.receiver_journal)
        self.assertEqual(after_forward, collections.Counter({5: 2, 6: 2, 8: 1, 9: 1}))
        forwarded_names = sorted(
            p.name for p in (self.receiver_journal / "lifecycle").glob("*.fnb"))

        self.stop_process(peer)
        self.relay.route(None)
        replayed = subprocess.run(
            args, cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=120, check=False,
        )
        self.assertEqual(replayed.returncode, 0, replayed.stderr)
        self.assertIn(b"BP FNBS recovered held=2", replayed.stdout)
        self.assertNotIn(b"BP forwarding attempt durable", replayed.stdout)
        self.assertEqual(
            sorted(p.name for p in (self.receiver_journal / "lifecycle").glob("*.fnb")),
            forwarded_names)
        self.assertEqual(self.acl2_lifecycle_kinds(self.receiver_journal), after_forward)

    @staticmethod
    def acl2_lifecycle_kinds(journal):
        """Count the journal's lifecycle frames by the ACL2 decoder that opens each.

        Each kind's own unframe function accepts only its frame version and
        kind, so a frame counts as kind 6 only when it is a dispatch record.
        A frame no decoder here opens counts as 0.
        """
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            for book in ("bp-fnbs-codec", "bp-fnbs-dispatch-codec",
                         "bp-fnbs-forward-codec"):
                bridge.call(f'(include-book "books/{book}")')
            kinds = collections.Counter()
            for frame in sorted((journal / "lifecycle").glob("*.fnb")):
                octets = "'" + bridge.literal(frame.read_bytes())
                kinds[run_store.acl2_nat(bridge.call(
                    f"(cond ((fn-bpnf-stored-record-unframe {octets}) 5) "
                    f"((fn-bpnp-dispatch-unframe {octets}) 6) "
                    f"((fn-bpnp-attempt-unframe {octets}) 8) "
                    f"((fn-bpnp-result-unframe {octets}) 9) (t 0))"))] += 1
            return kinds
        finally:
            bridge.close()

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
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.stop_process(receiver)
        payload = self.acl2_lifecycle_payloads(self.receiver_journal, 5)[-1]

        peer, peer_port = self.start_node(False, once=False)
        self.relay.route(peer_port)
        args = self.dispatch_receiver_args()
        env = dict(self.env)
        env["FN_BP_NODE_TEST_PAUSE_AFTER_KIND_EIGHT_SENT"] = "1"
        cut = subprocess.Popen(
            args, cwd=ROOT, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0,
        )
        self.addCleanup(self.stop_process, cut)
        self.wait_for_output(cut, b"BP NODE KIND8 SENT", timeout=240)
        cut.kill()
        cut.wait(timeout=15)
        journal = self.receiver_journal / "lifecycle"
        after_cut = len(tuple(journal.glob("*.fnb")))
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.sender_journal, 5).count(payload), 1)

        retried = subprocess.run(
            args, cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=240, check=False,
        )
        self.assertEqual(retried.returncode, 0, retried.stderr)
        self.assertIn(b"BP FNBS recovered", retried.stdout)
        self.assertIn(b"BP forwarding attempt durable", retried.stdout)
        self.assertIn(b"BP forwarding result durable", retried.stdout)
        self.assertIn(b"status=sent", retried.stdout)
        self.assertNotIn(b"BP forwarding stranded", retried.stdout)
        # The retry's kind 8 and its kind 9; the peer still holds one copy.
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), after_cut + 2)
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.sender_journal, 5).count(payload), 1)

        settled = subprocess.run(
            args, cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=120, check=False,
        )
        self.assertEqual(settled.returncode, 0, settled.stderr)
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

        self.assertEqual(send_younger("u-spool-1").returncode, 0)
        first = self.wait_for_output(
            receiver, b"BP forwarding result durable", timeout=120)
        self.assertIn(b"BP forwarding attempt durable", first)
        self.assertIn(b"BP forwarding transfer uncertain", first)
        self.assertIn(b"status=uncertain", first)
        self.assertIsNone(receiver.poll(), "node stopped after a connection fault")
        # The same process serves again, and re-offers the row in-process.
        self.assertEqual(send_younger("u-spool-2").returncode, 0)
        second = self.wait_for_output(
            receiver, b"BP forwarding result durable", timeout=120)
        self.assertIn(b"BP forwarding attempt durable", second)
        self.assertIn(b"status=uncertain", second)
        self.assertIsNone(receiver.poll())
        self.stop_process(receiver)

        args = self.dispatch_receiver_args()
        for _ in range(2):
            cut = subprocess.run(args, cwd=ROOT, env=self.env,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 timeout=240, check=False)
            self.assertEqual(cut.returncode, 0, cut.stdout + cut.stderr)
            self.assertIn(b"status=uncertain", cut.stdout)
        stranded = subprocess.run(args, cwd=ROOT, env=self.env,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  timeout=240, check=False)
        self.assertEqual(stranded.returncode, 0, stranded.stderr)
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
        self.assertEqual(unknown.returncode, 1, unknown.stdout + unknown.stderr)
        self.assertIn(b"resume refused", unknown.stdout)
        self.assertIn(b"reason=no-row", unknown.stdout)
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), before)

        resumed = self.resume_receiver(arrival)
        self.assertEqual(resumed.returncode, 0, resumed.stdout + resumed.stderr)
        self.assertIn(b"status=resumed", resumed.stdout)
        self.assertEqual(len(tuple(journal.glob("*.fnb"))), before + 1)
        again = self.resume_receiver(arrival)
        self.assertEqual(again.returncode, 1, again.stdout)
        self.assertIn(b"reason=not-attempted", again.stdout)

        self.relay.route(peer_port)
        offered = subprocess.run(args, cwd=ROOT, env=self.env,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 timeout=240, check=False)
        self.assertEqual(offered.returncode, 0, offered.stderr)
        self.assertIn(b"BP forwarding attempt durable", offered.stdout)
        self.assertIn(b"status=sent", offered.stdout)
        self.stop_process(peer)
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
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-fnbs-deletion-codec")')
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
                payload = run_store.acl2_octets(bridge.call(form))
                if payload:
                    payloads.append(payload)
            return payloads
        finally:
            bridge.close()

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

    def test_deletion_report_intent_recovers_and_observation_does_not_release(self):
        receiver, port = self.start_node(
            True, extra_env={"FN_BP_NODE_TEST_PAUSE_AFTER_KIND_FIVE": "1"},
        )
        sent = self.send_deletion_request(port)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.wait_for_output(receiver, b"BP NODE KIND5 DURABLE", timeout=120)
        receiver.kill()
        receiver.wait(timeout=15)
        time.sleep(1.8)

        # The kind-10 record is durable before the outbound sequence/job cut.
        env = dict(self.env)
        env["FN_BP_NODE_TEST_PAUSE_AFTER_KIND_TEN"] = "1"
        candidate = subprocess.Popen(
            self.dispatch_receiver_args(reports=True), cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0,
        )
        self.addCleanup(self.stop_process, candidate)
        self.wait_for_output(candidate, b"BP NODE KIND10 DURABLE", timeout=120)
        candidate.kill()
        candidate.wait(timeout=15)
        self.assertEqual(self.receiver_counts()[1], 0)

        report_payloads = self.acl2_lifecycle_payloads(
            self.receiver_journal, 10)
        self.assertEqual(len(report_payloads), 1)
        report_payload = report_payloads[0]
        self.assertLessEqual(len(report_payload), 4096)
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-status-report")')
            literal = bridge.literal(report_payload)
            self.assertEqual(
                run_store.acl2_result(bridge.call(
                    "(let ((parsed (fn-bpn-report-decode '" + literal + "))) "
                    "(and (fn-cbor-result-okp parsed) "
                    "(equal (fn-bpn-report-encode "
                    "(fn-cbor-result-value parsed)) '" + literal + ")))"
                )), b"T")
        finally:
            bridge.close()

        restarted = self.dispatch_receiver(reports=True)
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertIn(b"BP queue accepted", restarted.stdout)
        self.assertEqual(self.receiver_counts()[1], 0)
        frontier = self.receiver_journal / "sequence" / "frontier.fnb"
        frontier_bytes = frontier.read_bytes()
        lifecycle = self.receiver_journal / "lifecycle"
        durable_frames = {
            frame.name: frame.read_bytes() for frame in lifecycle.glob("*.fnb")
        }
        repeated = self.dispatch_receiver(reports=True)
        self.assertEqual(repeated.returncode, 0, repeated.stderr)
        self.assertEqual(frontier.read_bytes(), frontier_bytes)
        self.assertEqual(
            {frame.name: frame.read_bytes() for frame in lifecycle.glob("*.fnb")},
            durable_frames,
        )
        self.assertEqual(
            self.acl2_lifecycle_payloads(self.receiver_journal, 10),
            [report_payload],
        )

        sender, port = self.start_node(False, once=False)
        self.relay.route(port, cut_next=True)
        interrupted = self.tick_receiver()
        self.assertEqual(interrupted.returncode, 3, interrupted.stderr)
        self.assertIn(b"reason=uncertain", interrupted.stdout)
        self.stop_process(sender)
        pinned = self.sender_status()
        self.assertEqual(pinned.returncode, 0, pinned.stderr)
        self.assertIn(b"pinned=yes", pinned.stdout)

        sender, port = self.start_node(False, once=False)
        self.relay.route(port)
        delivered = self.tick_receiver()
        self.assertEqual(delivered.returncode, 0, delivered.stderr)
        self.wait_for_output(sender, b"BP status report observed", timeout=120)
        self.assertIn(
            report_payload,
            self.acl2_lifecycle_payloads(self.sender_journal, 5),
        )
        self.stop_process(sender)
        self.assertIn(b"pinned=yes", self.sender_status().stdout)
        self.assertIn(b"pinned=yes", self.unrelated_status().stdout)



if __name__ == "__main__":
    unittest.main()
