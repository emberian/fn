"""Two native endpoints exercise BP request -> owner Store -> FNRJ receipt."""

import os
from pathlib import Path
import select
import shutil
import socket
import subprocess
import tempfile
import time
import unittest

from tools import run_bp_ingress, run_store


from tests.native_process import stop_and_diagnostics, wait_for_announcement

# specs/host.md "BP run classes" (books/bp-run-class.lisp, PRF-131): a
# connection lost after it existed is exit 6 (connection-local: the job stays
# and is re-offered; no recovery); exit 3 stays the fence.
LOST = 6


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


class NativeBpApplicationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(f"native host image missing: {IMAGE}")

    def setUp(self):
        self.temp = Path(tempfile.mkdtemp(prefix="fn-native-bp-app-"))
        self.addCleanup(shutil.rmtree, self.temp)
        self.store = self.temp / "store"
        self.receiver_spool = self.temp / "receiver-spool"
        self.sender_spool = self.temp / "sender-spool"
        self.receipts = self.temp / "receipts"
        self.request_path = self.temp / "request.adu"
        self.env = environment()
        initialized = self.invoke("store", self.store, "init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.enroll_sender_boundary()

        self.msgid = b"<native-bp-app@example.invalid>"
        self.article = (
            b"From: sender@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: native BP application\r\n"
            b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
            b"Message-ID: " + self.msgid + b"\r\n\r\nbody over BP\r\n"
        )
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-adu")')
            extracted = bridge.extract_message_id(self.article)
            self.assertEqual(extracted, self.msgid)
            _archive, subject, _provenance = run_store.metadata(
                self.msgid, self.article)

            def text(value):
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = [
                b"work-native-bp", subject, b"dtn://sender/",
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

    def enroll_sender_boundary(self):
        """Admit dtn://sender/ as a BP boundary principal of the receiving Store.

        The receiver plans a request as transit from an admitted ingress
        principal (books/bp-transit-join.lisp `fn-bpaj-ingress-peer'): with
        no boundary for the sender's EID the plan is `(:refused
        :no-principal)'.  This is the enrollment the fragment and node
        fixtures carry (tests/test_bp_fragment_node_native.py).  Admission
        (books/bp-session-admission.lisp) binds the boundary to the port
        the receiver listens on, so every receiver listens on `self.port'.
        """
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as reservation:
            reservation.bind(("127.0.0.1", 0))
            self.port = reservation.getsockname()[1]
        config = self.temp / "receiver-fn.toml"
        config.write_text(f'[store]\npath = "{self.store}"\n', encoding="ascii")
        policy = self.invoke("operator", config, "policy", "set",
                             "path-identity", "receiver.bp.gate.invalid")
        self.assertEqual(policy.returncode, 0, policy.stderr.decode())
        trusted = self.invoke(
            "operator", config, "bp-boundary", "add", "sender-boundary",
            "sender.bp.gate.invalid", "dtn://sender/", self.port,
            "fn.test", 32768, 16)
        self.assertEqual(trusted.returncode, 0, trusted.stderr.decode())

    def invoke(self, *args, env=None, timeout=180):
        return subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False,
        )

    def start_receiver(self, pause=False, fail_decision_namespace=False,
                       port=None):
        port = self.port if port is None else port
        env = dict(self.env)
        if pause:
            env["FN_BP_APP_TEST_PAUSE_AFTER_DECISION"] = "1"
        if fail_decision_namespace:
            env["FN_APP_JOURNAL_TEST_FAIL_RECEIPT_DECISION_NAMESPACE"] = "1"
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "bp-app", "receive", str(port),
             str(self.receiver_spool), str(self.store), str(self.receipts),
             "dtn://receiver/", "dtn://sender/", "dtn://receiver/",
             "native-policy", "dtn://receiver/", "1", "8"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0,
        )
        line = wait_for_announcement(process, b"BP APP LISTENING ")
        if not line.startswith(b"BP APP LISTENING "):
            self.fail(
                f"receiver failed: {line!r} "
                f"{stop_and_diagnostics(process)}"
            )
        actual_port = int(line.rsplit(b" ", 1)[1])
        if port:
            self.assertEqual(actual_port, port)
        return process, actual_port

    def start_sender(self, port):
        return subprocess.Popen(
            [str(IMAGE), "--fn", "bp", "send", "127.0.0.1", str(port),
             str(self.request_path), str(self.sender_spool), "dtn://sender/",
             "dtn://receiver/", "3600000", "2", "32", "1048576", "1",
             "-", "0"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def recovered_counts(self):
        store, bridge, records = run_bp_ingress.open_live_bp_store(
            self.store, False)
        try:
            return len(records), bridge.article_count(), bridge.pin_count()
        finally:
            bridge.close()
            store.close()

    def recovered_provenance(self):
        store, bridge, _records = run_bp_ingress.open_live_bp_store(
            self.store, False)
        try:
            return bridge.prov_for_msgid(self.msgid)
        finally:
            bridge.close()
            store.close()

    def prepare_sender_obligation(self):
        sender_store = self.temp / "sender-store"
        workflow = self.temp / "sender-workflow"
        initialized = self.invoke("store", sender_store, "init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        payload = self.temp / "sender-article"
        payload.write_bytes(self.article)
        posted = self.invoke(
            "store", sender_store, "post", self.msgid.decode("ascii"),
            payload, "-", "-", "fn.test",
        )
        self.assertEqual(posted.returncode, 0, posted.stderr.decode())
        workflow_init = self.invoke(
            "app-journal", "workflow-init", sender_store, workflow,
            "dtn://sender/", "dtn://receiver/", "native-policy",
            "dtn://receiver/", "3600000", "origin-native", "wire-auth",
        )
        self.assertEqual(workflow_init.returncode, 0, workflow_init.stderr.decode())
        enqueued = self.invoke(
            "app-journal", "workflow-enqueue", sender_store, workflow,
            "1", "0", "work-native-bp", self.msgid.decode("ascii"),
            "forward-native-bp", "dtn://receiver/", "native-policy",
            "terms-native",
        )
        self.assertEqual(enqueued.returncode, 0, enqueued.stderr.decode())
        undertaken = self.invoke(
            "bp-obligation", "undertake", sender_store, workflow,
            "work-native-bp", "3",
        )
        self.assertEqual(undertaken.returncode, 0, undertaken.stderr.decode())
        return sender_store, workflow

    def test_application_receipt_releases_forward_pin_only_after_durable_record(self):
        sender_store, workflow = self.prepare_sender_obligation()
        before = self.invoke(
            "bp-obligation", "status", sender_store, workflow, "work-native-bp",
        )
        self.assertEqual(before.returncode, 0, before.stderr.decode())
        self.assertIn(b"pinned=yes", before.stdout)

        receiver, port = self.start_receiver()
        sender = self.start_sender(port)
        try:
            sender_out, sender_err = sender.communicate(timeout=180)
            receiver_out, receiver_err = receiver.communicate(timeout=180)
            self.assertEqual(sender.returncode, 0, sender_err.decode())
            self.assertEqual(receiver.returncode, 0, receiver_err.decode())
            self.assertIn(b"BP application accepted", receiver_out)
            self.assertIn(b"BP summary accepted=1", sender_out)
        finally:
            if receiver.poll() is None:
                receiver.kill()
                receiver.wait(timeout=10)
            if sender.poll() is None:
                sender.kill()
                sender.wait(timeout=10)
            receiver.stdout.close()
            receiver.stderr.close()
            sender.stdout.close()
            sender.stderr.close()

        receipts = sorted((self.sender_spool / "receive-evidence").glob("*.adu"))
        self.assertEqual(len(receipts), 1)
        fault_env = dict(self.env)
        fault_env["FN_APP_JOURNAL_TEST_FAIL_RELEASE_NAMESPACE"] = "1"
        uncertain = self.invoke(
            "bp-obligation", "receipt", sender_store, workflow, receipts[0],
            "2", "0", "trusted-local-observation-v0", env=fault_env,
        )
        self.assertEqual(uncertain.returncode, 3, uncertain.stderr.decode())
        self.assertIn(b"publication is uncertain", uncertain.stderr)

        recovered = self.invoke(
            "bp-obligation", "status", sender_store, workflow, "work-native-bp",
        )
        self.assertEqual(recovered.returncode, 0, recovered.stderr.decode())
        self.assertIn(b"status=receipted", recovered.stdout)
        self.assertIn(b"pinned=no", recovered.stdout)

    def test_unadmitted_channel_is_refused_with_the_planner_reason(self):
        """A receiver on a port no boundary names admits no principal.

        The planner refuses `:no-principal'; the receiver's line is ACL2's
        (books/owner-log.lisp fn-olog-bp-app-refusal-line) and carries that
        reason; the one-shot sender ends its session on the refusal and exits
        with the refused code instead of awaiting a receipt that cannot come.
        """
        receiver, port = self.start_receiver(port=0)
        self.assertNotEqual(port, self.port)
        sender = self.start_sender(port)
        try:
            sender_out, sender_err = sender.communicate(timeout=180)
            receiver_out, receiver_err = receiver.communicate(timeout=180)
            self.assertEqual(sender.returncode, 1, sender_err.decode())
            self.assertEqual(receiver.returncode, 1, receiver_err.decode())
            self.assertIn(
                b"refused bp-application xfer=0 result=refused "
                b"reason=no-principal\n", receiver_err)
            self.assertIn(b"BP summary accepted=0", sender_out)
            self.assertNotIn(b"BP application accepted", receiver_out)
        finally:
            for process in (receiver, sender):
                if process.poll() is None:
                    process.kill()
                    process.wait(timeout=10)
                process.stdout.close()
                process.stderr.close()
        self.assertEqual(self.recovered_counts()[1], 0)

    def test_unsupported_receipt_profile_refuses_before_file_read(self):
        sender_store, workflow = self.prepare_sender_obligation()
        missing_receipt = self.temp / "missing-untrusted-receipt.adu"
        before = {p.name: p.read_bytes()
                  for p in (workflow / "records").glob("*.wf")}
        refused = self.invoke(
            "bp-obligation", "receipt", sender_store, workflow,
            missing_receipt, "2", "0", "unsigned-lab",
        )
        self.assertEqual(refused.returncode, 1, refused.stderr.decode())
        self.assertIn(b"authentication profile is unsupported", refused.stderr)
        self.assertEqual(before, {p.name: p.read_bytes()
                                  for p in (workflow / "records").glob("*.wf")})
        status = self.invoke(
            "bp-obligation", "status", sender_store, workflow,
            "work-native-bp",
        )
        self.assertEqual(status.returncode, 0, status.stderr.decode())
        self.assertIn(b"pinned=yes", status.stdout)

    def test_lost_receipt_restart_replays_without_second_acceptance(self):
        receiver, port = self.start_receiver(pause=True)
        sender = self.start_sender(port)
        try:
            deadline = time.time() + 180
            saw_decision = False
            while time.time() < deadline:
                ready = select.select([receiver.stdout], [], [], 1)[0]
                if ready:
                    line = receiver.stdout.readline()
                    if b"BP APP DECISION DURABLE" in line:
                        saw_decision = True
                        break
                if receiver.poll() is not None:
                    break
            if not saw_decision:
                receiver.kill()
                receiver.wait(timeout=30)
                self.fail(receiver.stderr.read().decode("utf-8", "replace"))
            receiver.kill()
            receiver.wait(timeout=30)
            sender.wait(timeout=60)
        finally:
            if receiver.poll() is None:
                receiver.kill()
                receiver.wait(timeout=10)
            if sender.poll() is None:
                sender.kill()
                sender.wait(timeout=10)
            receiver.stdout.close()
            receiver.stderr.close()
            sender.stdout.close()
            sender.stderr.close()

        before = self.recovered_counts()
        self.assertEqual(before, (1, 1, 1))

        receiver2, port2 = self.start_receiver()
        sender2 = self.start_sender(port2)
        try:
            sender_out, sender_err = sender2.communicate(timeout=180)
            receiver_out, receiver_err = receiver2.communicate(timeout=180)
            self.assertEqual(sender2.returncode, 0, sender_err.decode())
            self.assertEqual(receiver2.returncode, 0, receiver_err.decode())
            self.assertIn(b"BP application accepted", receiver_out)
            self.assertIn(b"BP summary accepted=1", sender_out)
        finally:
            if receiver2.poll() is None:
                receiver2.kill()
                receiver2.wait(timeout=10)
            if sender2.poll() is None:
                sender2.kill()
                sender2.wait(timeout=10)
            receiver2.stdout.close()
            receiver2.stderr.close()
            sender2.stdout.close()
            sender2.stderr.close()

        self.assertEqual(self.recovered_counts(), before)
        inspected = self.invoke("store", self.store, "inspect",
                                self.msgid.decode("ascii"))
        self.assertEqual(inspected.returncode, 0, inspected.stderr.decode())
        self.assertEqual(inspected.stdout, self.article)
        # A BP request is peer transit (specs/bp-node-machine.md, the
        # :request-transit-intent join): the Store record's provenance is
        # the one fn-peer-injection-arguments gives, naming the principal
        # the channel admitted.  The `bp-receive node=... label=...' form is
        # the historical control-submission binding, which a request only
        # took while the ingress was dropped and no principal was admitted.
        provenance = self.recovered_provenance()
        self.assertIn(b"peer-transit:sender-boundary", provenance)
        self.assertNotIn(b"bp-receive", provenance)

        result_files = sorted(
            (self.sender_spool / "receive-evidence").glob("*.adu")
        )
        self.assertEqual(len(result_files), 1)
        replay = self.invoke(
            "app-journal", "receipt-replay", self.store, self.receipts,
            self.request_path,
        )
        self.assertEqual(replay.returncode, 0, replay.stderr.decode())
        receipt = result_files[0].read_bytes()
        self.assertIn(("hex=" + receipt.hex()).encode("ascii"), replay.stdout)

    def test_visible_decision_namespace_eio_fences_before_receipt(self):
        receiver, port = self.start_receiver(fail_decision_namespace=True)
        sender = self.start_sender(port)
        try:
            sender_out, sender_err = sender.communicate(timeout=180)
            receiver_out, receiver_err = receiver.communicate(timeout=180)
            self.assertEqual(receiver.returncode, 3, receiver_err.decode())
            self.assertEqual(sender.returncode, LOST, sender_err.decode())
            self.assertNotIn(b"BP application accepted", receiver_out)
        finally:
            if receiver.poll() is None:
                receiver.kill()
                receiver.wait(timeout=10)
            if sender.poll() is None:
                sender.kill()
                sender.wait(timeout=10)
            receiver.stdout.close()
            receiver.stderr.close()
            sender.stdout.close()
            sender.stderr.close()

        # link(2) succeeded before the injected directory barrier EIO, so the
        # exact decision is visible even though this process cannot call it
        # durable or author a receipt.
        records = sorted((self.receipts / "records").glob("*.rj"))
        self.assertEqual(len(records), 5)
        self.assertGreater(records[-1].stat().st_size, 0)
        self.assertEqual(
            list((self.sender_spool / "receive-evidence").glob("*.adu")), []
        )
        before = self.recovered_counts()
        self.assertEqual(before, (1, 1, 1))

        # Opening the second native receiver repeats the journal namespace
        # barriers, replays the visible valid decision, and returns its receipt
        # without a second Store acceptance or retention pin.
        receiver2, port2 = self.start_receiver()
        sender2 = self.start_sender(port2)
        try:
            sender_out, sender_err = sender2.communicate(timeout=180)
            receiver_out, receiver_err = receiver2.communicate(timeout=180)
            self.assertEqual(sender2.returncode, 0, sender_err.decode())
            self.assertEqual(receiver2.returncode, 0, receiver_err.decode())
            self.assertIn(b"BP application accepted", receiver_out)
            self.assertIn(b"BP summary accepted=1", sender_out)
        finally:
            if receiver2.poll() is None:
                receiver2.kill()
                receiver2.wait(timeout=10)
            if sender2.poll() is None:
                sender2.kill()
                sender2.wait(timeout=10)
            receiver2.stdout.close()
            receiver2.stderr.close()
            sender2.stdout.close()
            sender2.stderr.close()

        self.assertEqual(self.recovered_counts(), before)
        result_files = sorted(
            (self.sender_spool / "receive-evidence").glob("*.adu")
        )
        self.assertEqual(len(result_files), 1)
        replay = self.invoke(
            "app-journal", "receipt-replay", self.store, self.receipts,
            self.request_path,
        )
        self.assertEqual(replay.returncode, 0, replay.stderr.decode())
        receipt = result_files[0].read_bytes()
        self.assertIn(("hex=" + receipt.hex()).encode("ascii"), replay.stdout)


if __name__ == "__main__":
    unittest.main()
