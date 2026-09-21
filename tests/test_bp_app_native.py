"""Two native endpoints exercise BP request -> owner Store -> FNRJ receipt."""

import os
from pathlib import Path
import select
import shutil
import subprocess
import tempfile
import time
import unittest

from tools import run_bp_ingress, run_store


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


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

    def invoke(self, *args, env=None, timeout=180):
        return subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=env or self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False,
        )

    def start_receiver(self, pause=False):
        env = dict(self.env)
        if pause:
            env["FN_BP_APP_TEST_PAUSE_AFTER_DECISION"] = "1"
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "bp-app", "receive", "0",
             str(self.receiver_spool), str(self.store), str(self.receipts),
             "dtn://receiver/", "dtn://sender/", "dtn://receiver/",
             "native-policy", "dtn://receiver/", "1", "8"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0,
        )
        ready = select.select([process.stdout], [], [], 180)[0]
        self.assertTrue(ready, "BP application receiver did not announce")
        line = process.stdout.readline()
        if not line.startswith(b"BP APP LISTENING "):
            self.fail(
                f"receiver failed: {line!r} "
                f"{process.stderr.read().decode('utf-8', 'replace')}"
            )
        return process, int(line.rsplit(b" ", 1)[1])

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
        provenance = self.invoke(
            "store", self.store, "inspect", self.msgid.decode("ascii"),
            "--provenance",
        )
        self.assertEqual(provenance.returncode, 0, provenance.stderr.decode())
        self.assertIn(b"kind=bp", provenance.stdout.lower())
        self.assertIn(b"node=dtn://receiver/", provenance.stdout)

        result_files = sorted(
            (self.sender_spool / "receive-evidence").glob("*.accepted")
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
