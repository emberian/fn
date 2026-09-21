"""Developer-image owner diagnostic: writable NNTP POST with no Python peer."""
import os
from pathlib import Path
import select
import socket
import struct
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


class NativeOwnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(
                "developer native image missing: {} "
                "(FN_NATIVE_PROFILE=developer tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-owner-")
        self.addCleanup(self.temporary.cleanup)
        self.store = Path(self.temporary.name) / "store"
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())

    def start_owner(self, once=True, fault=None):
        command = [str(IMAGE), "--fn", "owner", "run", str(self.store),
                   "0", "1" if once else "0", "8"]
        if fault is not None:
            command.append(fault)
        process = subprocess.Popen(
            command, cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=environment())
        ready = select.select([process.stdout], [], [], 180)[0]
        self.assertTrue(ready, "native owner did not announce its port")
        line = process.stdout.readline()
        if not line.startswith(b"LISTENING "):
            self.fail("native owner failed: {} {}".format(
                line, process.stderr.read().decode("utf-8", "replace")))
        return process, int(line.split()[1])

    def connect_owner(self, port):
        client = socket.create_connection(("127.0.0.1", port), timeout=30)
        self.addCleanup(client.close)
        stream = client.makefile("rwb", buffering=0)
        self.addCleanup(stream.close)
        self.assertTrue(stream.readline().startswith(b"200 "))
        return client, stream

    def assert_live_writer_and_reader(self, port, writer, reader, message_id):
        article = self.article(message_id, b"surviving native owner body\r\n")
        writer.write(b"POST\r\n")
        self.assertTrue(writer.readline().startswith(b"340 "))
        writer.write(article + b".\r\n")
        self.assertTrue(writer.readline().startswith(b"240 "))

        # This connection predates the post and deliberately retains its
        # pinned archive snapshot.  Prove it is still served without asking
        # that old snapshot to expose a later commit.
        reader.write(b"CAPABILITIES\r\n")
        self.assertTrue(reader.readline().startswith(b"101 "))
        while True:
            line = reader.readline()
            self.assertNotEqual(line, b"", "owner closed the surviving reader")
            if line == b".\r\n":
                break

        # A fresh reader pins the post-commit archive and proves the healthy
        # writer's article became visible without restarting the service.
        _, current_reader = self.connect_owner(port)
        current_reader.write(b"GROUP fn.test\r\n")
        self.assertTrue(current_reader.readline().startswith(b"211 "))
        current_reader.write(b"ARTICLE " + message_id + b"\r\n")
        self.assertTrue(current_reader.readline().startswith(b"220 "))
        received = bytearray()
        while True:
            line = current_reader.readline()
            self.assertNotEqual(line, b"", "owner closed the current reader")
            if line == b".\r\n":
                break
            received.extend(line)
        self.assertIn(b"Message-ID: " + message_id + b"\r\n", received)
        self.assertIn(b"surviving native owner body\r\n", received)

    @staticmethod
    def article(message_id, body=b"native owner body\r\n"):
        return (b"From: sender@example.invalid\r\n"
                b"Newsgroups: fn.test\r\n"
                b"Subject: native owner\r\n"
                b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
                b"Message-ID: " + message_id + b"\r\n\r\n" + body)

    def test_client_disconnect_is_not_a_global_owner_fault(self):
        process, port = self.start_owner(once=False)
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                self.assertTrue(client.makefile("rb", buffering=0).readline().startswith(b"200 "))
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertIsNone(process.poll(), "owner stopped after an ordinary disconnect")
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

    def test_reset_peer_does_not_stop_concurrent_writer_or_reader(self):
        process, port = self.start_owner(once=False)
        resetter, reset_stream = self.connect_owner(port)
        _, reader = self.connect_owner(port)
        _, writer = self.connect_owner(port)
        try:
            # Force an attributable transport reset.  The peer owns this
            # socket and no shared owner transition is in progress.
            resetter.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER,
                                struct.pack("ii", 1, 0))
            reset_stream.close()
            resetter.close()
            time.sleep(0.1)
            self.assert_live_writer_and_reader(
                port, writer, reader, b"<after-native-reset@example.invalid>")
            self.assertIsNone(process.poll(), "peer reset stopped the owner")
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

    def test_local_handler_fault_uses_core_fault_and_preserves_other_clients(self):
        process, port = self.start_owner(once=False, fault="connectionhandler")
        _, faulted = self.connect_owner(port)
        _, reader = self.connect_owner(port)
        _, writer = self.connect_owner(port)
        try:
            faulted.write(b"CAPABILITIES\r\n")
            self.assertEqual(
                faulted.readline(),
                b"403 internal fault; this connection is closed and the server continues\r\n")
            self.assert_live_writer_and_reader(
                port, writer, reader, b"<after-native-handler-fault@example.invalid>")
            self.assertIsNone(process.poll(), "local handler fault stopped the owner")
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

    def test_invalid_complete_feed_evidence_is_process_fault(self):
        feed = self.store / "feed"
        feed.mkdir()
        (feed / "bad.fnfd").write_bytes(b"not-a-valid-complete-feed-frame")
        result = subprocess.run(
            [str(IMAGE), "--fn", "owner", "run", str(self.store),
             "0", "1", "8"], cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=environment(), timeout=180, check=False)
        self.assertEqual(result.returncode, 4, result.stderr.decode())
        self.assertIn(b"invalid complete FNFD evidence", result.stderr)

    def test_empty_v1_feed_namespace_is_preserved_as_conflicting_evidence(self):
        (self.store / "feed" / "v1").mkdir(parents=True)
        result = subprocess.run(
            [str(IMAGE), "--fn", "owner", "run", str(self.store),
             "0", "1", "8"], cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=environment(), timeout=180, check=False)
        self.assertEqual(result.returncode, 4, result.stderr.decode())
        self.assertIn(b"empty FNFD v1 namespace", result.stderr)
        self.assertTrue((self.store / "feed" / "v1").is_dir())

    def test_two_client_uncertainty_fences_before_later_mutation(self):
        process, port = self.start_owner(once=False, fault="postpublish")
        first = socket.create_connection(("127.0.0.1", port), timeout=30)
        second = socket.create_connection(("127.0.0.1", port), timeout=30)
        self.addCleanup(first.close)
        self.addCleanup(second.close)
        one = first.makefile("rwb", buffering=0)
        two = second.makefile("rwb", buffering=0)
        try:
            self.assertTrue(one.readline().startswith(b"200 "))
            self.assertTrue(two.readline().startswith(b"200 "))
            one.write(b"POST\r\n")
            self.assertTrue(one.readline().startswith(b"340 "))
            one.write(self.article(b"<uncertain-native-owner@example.invalid>")
                      + b".\r\n")
            try:
                two.write(b"POST\r\n")
            except (BrokenPipeError, ConnectionResetError, OSError):
                pass
            self.assertEqual(process.wait(timeout=60), 3,
                             process.stderr.read().decode("utf-8", "replace"))
            # The already-open second session was shut down by the fence; it
            # cannot enter fn-owner-chunk after the ambiguous publication.
            try:
                later = two.readline()
            except (BrokenPipeError, ConnectionResetError, OSError):
                later = b""
            self.assertFalse(later.startswith(b"340 "), later)
        finally:
            one.close()
            two.close()
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

        committed = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "inspect",
             "<uncertain-native-owner@example.invalid>"], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(committed.returncode, 0, committed.stderr.decode())
        missing = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "inspect",
             "<later-native-owner@example.invalid>"], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertNotEqual(missing.returncode, 0)

    def test_uncertain_commit_reconciles_its_durable_feed_intent_on_restart(self):
        configured = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.store),
             "peer", "add", "sink", "--path-identity", "sink.example.invalid",
             "--nntp", "127.0.0.1:9", "--outbound-groups", "fn.*",
             "--source-address", "127.0.0.1"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())

        msgid = b"<native-owner-feed-recovery@example.invalid>"
        article = self.article(msgid)
        process, port = self.start_owner(once=False, fault="postpublish")
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"340 "))
                stream.write(article + b".\r\n")
            self.assertEqual(process.wait(timeout=60), 3,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

        journal = self.store / "feed" / "sink.fnfd"
        self.assertTrue(journal.is_file())
        intent_size = journal.stat().st_size
        self.assertGreater(intent_size, 0)

        # Opening the same native owner resolves the retained intent against
        # the physically committed Store record before it serves a client.
        restarted, port = self.start_owner()
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(restarted.wait(timeout=60), 0,
                             restarted.stderr.read().decode("utf-8", "replace"))
        finally:
            if restarted.poll() is None:
                restarted.terminate()
                restarted.wait(timeout=10)
            restarted.stdout.close()
            restarted.stderr.close()
        self.assertGreater(journal.stat().st_size, intent_size)

        inspected = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "inspect",
             msgid.decode("ascii")], cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=environment(), timeout=180, check=False)
        self.assertEqual(inspected.returncode, 0, inspected.stderr.decode())
        self.assertTrue(inspected.stdout.endswith(article), inspected.stdout[-80:])

    def test_post_is_committed_and_readable_after_owner_exit(self):
        process, port = self.start_owner()
        article = self.article(
            b"<native-owner@example.invalid>",
            (b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ\r\n"
             * 145))
        self.assertGreater(len(article), 8192)
        self.assertLessEqual(len(article), 32768)
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"340 "))
                stream.write(article + b".\r\n")
                self.assertTrue(stream.readline().startswith(b"240 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(process.wait(timeout=60), 0,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()
        inspected = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "inspect",
             "<native-owner@example.invalid>"], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(inspected.returncode, 0, inspected.stderr.decode())
        # The injection transition prepends the ACL2-produced Path field.  The
        # accepted source article, including the 9 KiB body, remains exact.
        self.assertTrue(inspected.stdout.startswith(
            b"Path: fn.example.invalid!not-for-mail\r\n"), inspected.stdout[:80])
        self.assertTrue(inspected.stdout.endswith(article), inspected.stdout[-80:])


if __name__ == "__main__":
    unittest.main()
