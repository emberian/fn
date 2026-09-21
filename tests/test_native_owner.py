"""Executable native owner slice: writable NNTP POST with no Python process."""
import os
from pathlib import Path
import select
import socket
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


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
                "native host image missing: {} (tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-owner-")
        self.addCleanup(self.temporary.cleanup)
        self.store = Path(self.temporary.name) / "store"
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment(), timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())

    def start_owner(self, once=True):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "owner", "run", str(self.store),
             "0", "1" if once else "0", "8"], cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=environment())
        ready = select.select([process.stdout], [], [], 180)[0]
        self.assertTrue(ready, "native owner did not announce its port")
        line = process.stdout.readline()
        if not line.startswith(b"LISTENING "):
            self.fail("native owner failed: {} {}".format(
                line, process.stderr.read().decode("utf-8", "replace")))
        return process, int(line.split()[1])

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

    def test_post_is_committed_and_readable_after_owner_exit(self):
        process, port = self.start_owner()
        article = (b"From: sender@example.invalid\r\n"
                   b"Newsgroups: fn.test\r\n"
                   b"Subject: native owner\r\n"
                   b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
                   b"Message-ID: <native-owner@example.invalid>\r\n"
                   b"\r\n" +
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
        self.assertEqual(inspected.stdout, article)


if __name__ == "__main__":
    unittest.main()
