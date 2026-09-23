"""Saved-image witness for pinned NNTP Message-ID retrieval.

The Python test drives only public operator and NNTP interfaces.  The index,
archive and their correspondence are ACL2 decisions in the called owner path.
Run only against an image built from the integrated T10/T17 source:
FN_RUN_NATIVE_READER_INDEX=1 FN_NATIVE_HOST=... python3 -m unittest
tests.test_native_reader_index -v
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement, stop_and_diagnostics


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(os.environ.get("FN_RUN_NATIVE_READER_INDEX") == "1",
                     "set FN_RUN_NATIVE_READER_INDEX=1 for the integrated saved-image gate")
@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "an executable FN_NATIVE_HOST is required")
class NativeReaderIndexTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fn-reader-index-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.run_native("operator", self.config, "init", "fn.test")

    def run_native(self, *words):
        result = subprocess.run([str(IMAGE), "--fn", *map(str, words)], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=180, check=False)
        self.assertEqual(result.returncode, 0,
                         result.stderr.decode("utf-8", "replace"))
        return result

    def start_owner(self):
        proc = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(self.reap, proc)
        wait_for_announcement(proc, b"LISTENING ")
        return proc

    @staticmethod
    def reap(proc):
        if proc.poll() is None:
            proc.kill()
            proc.wait(timeout=10)
        for stream in (proc.stdout, proc.stderr):
            if stream and not stream.closed:
                stream.close()

    def stop_owner(self, proc):
        diagnostic = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostic)

    def reader(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=15)
        sock.settimeout(15)
        self.addCleanup(sock.close)
        stream = sock.makefile("rb", buffering=0)
        self.addCleanup(stream.close)
        greeting = stream.readline(4096)
        self.assertTrue(greeting.startswith(b"200 "), greeting)
        return sock, stream

    def command(self, reader, line, multiline=False):
        sock, stream = reader
        sock.sendall(line.encode("ascii") + b"\r\n")
        status = stream.readline(4096)
        self.assertTrue(status, "missing NNTP reply to " + line)
        rows = []
        if multiline and status[:1] == b"2":
            while True:
                row = stream.readline(32769)
                self.assertTrue(row, "unterminated reply to " + line)
                if row == b".\r\n":
                    break
                rows.append(row)
                self.assertLessEqual(len(rows), 256)
        return status, rows

    def post(self, msgid, ordinal):
        source = (
            b"From: reader@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: pinned reader " + str(ordinal).encode("ascii") + b"\r\n"
            b"Message-ID: " + msgid.encode("ascii") +
            b"\r\n\r\nexact reader source\r\n")
        path = self.root / ("post-{}.eml".format(ordinal))
        path.write_bytes(source)
        self.run_native("operator", self.config, "post", "--message-id", msgid,
                        "--payload", path, "--group", "fn.test")
        return source

    def test_pinned_archive_and_index_through_public_reader(self):
        first = "<reader-index-first@example.invalid>"
        second = "<reader-index-second@example.invalid>"
        absent = "<reader-index-missing@example.invalid>"
        owner = self.start_owner()
        old = self.reader()
        self.assertEqual(self.command(old, "STAT " + first)[0],
                         b"430 no article with that message-id\r\n")
        first_source = self.post(first, 1)
        middle = self.reader()
        self.assertEqual(self.command(old, "STAT " + first)[0],
                         b"430 no article with that message-id\r\n")
        self.assertIn(first.encode(), self.command(middle, "STAT " + first)[0])
        self.assertEqual(self.command(middle, "STAT " + second)[0],
                         b"430 no article with that message-id\r\n")
        second_source = self.post(second, 2)
        fresh = self.reader()
        self.assertEqual(self.command(old, "STAT " + second)[0],
                         b"430 no article with that message-id\r\n")
        self.assertEqual(self.command(middle, "STAT " + second)[0],
                         b"430 no article with that message-id\r\n")
        self.assertIn(second.encode(), self.command(fresh, "STAT " + second)[0])
        self.assertEqual(self.command(fresh, "STAT " + absent)[0],
                         b"430 no article with that message-id\r\n")

        for msgid, source in ((first, first_source), (second, second_source)):
            status, rows = self.command(fresh, "ARTICLE " + msgid, True)
            self.assertTrue(status.startswith(b"220 "), status)
            self.assertTrue(b"".join(rows).endswith(source))
            status, rows = self.command(fresh, "HEAD " + msgid, True)
            self.assertTrue(status.startswith(b"221 "), status)
            self.assertIn(b"Message-ID: " + msgid.encode() + b"\r\n", rows)
            status, rows = self.command(fresh, "BODY " + msgid, True)
            self.assertTrue(status.startswith(b"222 "), status)
            self.assertEqual(rows, [b"exact reader source\r\n"])
            status, rows = self.command(fresh, "HDR :fn-verified " + msgid, True)
            self.assertEqual(status, b"225 headers follow\r\n")
            self.assertEqual(rows, [b"0 absent no-record\r\n"])

        # Independent clients exercise the same called path under bounded
        # overlap.  This records responsiveness, not an asymptotic claim.
        def batch(_):
            reader = self.reader()
            try:
                observations = []
                for _ in range(12):
                    observations.append(self.command(reader, "STAT " + first)[0])
                    observations.append(self.command(reader, "STAT " + absent)[0])
                return observations
            finally:
                reader[1].close()
                reader[0].close()

        started = time.monotonic()
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = [pool.submit(batch, i) for i in range(4)]
            for future in as_completed(futures, timeout=90):
                observations = future.result()
                self.assertEqual(len(observations), 24)
                for index, status in enumerate(observations):
                    if index % 2 == 0:
                        self.assertIn(first.encode(), status)
                    else:
                        self.assertEqual(status,
                                         b"430 no article with that message-id\r\n")
        print("native reader indexed 96 concurrent STAT reads: {:.3f}s".format(
            time.monotonic() - started))
        for reader in (old, middle, fresh):
            reader[1].close()
            reader[0].close()
        self.stop_owner(owner)


if __name__ == "__main__":
    unittest.main()
