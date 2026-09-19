"""9P2000 transcripts for the read-only projection of a committed store.

The client here is independent of tools/fn9p.py: it encodes and decodes the
protocol itself, so a server that agreed with a shared helper but not with the
protocol would fail.  Expected article bytes are never taken from the 9P view;
they come from the NNTP reader's own ARTICLE and LISTGROUP replies over the
same store, which is the comparison this lane exists to make.
"""
import os
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
from tests.test_reader import ReaderProcess  # noqa: E402

import socket  # noqa: E402

TVERSION, TATTACH, TWALK, TOPEN, TREAD, TCLUNK, TSTAT = 100, 104, 110, 112, 116, 120, 124
RERROR = 107
NOFID = 0xFFFFFFFF
QTDIR = 0x80
OREAD, OWRITE = 0, 1
ROOT_FID = 1


class NineError(Exception):
    """An Rerror the server returned."""


class NineClient:
    """A minimal 9P2000 client written for this test only."""

    def __init__(self, port, msize=8192):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=15)
        self.sock.settimeout(15)
        self.tag = 0
        self.msize = msize
        reply = self.rpc(TVERSION, struct.pack("<I", msize) + self.string(b"9P2000"))
        self.msize = struct.unpack("<I", reply[:4])[0]
        if self.field(reply, 4)[0] != b"9P2000":
            raise AssertionError("server refused 9P2000")
        self.rpc(TATTACH, struct.pack("<II", ROOT_FID, NOFID)
                 + self.string(b"fn") + self.string(b""))
        self.next_fid = ROOT_FID + 1

    def close(self):
        self.sock.close()

    @staticmethod
    def string(value):
        return struct.pack("<H", len(value)) + value

    @staticmethod
    def field(body, at):
        size = struct.unpack("<H", body[at:at + 2])[0]
        return body[at + 2:at + 2 + size], at + 2 + size

    def recv_exact(self, count):
        data = b""
        while len(data) < count:
            chunk = self.sock.recv(count - len(data))
            if not chunk:
                raise AssertionError("9P server closed the connection")
            data += chunk
        return data

    def rpc(self, kind, body):
        self.tag = (self.tag + 1) & 0x7FFF
        self.sock.sendall(struct.pack("<IBH", 7 + len(body), kind, self.tag) + body)
        size = struct.unpack("<I", self.recv_exact(4))[0]
        rest = self.recv_exact(size - 4)
        received, tag = rest[0], struct.unpack("<H", rest[1:3])[0]
        if received == RERROR:
            raise NineError(self.field(rest[3:], 0)[0].decode())
        if received != kind + 1 or tag != self.tag:
            raise AssertionError("unexpected 9P reply {} tag {}".format(received, tag))
        return rest[3:]

    def walk(self, names):
        fid = self.next_fid
        self.next_fid += 1
        body = struct.pack("<IIH", ROOT_FID, fid, len(names))
        for name in names:
            body += self.string(name)
        reply = self.rpc(TWALK, body)
        if struct.unpack("<H", reply[:2])[0] != len(names):
            raise NineError("incomplete walk")
        return fid

    def open(self, fid, mode=OREAD):
        self.rpc(TOPEN, struct.pack("<IB", fid, mode))
        return fid

    def read(self, fid, offset, count):
        reply = self.rpc(TREAD, struct.pack("<IQI", fid, offset, count))
        return reply[4:4 + struct.unpack("<I", reply[:4])[0]]

    def clunk(self, fid):
        self.rpc(TCLUNK, struct.pack("<I", fid))

    def stat(self, fid):
        reply = self.rpc(TSTAT, struct.pack("<I", fid))
        return self.parse_stat(reply[2:])

    @staticmethod
    def parse_stat(entry):
        qtype = entry[8]
        length = struct.unpack("<Q", entry[33:41])[0]
        name = NineClient.field(entry, 41)[0]
        return {"name": name, "length": length, "dir": bool(qtype & QTDIR)}

    def read_file(self, names):
        fid = self.open(self.walk(names))
        try:
            data, offset = b"", 0
            while True:
                chunk = self.read(fid, offset, self.msize - 64)
                if not chunk:
                    return data
                data += chunk
                offset += len(chunk)
        finally:
            self.clunk(fid)

    def read_dir(self, names):
        fid = self.open(self.walk(names))
        try:
            entries, offset = [], 0
            while True:
                chunk = self.read(fid, offset, self.msize - 64)
                if not chunk:
                    return entries
                offset += len(chunk)
                at = 0
                while at < len(chunk):
                    size = struct.unpack("<H", chunk[at:at + 2])[0]
                    entries.append(self.parse_stat(chunk[at:at + 2 + size]))
                    at += 2 + size
        finally:
            self.clunk(fid)


class NineProcess:
    """tools/fn9p.py over one store, addressed by an ephemeral port."""

    def __init__(self, store):
        self.store = store

    def __enter__(self):
        self.proc = subprocess.Popen(
            [sys.executable, "tools/fn9p.py", "--store", str(self.store), "--port", "0"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        deadline = time.monotonic() + 180
        while time.monotonic() < deadline:
            line = self.proc.stdout.readline()
            if line.startswith(b"LISTENING "):
                self.port = int(line.split()[1])
                return self
            if not line and self.proc.poll() is not None:
                break
        self.__exit__()
        raise RuntimeError("fn9p did not listen: "
                           + self.proc.stderr.read().decode("utf-8", "replace"))

    def __exit__(self, *unused):
        if self.proc.poll() is None:
            self.proc.terminate()
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)
        self.proc.stdout.close()
        self.proc.stderr.close()

    def client(self):
        return NineClient(self.port)


def nntp_reply(sock, terminator=b"\r\n"):
    """Read one reply, either a single line or a complete multi-line block."""
    data = b""
    while not data.endswith(terminator):
        chunk = sock.recv(4096)
        if not chunk:
            break
        data += chunk
    return data


ONE = (b"Message-ID: <one@example.invalid>\r\nSubject: one\r\n\r\nFirst body\r\n")
TWO = (b"Message-ID: <two@example.invalid>\r\nSubject: two\r\n\r\nSecond body\r\n")
THREE = (b"Message-ID: <three@example.invalid>\r\nSubject: three\r\n\r\nThird body\r\n")


class NinePViewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-9p-store-")
        self.store = Path(self.temp.name) / "store"
        self.payload = Path(self.temp.name) / "article"
        self.store_command("init")

    def tearDown(self):
        self.temp.cleanup()

    def store_command(self, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.store), command,
             *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode != expected:
            self.fail("store {} returned {}\nstderr={}".format(
                command, result.returncode, result.stderr))
        return result

    def post(self, msgid, payload, groups):
        self.payload.write_bytes(payload)
        args = ["--message-id", msgid, "--payload", self.payload]
        for group in groups:
            args.extend(["--group", group])
        self.store_command("post", *args)

    def test_files_and_listings_agree_with_the_nntp_reader(self):
        self.post("<one@example.invalid>", ONE, ("fn.letters", "fn.test"))
        self.post("<two@example.invalid>", TWO, ("fn.letters",))
        with NineProcess(self.store) as server:
            client = server.client()
            self.addCleanup(client.close)

            top = sorted(entry["name"] for entry in client.read_dir([]))
            self.assertEqual(top, [b"by-id", b"groups", b"status"])

            groups = sorted(entry["name"] for entry in client.read_dir([b"groups"]))
            self.assertEqual(groups, [b"fn.letters", b"fn.test"])

            letters = client.read_dir([b"groups", b"fn.letters"])
            numbers = [entry["name"] for entry in letters]

            with ReaderProcess(self.store) as reader:
                sock = reader.connect()
                self.addCleanup(sock.close)
                sock.sendall(b"LISTGROUP fn.letters\r\n")
                listing = nntp_reply(sock, b"\r\n.\r\n")
                self.assertEqual(
                    listing,
                    b"211 2 1 2 fn.letters list follows\r\n1\r\n2\r\n.\r\n")
                # The directory names are exactly LISTGROUP's number lines.
                self.assertEqual(
                    numbers, listing.split(b"\r\n")[1:-2])

                for number, payload, msgid in ((b"1", ONE, b"<one@example.invalid>"),
                                               (b"2", TWO, b"<two@example.invalid>")):
                    served = client.read_file([b"groups", b"fn.letters", number])
                    sock.sendall(b"ARTICLE " + number + b"\r\n")
                    reply = nntp_reply(sock, b"\r\n.\r\n")
                    self.assertEqual(
                        reply,
                        b"220 " + number + b" " + msgid + b" article follows\r\n"
                        + served + b".\r\n")
                    self.assertEqual(served, payload)

            # Sizes reported by stat match the bytes the reads returned.
            self.assertEqual([entry["length"] for entry in letters], [len(ONE), len(TWO)])

            # The same article under both names is the same file content.
            by_id = sorted(entry["name"] for entry in client.read_dir([b"by-id"]))
            self.assertEqual(
                by_id, sorted(msgid.encode().hex().encode()
                              for msgid in ("<one@example.invalid>", "<two@example.invalid>")))
            self.assertEqual(
                client.read_file([b"by-id", b"<one@example.invalid>".hex().encode()]), ONE)

            # fn.test holds only the article that named it.
            self.assertEqual(
                [entry["name"] for entry in client.read_dir([b"groups", b"fn.test"])], [b"1"])
            self.assertEqual(client.read_file([b"groups", b"fn.test", b"1"]), ONE)

            status = client.read_file([b"status"])
            self.assertEqual(status.splitlines()[1:],
                             [b"articles 2", b"groups 2"])
            self.assertTrue(status.startswith(b"generation "))

            # The view is read-only and has no namespace beyond the projection.
            with self.assertRaises(NineError):
                client.open(client.walk([b"status"]), OWRITE)
            with self.assertRaises(NineError):
                client.walk([b"groups", b"fn.letters", b"99"])

    def test_mount_generation_is_fixed_and_a_fresh_mount_advances(self):
        self.post("<one@example.invalid>", ONE, ("fn.letters",))
        with NineProcess(self.store) as mounted:
            client = mounted.client()
            self.addCleanup(client.close)
            before = client.read_file([b"status"])
            self.assertEqual([entry["name"]
                              for entry in client.read_dir([b"groups", b"fn.letters"])], [b"1"])

            # The snapshot was taken under the shared store lock and the lock
            # was released with the bridge, so a writer is not blocked by a
            # live mount.  What the mount shows is fixed all the same.
            self.post("<three@example.invalid>", THREE, ("fn.letters",))

            self.assertEqual(client.read_file([b"status"]), before)
            self.assertEqual([entry["name"]
                              for entry in client.read_dir([b"groups", b"fn.letters"])], [b"1"])
            with self.assertRaises(NineError):
                client.walk([b"groups", b"fn.letters", b"2"])

            with NineProcess(self.store) as fresh:
                later = fresh.client()
                self.addCleanup(later.close)
                after = later.read_file([b"status"])
                self.assertNotEqual(after, before)
                self.assertEqual(after.splitlines()[1], b"articles 2")
                self.assertGreater(int(after.split(b"\n")[0].split()[1]),
                                   int(before.split(b"\n")[0].split()[1]))
                self.assertEqual([entry["name"] for entry
                                  in later.read_dir([b"groups", b"fn.letters"])],
                                 [b"1", b"2"])
                self.assertEqual(later.read_file([b"groups", b"fn.letters", b"2"]), THREE)


if __name__ == "__main__":
    unittest.main()
