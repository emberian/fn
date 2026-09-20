"""Configuration records through the CLI: create, retire, revive, refuse."""
import sys
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from run_store import Acl2Store, Store  # noqa: E402
from tests.test_reader import ReaderProcess  # noqa: E402


class StoreConfigTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-store-config-")
        self.path = Path(self.temp.name) / "store"
        self.payload = Path(self.temp.name) / "payload"
        self.payload.write_bytes(b"Message-ID: <x@example.invalid>\r\n\r\nbody\r\n")
        self.invoke("init")

    def tearDown(self):
        self.temp.cleanup()

    def invoke(self, command, *args, expected=0):
        result = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(self.path),
                                 command, *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, check=False)
        if result.returncode != expected:
            self.fail("{} {} returned {}\nstdout={}\nstderr={}".format(
                command, args, result.returncode, result.stdout.decode("utf-8", "replace"),
                result.stderr.decode("utf-8", "replace")))
        return result

    def post(self, msgid, group, expected=0):
        return self.invoke("post", "--message-id", msgid, "--payload", self.payload,
                           "--group", group, expected=expected)

    def config(self):
        line = self.invoke("config").stdout.decode("ascii").strip()
        fields = dict(part.split("=", 1) for part in line.split())
        return (int(fields["generation"]),
                tuple(n for n in fields["served"].split(",") if n),
                tuple(n for n in fields["domain"].split(",") if n))

    @staticmethod
    def read_all(sock):
        chunks = []
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)

    def recovered(self):
        store = Store(self.path, writable=False)
        store.acquire()
        bridge = Acl2Store()
        try:
            store.recover(bridge)
            return store.config_generation, store.config_served, store.config_domain, \
                [bridge.group_next(code) for code in range(len(store.config_domain))]
        finally:
            bridge.close()
            store.close()

    def test_init_writes_generation_one_from_its_arguments(self):
        self.assertEqual(self.config(), (1, ("fn.letters", "fn.test"), ("fn.letters", "fn.test")))
        other = Path(self.temp.name) / "nine"
        names = ["fn.g{}".format(i) for i in range(9)]
        args = []
        for name in names:
            args += ["--group", name]
        subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "init", *args],
                       cwd=ROOT, check=True, stdout=subprocess.PIPE)
        line = subprocess.run([sys.executable, "tools/run_store.py", "--store", str(other), "config"],
                              cwd=ROOT, check=True, stdout=subprocess.PIPE).stdout.decode("ascii")
        self.assertIn("served=" + ",".join(names), line)

    def test_create_retire_and_revive_resume_numbering_across_recovery(self):
        self.assertIn(b"generation=2", self.invoke("group", "create", "fn.dtn").stdout)
        self.assertEqual(self.config(), (2, ("fn.letters", "fn.test", "fn.dtn"),
                                         ("fn.letters", "fn.test", "fn.dtn")))
        self.post("<a@example.invalid>", "fn.dtn")
        self.post("<b@example.invalid>", "fn.dtn")
        self.invoke("recover")
        self.assertEqual(self.recovered()[3], [1, 1, 3])
        self.invoke("group", "retire", "fn.dtn")
        generation, served, domain, nexts = self.recovered()
        # Retired: not served, still in the domain, watermark kept, articles bound.
        self.assertEqual((generation, served, domain), (3, ("fn.letters", "fn.test"),
                                                       ("fn.letters", "fn.test", "fn.dtn")))
        self.assertEqual(nexts, [1, 1, 3])
        self.assertIn(b"articles=2", self.invoke("status").stdout)
        refused = self.post("<c@example.invalid>", "fn.dtn", expected=run_store.EXIT_REFUSED)
        self.assertIn(b"refused", refused.stderr)
        self.invoke("recover")
        self.invoke("group", "create", "fn.dtn")
        self.post("<c@example.invalid>", "fn.dtn")
        generation, served, domain, nexts = self.recovered()
        self.assertEqual((generation, served), (4, ("fn.letters", "fn.test", "fn.dtn")))
        # Re-creation resumed the numbering: the third article took number 3.
        self.assertEqual(nexts, [1, 1, 4])

    def test_duplicate_create_unknown_retire_and_overflow_are_refused(self):
        dup = self.invoke("group", "create", "fn.letters", expected=run_store.EXIT_REFUSED)
        self.assertIn(b"duplicate-group", dup.stderr)
        gone = self.invoke("group", "retire", "fn.nope", expected=run_store.EXIT_REFUSED)
        self.assertIn(b"no-such-group", gone.stderr)
        # RFC 3977 section 3.1: the served table must render inside the initial
        # line.  Three 128-octet names fit beside the two defaults; a fourth
        # would not, and is refused before anything is written.
        for i in range(3):
            self.invoke("group", "create", "fn." + chr(ord("a") + i) * 125)
        over = self.invoke("group", "create", "fn." + "z" * 125, expected=run_store.EXIT_REFUSED)
        self.assertIn(b"group-table-unprojectable", over.stderr)
        self.invoke("recover")
        self.assertEqual(self.config()[0], 4)
        self.assertEqual(len(self.config()[1]), 5)

    def test_reader_pins_the_generation_it_opened_at(self):
        with ReaderProcess(store=str(self.path)) as reader:
            self.assertEqual(reader.generation, 1)
            sock = reader.connect()
            sock.sendall(b"LIST ACTIVE\r\nQUIT\r\n")
            listing = self.read_all(sock)
            self.assertIn(b"fn.letters ", listing)
            self.assertNotIn(b"fn.dtn", listing)
            # The reader's shared lock fixes its snapshot; a reconfiguration
            # while it is open is refused at the lock, never applied under it.
            held = self.invoke("group", "create", "fn.dtn", expected=run_store.EXIT_REFUSED)
            self.assertIn(b"locked", held.stderr)
        self.invoke("group", "create", "fn.dtn")
        with ReaderProcess(store=str(self.path)) as reader:
            self.assertEqual(reader.generation, 2)
            sock = reader.connect()
            sock.sendall(b"LIST ACTIVE\r\nQUIT\r\n")
            self.assertIn(b"fn.dtn ", self.read_all(sock))


if __name__ == "__main__":
    unittest.main()
