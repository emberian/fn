"""Configuration records through the CLI: create, retire, revive, capacity, refuse."""
import re
import sys
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402
from tools import frame_bridge  # noqa: E402
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

    def test_capacity_is_a_configuration_record_with_three_outcomes(self):
        """R6.  `capacity <n>` raises, refuses below the reservation total, and
        refuses a decrease the store could not replay -- three outcomes, and
        the accepted one survives recovery."""
        before = self.config()[0]
        self.invoke("capacity", 2097152)
        self.assertEqual(self.config()[0], before + 1)

        # One article reserves; a capacity below the reservation total is the
        # core's refusal (:capacity-below-reserved), not Python's.
        self.post("<cap@example.invalid>", "fn.letters")
        refused = self.invoke("capacity", 0, expected=run_store.EXIT_REFUSED)
        self.assertIn(b"refused capacity", refused.stderr)
        # and the refusal wrote nothing: the generation did not move.
        self.assertEqual(self.config()[0], before + 1)

        # A decrease that the store could still replay is accepted, and the
        # value survives a reopen -- a configuration record, not a flag.
        self.invoke("capacity", 1048576)
        self.assertEqual(self.config()[0], before + 2)
        store = Store(self.path, writable=False)
        store.acquire()
        bridge = Acl2Store()
        try:
            store.recover(bridge)
            self.assertEqual(store.config_generation, before + 2)
        finally:
            bridge.close()
            store.close()

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

    def test_peer_add_with_no_size_options_is_accepted(self):
        """The default `--inbound-max-octets` is inside the model's ceiling.

        `bin/fn` and `tools/run_store.py` both typed 1048576, while
        `fn-cfg-peer-inboundp` (books/peer-config.lisp) caps the inbound
        octet count at `*fn-record-max-payload*`, so the operator's first
        `peer add` was refused `:peer-record` with exit 1 and no harness
        ever had a peer table. `w11/twonode-feed` made the default 0 and
        `fn-store-cfg-peer-record` resolve it, which is the one-owner fix;
        this case is the regression test that arrived a lane later.

        The ceiling is never typed here. It is ACL2's `*fn-record-max-payload*`,
        read from the model, and the second half shows the bound still bites
        one octet above it.  The listing is ACL2's `peer list` report
        (`fn-native-admin-peer-report`), the line the native host prints.
        """
        self.invoke("peer", "add", "upstream", "--nntp", "news.example.invalid:119",
                    "--inbound-groups", "fn.*", "--source-address", "192.0.2.1")
        listing = self.invoke("peer", "list").stdout.decode("ascii").strip()
        self.assertTrue(listing.startswith("upstream path-identity="), listing)
        self.assertIn(" inbound=fn.* ", listing + " ")
        self.assertIn(" outbound=- auth=source-address:192.0.2.1", listing)
        ceiling = frame_bridge.session().call("*fn-record-max-payload*")
        self.assertGreater(ceiling, 0)
        refused = self.invoke("peer", "add", "toobig", "--nntp", "news.example.invalid:119",
                              "--inbound-groups", "fn.*", "--source-address", "192.0.2.2",
                              "--inbound-max-octets", ceiling + 1,
                              expected=run_store.EXIT_REFUSED)
        self.assertIn(b"peer-record", refused.stderr)
        # And it is the bound that refused, not the rest of the record: the
        # same peer at the ceiling itself is accepted.
        self.invoke("peer", "add", "atceiling", "--nntp", "news.example.invalid:119",
                    "--inbound-groups", "fn.*", "--source-address", "192.0.2.3",
                    "--inbound-max-octets", ceiling)


if __name__ == "__main__":
    unittest.main()
