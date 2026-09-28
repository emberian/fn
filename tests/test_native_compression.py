"""Compressed records in the log, on the developer image (lane
compression-extents-2; books/payload-lz-append.lisp PRF-341 over
books/payload-lz-record.lisp PRF-326).

`operator CONFIG policy set compress-min-octets N` (a configuration row; no
row is off) makes the append offer every article record whose payload span has
at least N octets to the vendored LZ4-HC encoder (lib/libfn-lz4); ACL2's
proved decoder checks the candidate before the record is taken, and every read
of the log expands the frame through the same decoder.  Two twin stores get
the same articles, one with the row: the compressed one holds fewer octets,
`store ROOT compression` reports its compressed records and dictionary 0, and
every article reads back octet for octet as the uncompressed twin serves it --
after a recover, after a second recover (the replay is deterministic), and
after a torn last entry (a power loss through a compressed record recovers
to the entry before it, like any torn tail).

Run: FN_NATIVE_DEVELOPER_HOST=<developer launcher> python3 -m unittest -v tests.test_native_compression
"""
import os
from pathlib import Path
import re
import shutil
import tempfile
import unittest

from tests import fuzz_nntp as fz

SEGMENT = "journal/000001.log"
UNIT = 4096
ARTICLES = 16
MIN = 64


def payload(n):
    # Compressible text of 1-3 KiB with a unique first line: the shape of a
    # Usenet article's body, not random octets.
    body = b"".join(b"line %d of article %d: the quick brown fox jumps over the lazy dog\r\n"
                    % (k, n) for k in range(12 + (n * 7) % 30))
    return (b"From: z@b.invalid\r\nNewsgroups: fn.test\r\nSubject: z%d\r\n"
            b"Message-ID: <lz%d@compression.invalid>\r\n\r\n%s" % (n, n, body))


def mid(n):
    return b"<lz%d@compression.invalid>" % n


class CompressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = fz.developer_image()
        if not cls.image.is_file():
            raise unittest.SkipTest("developer native image missing: {}".format(cls.image))
        cls.dir = tempfile.TemporaryDirectory(prefix="fn-compression-")
        scratch = Path(cls.dir.name)
        cls.ids = [mid(n) for n in range(ARTICLES)]
        cls.plain = cls.build(scratch / "plain", None)
        cls.packed = cls.build(scratch / "packed", MIN)
        rc, served, err = fz.article_bytes(cls.image, cls.plain, cls.ids)
        if rc != 0:
            raise AssertionError("the plain store does not serve: " + err.decode()[-400:])
        cls.baseline = fz.store_article_map(served, cls.ids)

    @classmethod
    def build(cls, root, threshold):
        root.mkdir(parents=True)
        store = root / "store"
        config = root / "fn.toml"
        config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = 1\n'
                          '[control]\npath = "%s"\n' % (store, root / "c.sock"))
        init = fz.run_image(cls.image, ["store", store, "init", "fn.test"])
        if init.returncode != 0:
            raise AssertionError(init.stderr.decode()[-600:])
        if threshold is not None:
            row = fz.run_image(cls.image, ["operator", config, "policy", "set",
                                           "compress-min-octets", str(threshold)])
            if row.returncode != 0:
                raise AssertionError("policy set: " + row.stderr.decode()[-600:])
        file = root / "payload"
        for n in range(ARTICLES):
            file.write_bytes(payload(n))
            posted = fz.run_image(cls.image, ["store", store, "post", mid(n).decode(), file,
                                              "-", "-", "fn.test"])
            if posted.returncode != 0:
                raise AssertionError("post {}: {}".format(n, posted.stderr.decode()[-600:]))
        return store

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def copy(self, store):
        work = Path(tempfile.mkdtemp(prefix="case-", dir=self.dir.name))
        target = work / "store"
        shutil.copytree(store, target, symlinks=True)
        self.addCleanup(shutil.rmtree, work, True)
        return target

    def report(self, store):
        result = fz.run_image(self.image, ["store", store, "compression"])
        self.assertEqual(result.returncode, fz.EXIT_OK, result.stderr[-600:])
        line = result.stdout.decode().strip()
        fields = dict(re.findall(r"([a-z-]+)=([0-9a-z,]+)", line))
        return line, fields

    def served(self, store, ids=None):
        ids = ids or self.ids
        rc, out, err = fz.article_bytes(self.image, store, ids)
        self.assertEqual(rc, 0, err[-400:])
        return fz.store_article_map(out, ids)

    def test_the_row_compresses_and_the_report_says_so(self):
        _line, plain = self.report(self.plain)
        line, packed = self.report(self.packed)
        self.assertEqual(plain["compress-min-octets"], "0", line)
        self.assertEqual(plain["compressed-records"], "0")
        self.assertEqual(plain["dictionaries"], "none")
        self.assertEqual(packed["compress-min-octets"], str(MIN), line)
        self.assertEqual(int(packed["compressed-records"]), ARTICLES, line)
        self.assertEqual(packed["dictionaries"], "0", line)
        self.assertLess(int(packed["stored-octets"]), int(packed["uncompressed-octets"]), line)
        # The expansions are the plain store's records: the same octets.
        self.assertEqual(packed["uncompressed-octets"], plain["uncompressed-octets"])
        print("\n" + line)

    def test_every_article_reads_back_as_the_plain_twin_serves_it(self):
        got = self.served(self.packed)
        for m in self.ids:
            self.assertGreater(len(self.baseline[m]), 3, m)
            self.assertEqual(got[m], self.baseline[m], m)

    def test_recover_twice_serves_the_same_and_the_digest_is_stable(self):
        store = self.copy(self.packed)
        digests = []
        for _ in range(2):
            rec = fz.run_image(self.image, ["store", store, "recover"])
            self.assertEqual(rec.returncode, fz.EXIT_OK, rec.stderr[-600:])
            self.assertIn(b"recovered transactions=%d articles=%d" % (ARTICLES, ARTICLES), rec.stdout)
            dig = fz.run_image(self.image, ["store", store, "digest"])
            self.assertEqual(dig.returncode, fz.EXIT_OK, dig.stderr[-600:])
            digests.append(dig.stdout)
        self.assertEqual(digests[0], digests[1])
        got = self.served(store)
        for m in self.ids:
            self.assertEqual(got[m], self.baseline[m], m)

    def test_a_torn_compressed_last_entry_recovers_to_the_entry_before_it(self):
        store = self.copy(self.packed)
        path = store / SEGMENT
        data = bytearray(path.read_bytes())
        starts = [q for q in range(0, len(data), UNIT) if data[q:q + 4] == b"FNLG"]
        self.assertEqual(len(starts), ARTICLES, starts)
        last = starts[-1]
        # The last entry holds a frame ('fn-z' as a bstr head: 0x44 f n - z).
        self.assertIn(b"\x44fn-z", bytes(data[last:last + UNIT]))
        end = data.index(b"\x00" * 64, last + 64)
        cut = last + (end - last) // 2
        data[cut:end] = bytes(end - cut)
        path.write_bytes(bytes(data))
        rec = fz.run_image(self.image, ["store", store, "recover"])
        self.assertEqual(rec.returncode, fz.EXIT_OK, rec.stderr[-600:])
        self.assertIn(b"recovered transactions=%d articles=%d" % (ARTICLES - 1, ARTICLES - 1),
                      rec.stdout)
        self.assertIn(b"log torn-tail at=000001.log:%d" % last, rec.stdout)
        got = self.served(store)
        for m in self.ids[:-1]:
            self.assertEqual(got[m], self.baseline[m], m)
        self.assertFalse(got.get(self.ids[-1], b"").startswith(b"220"))

    def test_damage_inside_a_compressed_block_is_refused_by_name(self):
        # A flipped octet inside an entry that is not the last: its trailer
        # fails and valid entries follow, so the open refuses it as damage
        # (the frame is never expanded from unverified octets).
        store = self.copy(self.packed)
        path = store / SEGMENT
        data = bytearray(path.read_bytes())
        starts = [q for q in range(0, len(data), UNIT) if data[q:q + 4] == b"FNLG"]
        victim = starts[3]
        at = bytes(data[victim:victim + UNIT]).index(b"\x44fn-z") + victim + 40
        data[at] ^= 1
        path.write_bytes(bytes(data))
        result = fz.run_image(self.image, ["store", store, "recover"])
        self.assertEqual(result.returncode, fz.EXIT_REFUSED, result.stderr[-600:])
        self.assertIn(b"reason=log-damaged at=000001.log:%d " % victim, result.stderr)


if __name__ == "__main__":
    unittest.main()
