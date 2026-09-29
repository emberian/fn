"""Compressed records in the log, on the developer image (lane
compression-extents-2; books/payload-lz-append.lisp PRF-341 over
books/payload-lz-record.lisp PRF-326).

`operator CONFIG policy set compress-min-octets N` (a configuration row; no
row is off) makes the append offer every article record whose payload span has
at least N octets to the vendored zlib encoder (lib/libfn-deflate: a DEFLATE
stream over the current shipped dictionary); ACL2's proved decoder checks the candidate before the record is taken, and every read
of the log expands the frame through the same decoder.  Two twin stores get
the same articles, one with the row: the compressed one holds fewer octets,
`store ROOT compression` reports its compressed records and the shipped
dictionary's ID (baseline 1, planning/evidence/compress-dict/baseline-1.json), and
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
# The first four BLAKE3 octets of the shipped baseline dictionary
# (books/payload-lz-dicts.lisp *fn-lzd-baseline-1-id*).
BASELINE_1_ID = 2220533217
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
        self.assertEqual(packed["dictionaries"], str(BASELINE_1_ID), line)
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


    # NNT-055, XFN-ZARTICLE (books/nntp-zarticle.lisp, PRF-993): a peer that
    # lists the shipped baseline's digest gets the article as it is stored,
    # yEnc-style escaped in lines of at most 128 octets (RFC 3977 3.1.1: a
    # block carries no NUL, CR or LF), and those octets, unescaped and
    # inflated against the baseline dictionary, are ARTICLE's; a peer that
    # lists another digest gets ARTICLE's reply octet for octet.
    def zarticle(self, digest_hex):
        transcript = b"".join(b"XFN-ZARTICLE " + m + b" " + digest_hex + fz.CRLF
                              for m in self.ids) + b"QUIT\r\n"
        rc, out, err = fz.model_reply(self.image, [transcript], self.packed)
        self.assertEqual(rc, 0, err[-400:])
        return out.split(fz.CRLF)[1:]

    def test_zarticle_sends_the_stored_block_to_a_peer_with_the_dictionary(self):
        import zlib
        evidence = Path(__file__).resolve().parents[1] / "planning/evidence/compress-dict"
        dictionary = (evidence / "baseline-1.bin").read_bytes()
        import json
        b3 = json.loads((evidence / "baseline-1.json").read_text())["blake3"].encode()
        lines = self.zarticle(b3)
        i = 0
        for m in self.ids:
            head = lines[i].split(b" ")
            self.assertEqual(head[:2], [b"229", b3], (m, lines[i]))
            n, clen = int(head[2]), int(head[3])
            i += 1
            block = []
            while lines[i] != b".":
                line = lines[i][1:] if lines[i].startswith(b"..") else lines[i]
                self.assertLessEqual(len(line), 128, m)
                self.assertFalse(set(line) & {0, 10, 13}, m)
                block.append(line)
                i += 1
            i += 1
            escaped, c, k = b"".join(block), bytearray(), 0
            while k < len(escaped):
                if escaped[k] == 61 and k + 1 < len(escaped):
                    c.append((escaped[k + 1] - 64) % 256)
                    k += 2
                else:
                    c.append(escaped[k])
                    k += 1
            self.assertEqual(len(c), clen, m)
            inflater = zlib.decompressobj(wbits=-15, zdict=dictionary)
            decoded = inflater.decompress(bytes(c)) + inflater.flush()
            self.assertEqual(len(decoded), n, m)
            expected = fz.CRLF.join(l[1:] if l.startswith(b"..") else l
                                    for l in self.baseline[m].split(fz.CRLF))
            self.assertIn(decoded, (expected, expected + fz.CRLF), m)

    def test_zarticle_answers_as_article_to_a_peer_without_the_dictionary(self):
        lines = self.zarticle(b"00" * 32)
        got = fz.store_article_map(fz.CRLF.join([b"greeting"] + lines), self.ids)
        for m in self.ids:
            self.assertEqual(got[m], self.baseline[m], m)

    def test_zarticle_refuses_a_malformed_digest(self):
        lines = self.zarticle(b"xyz")
        for k in range(len(self.ids)):
            self.assertTrue(lines[k].startswith(b"501"), lines[k])

    def test_fuzzed_zarticle_served_equals_the_model(self):
        # The fuzzer's XFN-ZARTICLE (its table row's :fuzz grammar: a
        # Message-ID from the store, a fresh one or a malformed one, and the
        # baseline's digest, "00" or "x"), cut as the diff campaign cuts it,
        # served by the reader over the packed store: octet for octet the
        # model's reply, a well-formed reply stream (229 is a block), and the
        # stored answer reached.
        reader = fz.Reader(self.image, self.packed)
        self.addCleanup(reader.stop)
        stored = 0
        for seed in range(24):
            gen = fz.Gen(seed, "reader", self.ids)
            data = b"".join([gen.cmd("XFN-ZARTICLE") for _ in range(12)] + [b"QUIT\r\n"])
            cuts = gen.chunkings(data, 3)
            model = fz.model_reply(self.image, gen.choice(cuts), self.packed)
            for cut in cuts:
                session = fz.served(reader, cut, 0.0)
                self.assertIsNone(fz.diff_verdict(model, session, reader), (seed, cut[:2]))
            stored += fz.normalize(model[1]).count(b"\r\n229 ")
        self.assertGreater(stored, 0)


if __name__ == "__main__":
    unittest.main()
