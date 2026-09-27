"""The record log's open tells a torn tail from damage (lane log-corruption;
fuzz-nntp's F3, planning/evidence/log-corruption-2026-09-27.md).

books/store-log-damage.lisp: after the stream stops, ACL2 probes every unit
of the rest of the segment.  A valid entry after the stop is DAMAGE, refused
by name (reason=log-damaged at=SEGMENT:OFFSET ... valid-after=N), exit 1,
nothing written; the owner does not start.  No valid entry after it is the
torn tail of the one pending write, recovered to the stop with a
`log torn-tail' line.  `store ROOT recover --repair truncate SEGMENT:OFFSET'
is the operator's confirmed repair of exactly that damage: the segment's
octets are kept under quarantine/ first, then the log recovers to the stop.

The base store is fuzz-nntp's twelve-article store (tests/fuzz_nntp.py
build_base_store), on the developer image.
"""
import hashlib
import shutil
import tempfile
import unittest
from pathlib import Path

from tests import fuzz_nntp as fz

SEGMENT = "journal/000001.log"
UNIT = 4096


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class LogDamageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = fz.developer_image()
        if not cls.image.is_file():
            raise unittest.SkipTest("developer native image missing: {}".format(cls.image))
        cls.dir = tempfile.TemporaryDirectory(prefix="fn-log-damage-")
        scratch = Path(cls.dir.name)
        cls.base, _archive, cls.ids = fz.build_base_store(cls.image, scratch, 12)
        rc, served, _err = fz.article_bytes(cls.image, cls.base, cls.ids)
        if rc != 0:
            raise AssertionError("the base store does not serve")
        cls.baseline = fz.store_article_map(served, cls.ids)
        # Entry starts: every entry begins on a unit (the log's padding); the
        # base store writes one record per entry.
        data = (cls.base / SEGMENT).read_bytes()
        cls.starts = [q for q in range(0, len(data), UNIT) if data[q:q + 4] == b"FNLG"]

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix="case-", dir=self.dir.name))
        self.store = self.work / "store"
        shutil.copytree(self.base, self.store, symlinks=True)

    def tearDown(self):
        shutil.rmtree(self.work, ignore_errors=True)

    def fn(self, *words):
        return fz.run_image(self.image, ["store", self.store] + list(words))

    def flip(self, at, bit=1):
        path = self.store / SEGMENT
        data = bytearray(path.read_bytes())
        data[at] ^= bit
        path.write_bytes(bytes(data))

    def served(self):
        rc, out, err = fz.article_bytes(self.image, self.store, self.ids)
        self.assertEqual(rc, 0, err[-400:])
        got = fz.store_article_map(out, self.ids)
        for m in self.ids:
            if len(got.get(m, b"")) > 3:
                self.assertEqual(got[m], self.baseline[m], m)
        return [m for m in self.ids if len(got.get(m, b"")) > 3]

    def test_the_base_store_is_one_record_per_unit_aligned_entry(self):
        self.assertEqual(len(self.starts), 12, self.starts)
        self.assertEqual(self.served(), self.ids)

    def test_damage_followed_by_valid_entries_is_refused_by_name_and_nothing_is_written(self):
        # fuzz-nntp's two reproducers (offset 0; offset 25184, inside record
        # 6) and a flip in every other entry but the last.
        offsets = sorted({0, 25184} | {q + 20 for q in self.starts[:-1]})
        for at in offsets:
            with self.subTest(at=at):
                self.setUp()
                self.flip(at)
                damaged = sha(self.store / SEGMENT)
                stop = max(q for q in self.starts if q <= at)
                after = sum(1 for q in self.starts if q > stop)
                for verb in ("status", "recover", "status"):
                    result = self.fn(verb)
                    err = result.stderr.decode("utf-8", "replace")
                    self.assertEqual(result.returncode, fz.EXIT_REFUSED, (verb, err[-600:]))
                    self.assertIn("reason=log-damaged at=000001.log:{} ".format(stop), err)
                    self.assertIn(" valid-after={} records={}".format(after, after), err)
                    self.assertIn("--repair truncate 000001.log:{}".format(stop), err)
                    self.assertNotIn(b"recovered", result.stdout, verb)
                    self.assertEqual(sha(self.store / SEGMENT), damaged, verb)
                self.assertFalse((self.store / "quarantine").exists())
                self.tearDown()

    def test_a_torn_last_entry_recovers_to_the_entry_before_it_and_says_so(self):
        # The last entry's second half zeroed: nothing valid after it, the
        # torn tail of the one pending write (the power-loss case).
        last = self.starts[-1]
        path = self.store / SEGMENT
        data = bytearray(path.read_bytes())
        end = data.index(b"\x00" * 64, last + 64)
        cut = last + (end - last) // 2
        data[cut:end] = bytes(end - cut)
        path.write_bytes(bytes(data))
        result = self.fn("recover")
        self.assertEqual(result.returncode, fz.EXIT_OK, result.stderr[-600:])
        self.assertIn(b"recovered transactions=11 articles=11", result.stdout)
        self.assertIn(b"log torn-tail at=000001.log:%d debris-units=" % last, result.stdout)
        self.assertEqual(self.fn("status").returncode, fz.EXIT_OK)
        self.assertEqual(self.served(), self.ids[:-1])

    def test_the_repair_is_the_confirmed_truncate_and_keeps_the_segment(self):
        self.flip(25184)
        damaged = (self.store / SEGMENT).read_bytes()
        stop = max(q for q in self.starts if q <= 25184)
        # Not confirmed: a repair naming another offset or segment is the
        # same refusal, and writes nothing.
        for wrong in ("000001.log:0", "000002.log:{}".format(stop), "000001.log:{}".format(stop + 1)):
            with self.subTest(confirm=wrong):
                result = self.fn("recover", "--repair", "truncate", wrong)
                self.assertEqual(result.returncode, fz.EXIT_REFUSED, result.stderr[-400:])
                self.assertIn(b"reason=log-damaged", result.stderr)
                self.assertEqual((self.store / SEGMENT).read_bytes(), damaged)
        usage = self.fn("recover", "--repair", "restore", "000001.log:{}".format(stop))
        self.assertEqual(usage.returncode, fz.EXIT_USAGE, usage.stderr[-400:])
        # Confirmed: the octets are kept, the log recovers to the stop.
        result = self.fn("recover", "--repair", "truncate", "000001.log:{}".format(stop))
        self.assertEqual(result.returncode, fz.EXIT_OK, result.stderr[-600:])
        kept = self.store / "quarantine" / "000001.log.damaged-at-{}".format(stop)
        self.assertEqual(kept.read_bytes(), damaged)
        records = self.starts.index(stop)
        after = len(self.starts) - records - 1
        self.assertIn(b"recovered transactions=%d articles=%d" % (records, records), result.stdout)
        self.assertIn(b"log repaired at=000001.log:%d dropped-valid-entries=%d dropped-records=%d"
                      % (stop, after, after), result.stdout)
        self.assertEqual(self.fn("status").returncode, fz.EXIT_OK)
        self.assertEqual(self.served(), self.ids[:records])
        # The repair is not repeated: the log is now clean.
        again = self.fn("recover")
        self.assertEqual(again.returncode, fz.EXIT_OK, again.stderr[-400:])
        self.assertNotIn(b"log repaired", again.stdout)


if __name__ == "__main__":
    unittest.main()
