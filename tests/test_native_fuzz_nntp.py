"""Regression tests from the NNTP fuzzer (tests/fuzz_nntp.py).

Each JSON file in tests/fixtures/fuzz-nntp/ is a minimized reproducer a
campaign found (planning/evidence/fuzz-nntp-2026-09-27.md).  A `diff' one is
replayed through the developer image's diagnostic listener and the model;
a `node' one through a scratch production owner; a `store' one rebuilds the
base store, applies the recorded mutation and runs the store commands.

A reproducer's `status' says what the replay must show:
  fixed  no finding: the served bytes equal the model's, the reply stream has
         its shape, the server closed within the bound and is alive, the
         store refused by name or served the original bytes;
  open   the recorded finding, with its signature class, still reproduces.
         The defect is handed to its owner (the `packet' field); when the
         fix lands this test fails and says so, and the status becomes fixed.
Open is not passing: it keeps a known defect visible instead of red or
silent.  Without an image they are skipped by name, never passed.

The generator, the shape check and the minimizer are tested here without an
image: they are the harness, and a harness that cannot see a fault is the
failure this module would otherwise hide.
"""
import json
import os
from pathlib import Path
import unittest

from tests import fuzz_nntp as fz

FIXTURES = Path(__file__).resolve().parent / "fixtures" / "fuzz-nntp"


def reproducers(campaign):
    return sorted(p for p in FIXTURES.glob("*.json")
                  if json.loads(p.read_text()).get("campaign") == campaign)


class HarnessTests(unittest.TestCase):
    def test_a_seed_is_a_transcript(self):
        self.assertEqual(fz.Gen(7, "reader").transcript(), fz.Gen(7, "reader").transcript())
        self.assertNotEqual(fz.Gen(7, "reader").transcript(), fz.Gen(8, "reader").transcript())

    def test_every_cut_rejoins_the_transcript(self):
        gen = fz.Gen(3, "reader")
        data = b"".join(gen.transcript())
        for cut in gen.chunkings(data, 6):
            self.assertEqual(b"".join(cut), data)

    def test_shape_accepts_a_well_formed_stream(self):
        stream = (b"200 ready\r\n211 2 1 2 fn.test\r\n211 2 1 2 fn.test list follows\r\n1\r\n2\r\n.\r\n"
                  b"220 1 <a@b> article\r\nSubject: x\r\n\r\n..dot\r\n.\r\n"
                  b"229 845a 10 12\r\nab=Mc\r\n..x\r\n.\r\n205 bye\r\n")
        self.assertEqual(fz.shape_problems(stream), [])

    def test_shape_sees_each_fault(self):
        cases = {
            b"200 ok\r\nhello\r\n": "no reply code",
            b"200 ok\r\n220 1 <a@b>\r\n.dot\r\n.\r\n": "unstuffed",
            b"200 ok\r\n220 1 <a@b>\r\nbody\r\n": "not terminated",
            b"200 ok\r\n205 by": "partial last line",
            b"200 " + b"x" * 520 + b"\r\n": "octets",
            b"500 no\r\n": "greeting",
            b"200 ok\r\n229 00 1 2\r\nab\r\n": "not terminated",
        }
        for stream, word in cases.items():
            self.assertTrue(any(word in p for p in fz.shape_problems(stream)), (stream[:40], word))

    def test_ddmin_finds_the_two_culprits(self):
        self.assertEqual(fz.ddmin(list(range(40)), lambda xs: 3 in xs and 31 in xs, float("inf")), [3, 31])

    def test_normalize_hides_only_the_date_line(self):
        self.assertEqual(fz.normalize(b"111 20260927161500\r\n"), b"111 YYYYMMDDhhmmss\r\n")
        self.assertEqual(fz.normalize(b"211 20260927161500\r\n"), b"211 20260927161500\r\n")


def judge(test, path, verdict):
    record = json.loads(path.read_text())
    if record.get("status", "fixed") == "fixed":
        test.assertIsNone(verdict, "{} reproduces again".format(path.name))
    else:
        test.assertIsNotNone(verdict, "{} no longer reproduces: the fix for {} landed; set its "
                             "status to fixed".format(path.name, record.get("packet")))
        test.assertEqual(verdict[0], record["class"], verdict)


def image_ready(image):
    return image.is_file() and os.access(image, os.X_OK)


class DiffReproducerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not image_ready(fz.developer_image()):
            raise unittest.SkipTest("developer native image missing: {}".format(fz.developer_image()))

    def test_each_diff_reproducer(self):
        for path in reproducers("diff"):
            with self.subTest(reproducer=path.name):
                judge(self, path, fz.replay(path))


class NodeReproducerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not image_ready(fz.production_image()):
            raise unittest.SkipTest("native image missing: {}".format(fz.production_image()))

    def test_each_node_reproducer(self):
        for path in reproducers("node"):
            with self.subTest(reproducer=path.name):
                judge(self, path, fz.replay(path))


class BoundsReproducerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not image_ready(fz.production_image()):
            raise unittest.SkipTest("native image missing: {}".format(fz.production_image()))

    def test_each_bounds_reproducer(self):
        for path in reproducers("bounds"):
            with self.subTest(reproducer=path.name):
                judge(self, path, fz.replay(path))


class StoreReproducerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not image_ready(fz.developer_image()):
            raise unittest.SkipTest("developer native image missing: {}".format(fz.developer_image()))

    def test_each_store_reproducer(self):
        for path in reproducers("store"):
            with self.subTest(reproducer=path.name):
                judge(self, path, fz.replay(path))


if __name__ == "__main__":
    unittest.main()
