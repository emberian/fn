import json
import os
import shutil
import tempfile
import unittest
from datetime import datetime, timezone

from tools import gate_walls

FIX = os.path.join(os.path.dirname(__file__), "fixtures", "gate_walls", "run1")


class GateWallsTest(unittest.TestCase):
    def setUp(self):
        # mtime is not carried by git: copy the fixture and pin it (it is how
        # the time-of-day run.log is placed on a calendar day).
        self.tmp = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tmp)
        self.run = os.path.join(self.tmp, "run1")
        shutil.copytree(FIX, self.run)
        t = datetime(2026, 10, 8, 0, 7, tzinfo=timezone.utc).timestamp()
        os.utime(os.path.join(self.run, "run.log"), (t, t))
        self.r = gate_walls.analyze(self.run)

    def test_steps_across_midnight(self):
        s = self.r["steps"]
        self.assertEqual(s["install"], 60)
        self.assertEqual(s["certify"], 600)
        self.assertEqual(s["acquire"], 120)

    def test_image_phase_is_wall(self):
        self.assertEqual(self.r["image_s"], 60)
        self.assertEqual(self.r["steps"]["image-developer"], 40)

    def test_module_phase_and_total(self):
        self.assertEqual(self.r["module_s"], 60)
        self.assertEqual(self.r["total_s"], 16 * 60 + 20)

    def test_plumbing_share(self):
        self.assertEqual(self.r["plumbing_s"], 980 - 60 - 60)
        self.assertAlmostEqual(self.r["plumbing_share"], 860 / 980, places=3)

    def test_pre_book_and_top_books(self):
        self.assertEqual(self.r["certify_pre_book_s"], 180.0)
        self.assertEqual([b["book"] for b in self.r["top_books"]],
                         ["books/b", "books/a", "books/d"])

    def test_cache_line(self):
        self.assertTrue(self.r["cache"].startswith("From the cache: installed 9 of 10"))

    def test_main_prints_json_lines(self):
        import contextlib
        import io
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = gate_walls.main([self.run, self.run])
        lines = buf.getvalue().splitlines()
        self.assertEqual(rc, 0)
        self.assertEqual(len(lines), 3)
        self.assertEqual(json.loads(lines[2])["summary"]["runs"], 2)


if __name__ == "__main__":
    unittest.main()
