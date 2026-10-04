"""tools/box_table.py: rented build boxes from a config file, expiring by row."""
import datetime as dt
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import box_table  # noqa: E402

FIXED = {
    "hbox": {"acl2": "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k", "sbcl": "/tank/fn/sbcl/bin/sbcl",
             "cache": "/tank/fn/certcache", "wrap": "swarm-build"},
    "persvati": {"acl2": "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k", "sbcl": "/tank/fn/sbcl/bin/sbcl",
                 "cache": "~/fn-certcache", "wrap": ""},
}
NOW = dt.datetime(2026, 10, 4, 16, 0, tzinfo=dt.timezone.utc)


class BoxTableTests(unittest.TestCase):
    def table(self, boxes):
        handle = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        self.addCleanup(os.unlink, handle.name)
        json.dump({"boxes": boxes}, handle)
        handle.close()
        return {"FN_BOXES_FILE": handle.name}

    def test_no_file_is_no_boxes(self):
        self.assertEqual(box_table.extra_boxes(FIXED, {"FN_BOXES_FILE": "/nonexistent/boxes.json"}, NOW), {})

    def test_a_row_takes_its_like_box_and_its_own_fields(self):
        env = self.table({"cloud1": {"like": "hbox", "cores": 8, "check_jobs": 4},
                          "cloud2": {"like": "persvati", "wrap": "swarm-build"}})
        rows = box_table.extra_boxes(FIXED, env, NOW)
        self.assertEqual(rows["cloud1"]["acl2"], FIXED["hbox"]["acl2"])
        self.assertEqual(rows["cloud1"]["cache"], "/tank/fn/certcache")
        self.assertEqual(rows["cloud1"]["images"], "/tank/fn/images")
        self.assertEqual(rows["cloud1"]["check_jobs"], "4")
        self.assertEqual(rows["cloud2"]["cache"], "~/fn-certcache")
        self.assertEqual(rows["cloud2"]["wrap"], "swarm-build")
        self.assertEqual(rows["cloud2"]["openssl"], "system")
        farm = box_table.farm_rows(FIXED, env)
        self.assertEqual(set(farm["cloud1"]), {"acl2", "sbcl", "cache", "wrap"})

    def test_an_expired_row_is_gone(self):
        env = self.table({"cloud1": {"until": "2026-10-04T15:59:00Z"},
                          "cloud2": {"until": "2026-10-04T19:57:00Z"}})
        self.assertEqual(list(box_table.extra_boxes(FIXED, env, NOW)), ["cloud2"])

    def test_a_fixed_or_malformed_name_or_path_is_refused(self):
        for boxes in ({"hbox": {}}, {"laptop": {}}, {"Cloud 1": {}},
                      {"cloud1": {"cache": "/tank/fn/cert cache"}},
                      {"cloud1": {"like": "elsewhere"}}, {"cloud1": {"openssl": "mine"}}):
            with self.assertRaises(SystemExit, msg=boxes):
                box_table.extra_boxes(FIXED, self.table(boxes), NOW)

    def test_row_prints_shell_assignments_and_refuses_unknown(self):
        env = {**os.environ, **self.table({"cloud1": {"like": "hbox"}})}
        done = subprocess.run([sys.executable, str(ROOT / "tools" / "box_table.py"), "row", "cloud1"],
                              env=env, capture_output=True, text=True, check=True)
        self.assertIn("BASE='/tank/fn/scratch'", done.stdout)
        self.assertIn("WRAP='swarm-build'", done.stdout)
        missing = subprocess.run([sys.executable, str(ROOT / "tools" / "box_table.py"), "row", "cloud9"],
                                 env=env, capture_output=True, text=True)
        self.assertEqual(missing.returncode, 2)


if __name__ == "__main__":
    unittest.main()
