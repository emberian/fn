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
        self.assertEqual(rows["cloud2"]["openssl"], "bundled")
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


class EveryToolKnowsEveryBoxTests(unittest.TestCase):
    """A registered box is known to every box-aware tool, or it is half-registered:
    tools/box_qualify.sh's `tools` check reads the same list."""

    def test_a_registered_box_resolves_in_every_box_aware_tool(self):
        with tempfile.TemporaryDirectory() as tmp:
            table = Path(tmp) / "boxes.json"
            table.write_text(json.dumps({"boxes": {"rent9": {"like": "hbox", "cores": 4,
                                                             "until": "2999-01-01T00:00:00Z",
                                                             "qualified": {"ok": True}}}}))
            env = {**os.environ, "FN_BOXES_FILE": str(table)}
            probe = (
                "import sys, subprocess; sys.path.insert(0, 'tools')\n"
                "import acl2_slots, certs, proof_repl, gate_reap, evidence_manifests, box_table, boxq\n"
                "b = 'rent9'\n"
                "missing = [n for n, ok in [('farm HOSTS', b in acl2_slots.farm_hosts()),"
                " ('certs.REMOTE_CACHES', b in certs.REMOTE_CACHES),"
                " ('proof_repl.REMOTE_TREES', b in proof_repl.REMOTE_TREES),"
                " ('gate_reap', b in gate_reap.DEFAULT_ROOTS and b in gate_reap.DEFAULT_LOCKS),"
                " ('evidence_manifests', b in evidence_manifests.BOX_ROOTS),"
                " ('box_table env', box_table.env_line(b) is not None),"
                " ('boxq', b in boxq.known_boxes()),"
                " ('native_box.sh', subprocess.run(['sh', 'tools/native_box.sh', b, '.'], capture_output=True).returncode == 0)]"
                " if not ok]\n"
                "print(' '.join(missing))\n")
            done = subprocess.run([sys.executable, "-c", probe], cwd=ROOT, env=env,
                                  capture_output=True, text=True, timeout=120)
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual(done.stdout.strip(), "", f"half-registered: {done.stdout.strip()}")
            dry = subprocess.run(["sh", "tools/hbox_native.sh", "--box", "rent9", "--dry-run", "--name", "t",
                                  "--label", "l", "HEAD", "tests.test_native_owner"], cwd=ROOT, env=env,
                                 capture_output=True, text=True, timeout=60)
            self.assertEqual(dry.returncode, 0, dry.stderr[-500:])


if __name__ == "__main__":
    unittest.main()
