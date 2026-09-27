"""tools/cert_cache_sync.py: what a sync copies, without a box."""
from __future__ import annotations

import io
import json
import pathlib
import subprocess
import sys
import unittest
from contextlib import redirect_stdout
from types import SimpleNamespace

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import cert_cache_sync  # noqa: E402


class PlanTests(unittest.TestCase):
    SCANNED = [("k1/o1", "tc-a"), ("k2/o1", "tc-b"), ("k3/o2", "tc-a"), ("k4/o1", None)]

    def test_copies_only_absent_entries_of_a_toolchain_the_target_uses(self):
        decided = cert_cache_sync.plan(self.SCANNED, {"k3/o2"}, {"tc-a"}, False)
        self.assertEqual(decided["copy"], ["k1/o1"])
        self.assertEqual((decided["scanned"], decided["present"], decided["other_toolchain"]),
                         (4, 1, 2))
        self.assertEqual(decided["other_identities"], ["none", "tc-b"])
        every = cert_cache_sync.plan(self.SCANNED, set(), {"tc-a"}, True)
        self.assertEqual(len(every["copy"]), 4)

    def test_a_dry_run_reports_disjoint_toolchains_and_copies_nothing(self):
        calls = []

        def run(command, input="", capture_output=False, text=False, **_):
            calls.append(command)
            script = command[-1]
            if " scan " in script:
                out = "\n".join(json.dumps(item) for item in self.SCANNED[:2])
            elif " have " in script:
                out = ""
            else:
                out = json.dumps({"tc-z": 400})
            return SimpleNamespace(returncode=0, stdout=out, stderr="")

        printed = io.StringIO()
        with redirect_stdout(printed):
            self.assertEqual(cert_cache_sync.sync("hbox", "persvati", 24, dry_run=True,
                                                  run=run), 0)
        self.assertIn("2 entries changed in the last 24 h; 0 already there; 0 to copy; "
                      "2 left", printed.getvalue())
        self.assertIn("one toolchain on both boxes", printed.getvalue())
        self.assertEqual([command[1] for command in calls], ["hbox", "persvati", "persvati"])
        self.assertFalse(any(command[0] == "rsync" for command in calls))

    def test_the_remote_script_runs_against_a_local_cache(self):
        import tempfile
        with tempfile.TemporaryDirectory() as temporary:
            cache = pathlib.Path(temporary)
            (cache / "k1" / "o1").mkdir(parents=True)
            (cache / "k1" / "o1" / "meta.json").write_text(json.dumps(
                {"toolchain_identity": "tc-a"}))
            (cache / "k2" / "o1").mkdir(parents=True)  # no meta: never copied
            scan = subprocess.run([sys.executable, "-c", cert_cache_sync.REMOTE, "scan",
                                   str(cache), "0"], capture_output=True, text=True)
            self.assertEqual(scan.stdout.splitlines(), ['["k1/o1", "tc-a"]'])
            have = subprocess.run([sys.executable, "-c", cert_cache_sync.REMOTE, "have",
                                   str(cache)], input="k1/o1\nk2/o1\n",
                                  capture_output=True, text=True)
            self.assertEqual(have.stdout.split(), ["k1/o1"])


if __name__ == "__main__":
    unittest.main()
