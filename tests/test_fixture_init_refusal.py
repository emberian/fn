"""A fixture recipe whose init is refused stops there, saying why (t16).

extract-2 (2026-09-27): syn100k-2k's recipe ran postmeasure.py load under a
profile init now refuses (init-budget-cannot-hold-profile); postmeasure
ignored init's exit and failed later as an owner start on a store that was
"never initialized", and tools/fixtures.py's recipe_synth never read
load.json.  Now postmeasure exits 1 with init's own words before any owner
starts, and every recipe reads load.json through fixtures.check_load.  No
image: the "image" is a stand-in that refuses init as fn does.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fixtures  # noqa: E402

POSTMEASURE = ROOT / "planning/evidence/post-identity-index-2026-09-26/postmeasure.py"
REFUSAL = ("fn: refused init-budget-cannot-hold-profile profile=custom sizing=requested "
           "reservation=188365 MB budget=40960 MB")
STAND_IN = """#!/bin/sh
case " $* " in
  *" init "*) echo "{refusal}" >&2; echo "refused operator init"; exit 1 ;;
  *) touch "$0.started"; exit 7 ;;
esac
"""


class InitRefusalTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-fixture-init-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.image = self.root / "image"
        self.image.write_text(STAND_IN.format(refusal=REFUSAL), encoding="ascii")
        os.chmod(self.image, 0o755)

    def test_postmeasure_load_stops_at_a_refused_init(self):
        work = self.root / "seed"
        done = subprocess.run([sys.executable, str(POSTMEASURE), "load", str(self.image),
                               str(work), "1000"], cwd=ROOT, capture_output=True, text=True,
                              timeout=120)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("init exited 1, no store was made", done.stderr)
        self.assertIn(REFUSAL, done.stderr)
        self.assertFalse(Path(str(self.image) + ".started").exists(),
                         "no owner starts after a refused init")
        load = json.loads((work / "load.json").read_text())
        self.assertEqual((load["init_rc"], load["n"]), (1, 0))

    def test_check_load_refuses_naming_init(self):
        work = self.root / "w"
        work.mkdir()
        (work / "load.json").write_text(json.dumps(
            {"init_rc": 1, "n": 0, "init_tail": REFUSAL}))
        with self.assertRaises(RuntimeError) as caught:
            fixtures.check_load(work, 1000)
        self.assertIn("init_rc=1", str(caught.exception))
        self.assertIn("init-budget-cannot-hold-profile", str(caught.exception))

    def test_check_load_accepts_a_complete_load(self):
        work = self.root / "ok"
        work.mkdir()
        (work / "load.json").write_text(json.dumps({"init_rc": 0, "n": 1000}))
        self.assertEqual(fixtures.check_load(work, 1000)["n"], 1000)

    def test_the_synth_seed_profiles_keep_one_segment(self):
        # The owner's automatic checkpoint rotates the log every K records:
        # the 1,000-record seed must stay in one segment.
        for flags in (fixtures.SYNTH_100K, fixtures.SYNTH_1M):
            k = int(flags[flags.index("--max-open-suffix") + 1])
            self.assertGreater(k, 1000)


if __name__ == "__main__":
    unittest.main()
