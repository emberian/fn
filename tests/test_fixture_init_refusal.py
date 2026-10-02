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

POSTMEASURE = ROOT / "tools/fixture_scripts/post-identity-index-2026-09-26/postmeasure.py"
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


class CheckpointSuffixTests(unittest.TestCase):
    """cp100k-sfx20k-2k: a 20,000-record suffix over a 100,000-record checkpoint
    (heap-bounds, 2026-09-28: every registered store's capacity capped a suffix
    over syn100k-2k at 2,000 posts)."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-fixture-suffix-")
        self.addCleanup(self.temporary.cleanup)

    def test_the_seed_has_room_for_the_whole_suffix(self):
        self.assertEqual(fixtures.suffix_capacity(100000, 0), 204000)  # syn100k-2k's
        self.assertEqual(fixtures.suffix_capacity(100000, 20000), 244000)
        fixture = fixtures.BY_NAME["cp100k-sfx20k-2k"]
        self.assertEqual(fixture.stores, ("store",))
        self.assertIn("open=checkpoint:100000 suffix=20000", fixture.readme)
        # T (max transactions) holds the seed, the synthesized records and the suffix.
        flags = dict(zip(fixtures.SYNTH_100K[::2], fixtures.SYNTH_100K[1::2]))
        self.assertGreater(int(flags["--max-transactions"]), 1000 + 100000 + 20000)
        self.assertGreater(int(flags["--max-open-suffix"]), 20000)

    def test_post_suffix_checkpoints_then_posts_every_record_to_one_owner(self):
        from unittest import mock
        import rep_measure
        import msgid_measure
        work = Path(self.temporary.name).resolve() / "base"
        store = work / "store"
        store.mkdir(parents=True)
        verbs, posted, envs = [], [], []

        class Conn:
            def __init__(self, port):
                pass

            def close(self):
                pass

        def run(argv, env, check):
            verbs.append(argv[3:])
            return subprocess.CompletedProcess(argv, 0)

        def start(image, config, env, stderr_path, timeout=3600):
            envs.append(env)
            self.assertIn(str(store), config.read_text())
            return object(), 1.0, None

        report = work / "suffix.json"
        with mock.patch.object(fixtures.subprocess, "run", run), \
                mock.patch.object(rep_measure, "start_owner", start), \
                mock.patch.object(rep_measure, "stop_owner", lambda proc, err: None), \
                mock.patch.object(rep_measure, "post",
                                  lambda conn, i, octets: posted.append((i, octets))), \
                mock.patch.object(msgid_measure, "free_port", lambda: 1), \
                mock.patch.object(msgid_measure, "Conn", Conn):
            code = fixtures.main(["post-suffix", "/img", str(store), "3", "--json", str(report)])
        self.assertEqual(code, 0)
        self.assertEqual(verbs, [[str(store), "rebind-filesystem"], [str(store), "checkpoint"]])
        self.assertEqual(envs[0]["FN_NATIVE_CHECKPOINT_BUDGET_TEST"], "1")
        self.assertEqual(posted, [(5000000, 2048), (5000001, 2048), (5000002, 2048)])
        self.assertEqual(json.loads(report.read_text())["posted"], 3)
        self.assertTrue((store / "writer.lock").is_file())


if __name__ == "__main__":
    unittest.main()
