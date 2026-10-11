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

    def post_suffix(self, rooms, n=3):
        """fixtures.main post-suffix under mocks; ROOMS is each status's
        (max-history-octets, bytes-used) in order; the gate charge is 50 and
        the reserve 10."""
        from unittest import mock
        import rep_measure
        import msgid_measure
        work = Path(self.temporary.name).resolve() / "base"
        store = work / "store"
        store.mkdir(parents=True, exist_ok=True)
        calls = {"verbs": [], "posted": [], "envs": [], "starts": 0, "stops": 0}
        rooms = list(rooms)

        class Conn:
            def __init__(self, port):
                pass

            def close(self):
                pass

        def run(argv, env=None, check=False, **kw):
            words = [str(w) for w in argv[2:]]
            if words[0] == "operator" and words[2] == "status":
                history, used = rooms.pop(0)
                calls["verbs"].append(["status"])
                out = ("profile format=10 max-transactions=131072 max-history-octets=%d "
                       "max-record-octets=196608\nheadroom transactions-used=10 "
                       "bytes-used=%d history-bound=%d\nmaintenance-reserve octets=10 "
                       "transactions=1 debt=0 held\n" % (history, used, history))
                return subprocess.CompletedProcess(argv, 0, out, "")
            calls["verbs"].append(words[2:] if words[0] == "operator" else words[1:])
            return subprocess.CompletedProcess(argv, 0)

        def start(image, config, env, stderr_path, timeout=3600):
            calls["envs"].append(env)
            calls["starts"] += 1
            self.assertIn(str(store), config.read_text())
            return object(), 1.0, None

        def stop(proc, err):
            calls["stops"] += 1

        report = work / "suffix.json"
        with mock.patch.object(fixtures.subprocess, "run", run), \
                mock.patch.object(rep_measure, "start_owner", start), \
                mock.patch.object(rep_measure, "stop_owner", stop), \
                mock.patch.object(fixtures, "gate_figure", lambda image, octets: 50), \
                mock.patch.object(rep_measure, "post",
                                  lambda conn, i, octets: calls["posted"].append((i, octets))), \
                mock.patch.object(msgid_measure, "free_port", lambda: 1), \
                mock.patch.object(msgid_measure, "Conn", Conn):
            code = fixtures.main(["post-suffix", "/img", str(store), str(n),
                                  "--json", str(report)])
        return code, calls, json.loads(report.read_text()), store

    def test_post_suffix_checkpoints_then_posts_every_record_to_one_owner(self):
        code, calls, report, store = self.post_suffix([(1 << 20, 100), (1 << 20, 200)])
        self.assertEqual(code, 0)
        self.assertEqual(calls["verbs"], [[str(store), "rebind-filesystem"],
                                          [str(store), "checkpoint"], ["status"], ["status"]])
        self.assertEqual(calls["envs"][0]["FN_NATIVE_CHECKPOINT_BUDGET_TEST"], "1")
        self.assertEqual(calls["posted"], [(5000000, 2048), (5000001, 2048), (5000002, 2048)])
        self.assertEqual(report["post_charge"], 100)
        self.assertEqual(report["posted"], 3)
        self.assertTrue((store / "writer.lock").is_file())

    def test_post_suffix_raises_the_history_to_the_gates_bound(self):
        # FIXTURE-CP100K-HISTORY-SIZING: the first post is charged 1 MiB; the
        # other 2 need 11 MiB + 1 x 1 MiB + gate 50 + reserve 10, so 13 MiB.
        code, calls, report, _ = self.post_suffix(
            [(11 << 20, 10 << 20), (11 << 20, 11 << 20), (13 << 20, 11 << 20)])
        self.assertEqual(code, 0)
        self.assertIn(["policy", "set", "max-history-octets", str(13 << 20)], calls["verbs"])
        self.assertEqual((calls["starts"], calls["stops"]), (2, 2))
        self.assertEqual(report["history_needed"], 13 << 20)
        self.assertEqual(len(calls["posted"]), 3)

    def test_post_suffix_refuses_when_the_raise_is_not_in_force(self):
        code, calls, report, _ = self.post_suffix(
            [(11 << 20, 10 << 20), (11 << 20, 11 << 20), (11 << 20, 11 << 20)])
        self.assertEqual(code, 1)
        self.assertEqual(len(calls["posted"]), 1)
        self.assertEqual(calls["stops"], 2)

    def test_the_raise_admits_the_last_post_at_the_gate(self):
        # used + (remaining - 1) x each + gate + reserve, to the MiB.
        self.assertEqual(fixtures.raised_history(11 << 20, 1 << 20, 2, 50, 10), 13 << 20)
        # cp100k on hbox at d8fb738b3: the synthesized average (4,571) under-
        # sized the suffix, refused at post 19,992 under 549,453,824 octets.
        self.assertGreater(fixtures.raised_history(457012000 + 4624, 4624, 19999, 23096, 4096),
                           549453824)

if __name__ == "__main__":
    unittest.main()
