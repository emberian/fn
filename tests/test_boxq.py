"""tools/boxq.py: placement by free capacity, priority, fill, hbox's rule, native shards.

The boxes are a box table in a temporary file and canned probes; a job's runner is
a stub that records the placement (or, for the end-to-end case, the real runner
with --kind cmd running a local shell command)."""
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import boxq  # noqa: E402

SET = "6107ceb56d760f11d5d29b134cc5c664b8542465"


class Args:
    def __init__(self, **kw):
        self.kind = kw.get("kind", "cmd")
        self.priority = kw.get("priority", "lane")
        self.box = kw.get("box")
        self.slots = kw.get("slots")
        self.image_set = kw.get("image_set")
        self.rev = kw.get("rev")
        self.images = kw.get("images")
        self.mem = None
        self.root = kw.get("root", str(ROOT))
        self.lane = kw.get("lane", "lane-a")
        self.note = None
        self.tests = kw.get("tests", [])
        self.extra = kw.get("extra", ["true"])


class BoxqTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.dir = base / "boxq"
        table = base / "boxes.json"
        table.write_text(json.dumps({"boxes": {
            "big": {"like": "hbox", "cores": 32, "until": "2999-01-01T00:00:00Z"},
            "small": {"like": "hbox", "cores": 8, "until": "2999-01-01T00:00:00Z"},
            "gone": {"like": "hbox", "cores": 8, "until": "2000-01-01T00:00:00Z"}}}))
        self.env = {"FN_BOXES_FILE": str(table), "FN_BOXQ_DIR": str(self.dir)}
        self.saved = {k: os.environ.get(k) for k in self.env}
        os.environ.update(self.env)
        self.probe = {"big": {"cores": 32, "load": 0.5, "mem": 120, "sets": [SET]},
                      "small": {"cores": 8, "load": 0.2, "mem": 28, "sets": [SET]},
                      "hbox": {"cores": 24, "load": 3.0, "mem": 80, "sets": [SET]},
                      "persvati": {"cores": 24, "load": 1.0, "mem": 60, "sets": []}}
        self.saved_probe = boxq.PROBE, boxq.PROBE_TTL
        boxq.PROBE = lambda box: self.probe.get(box)
        boxq.PROBE_TTL = 0          # every pump sees the probe as it is now
        self.launched = []

    def tearDown(self):
        boxq.PROBE, boxq.PROBE_TTL = self.saved_probe
        for k, v in self.saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        self.tmp.cleanup()

    def launch(self, job, directory):
        self.launched.append((job["id"], job["box"], job["slots"]))
        return os.getpid()   # alive: the job stays running

    def submit(self, **kw):
        return boxq.submit(Args(**kw), self.dir)

    def state(self):
        return boxq.read_state(self.dir)["jobs"]

    def test_a_job_goes_to_the_box_with_the_most_free_cores_never_hbox_or_the_laptop(self):
        job = self.submit(kind="certify-lane", extra=["--lane"])
        boxq.pump(self.dir, self.launch)
        self.assertEqual(self.launched, [(job, "big", 8)])
        self.probe["big"]["load"] = 30.0
        second = self.submit(kind="certify-lane", extra=["--lane"])
        boxq.pump(self.dir, self.launch)
        self.assertEqual(self.launched[-1][:2], (second, "small"))
        self.assertNotIn("gone", [b for _, b, _ in self.launched])

    def test_a_box_is_never_given_more_cores_than_it_has_free(self):
        self.probe["big"] = None                    # unreachable
        for _ in range(3):
            self.submit(kind="certify-lane", extra=["--lane"])
        boxq.pump(self.dir, self.launch)
        on_small = [s for _, b, s in self.launched if b == "small"]
        self.assertLessEqual(sum(on_small), 8)
        waiting = [j for j in self.state().values() if j["state"] == "queued"]
        self.assertTrue(waiting and all("small has" in (j["why"] or "") or "unreachable" in (j["why"] or "")
                                        for j in waiting), waiting)

    def test_priority_orders_the_queue_and_fill_waits_behind_a_waiting_job(self):
        self.probe["big"] = None
        self.probe["small"]["load"] = 7.5           # no room for anyone
        fill = self.submit(kind="cmd", priority="fill", slots=1)
        lane = self.submit(kind="certify-lane", extra=["--lane"])
        integ = self.submit(kind="certify-lane", priority="integrator", extra=["--lane"])
        boxq.pump(self.dir, self.launch)
        self.assertEqual(self.launched, [])
        self.probe["small"]["load"] = 0.0
        boxq.pump(self.dir, self.launch)
        self.assertEqual(self.launched[0][0], integ)
        self.assertNotIn(fill, [j for j, _, _ in self.launched])
        self.assertEqual(self.state()[fill]["why"], "fill waits while a higher-priority job waits")
        self.assertEqual(self.state()[lane]["state"], "queued")

    def test_fill_keeps_a_quarter_of_the_box_free(self):
        self.probe["big"] = None
        self.probe["small"]["load"] = 4.5           # 3.5 free, a quarter of 8 is 2 -> 1.5 for fill
        job = self.submit(kind="cmd", priority="fill", slots=2)
        boxq.pump(self.dir, self.launch)
        self.assertEqual(self.launched, [])
        self.assertIn("kept free from fill", self.state()[job]["why"])

    def test_hbox_only_for_image_sets_or_by_name_and_one_certify_at_a_time(self):
        a = self.submit(kind="image-set", extra=["true"])
        b = self.submit(kind="image-set", extra=["true"])
        boxq.pump(self.dir, self.launch)
        self.assertEqual([(j, box) for j, box, _ in self.launched], [(a, "hbox")])
        self.assertEqual(self.state()[b]["why"], "hbox runs one certify at a time")
        self.assertEqual(self.launched[0][2], boxq.HBOX_JOBS)
        c = self.submit(kind="cmd", box="persvati", slots=2)
        boxq.pump(self.dir, self.launch)
        self.assertIn((c, "persvati"), [(j, box) for j, box, _ in self.launched])

    def test_hbox_load_cap(self):
        self.probe["hbox"]["load"] = 15.0
        job = self.submit(kind="cmd", box="hbox", slots=4)
        boxq.pump(self.dir, self.launch)
        self.assertEqual(self.launched, [])
        self.assertIn("hbox has", self.state()[job]["why"])

    def test_a_native_job_shards_over_the_boxes_holding_the_set_and_splits_long_modules(self):
        timings = {"tests": {f"tests.test_long.T.test_{i}": 100.0 for i in range(8)}, "modules": {}}
        timings["tests"].update({"tests.test_short.S.test_a": 5.0})
        self.dir.mkdir(parents=True, exist_ok=True)
        (self.dir / "timings.json").write_text(json.dumps(timings))
        self.probe["small"]["sets"] = []            # small cannot take it
        self.probe["hbox"]["sets"] = [SET]
        job = self.submit(kind="native", image_set=SET, tests=["tests.test_long", "tests.test_short"])
        boxq.pump(self.dir, self.launch)
        st = self.state()
        self.assertEqual(st[job]["state"], "split")
        kids = [st[k] for k in st[job]["shards"]]
        self.assertEqual({k["box"] for k in kids}, {"big"})
        self.assertEqual(len({k["label"] for k in kids} | {st[job]["label"]}), len(kids) + 1)
        tests = [t for k in kids for t in k["tests"]]
        self.assertIn("tests.test_long.T.test_3", tests)     # exploded into its tests
        self.assertIn("tests.test_short", tests)
        # Both boxes holding it: the work spreads.
        self.probe["small"]["sets"] = [SET]
        job2 = self.submit(kind="native", image_set=SET, tests=["tests.test_long"])
        boxq.pump(self.dir, self.launch)
        kids = [self.state()[k] for k in self.state()[job2]["shards"]]
        self.assertEqual({k["box"] for k in kids}, {"big", "small"})

    def test_a_fill_native_job_leaves_each_box_its_reserve(self):
        timings = {"tests": {f"tests.test_long.T.test_{i}": 100.0 for i in range(40)}, "modules": {}}
        self.dir.mkdir(parents=True, exist_ok=True)
        (self.dir / "timings.json").write_text(json.dumps(timings))
        job = self.submit(kind="native", priority="fill", image_set=SET, tests=["tests.test_long"])
        boxq.pump(self.dir, self.launch)
        st = self.state()
        for kid in (st[k] for k in st[job]["shards"]):
            cores = {"big": 32, "small": 8}[kid["box"]]
            self.assertLessEqual(kid["slots"] * boxq.SHAPE["native"][0], cores * (1 - boxq.FILL_RESERVE) + 1, kid)

    def test_pack_is_longest_first(self):
        plan = boxq.pack([("a", 9), ("b", 5), ("c", 4), ("d", 3)], {"x": 1, "y": 1})
        loads = {box: sum({"a": 9, "b": 5, "c": 4, "d": 3}[u] for u in units) for box, units in plan.items()}
        self.assertEqual(sorted(loads.values()), [9, 12])

    def test_end_to_end_runner_records_a_result_line_and_wait_returns_the_verdict(self):
        ok = self.submit(kind="cmd", box="small", slots=1, extra=['test "$BOXQ_BOX" = small'])
        red = self.submit(kind="cmd", box="small", slots=1, extra=["exit 1"])
        boxq.pump(self.dir)                          # the real runner, a local command
        out = io.StringIO()
        self.assertEqual(boxq.wait(ok, self.dir, poll=0.2, out=out), 0, out.getvalue())
        self.assertEqual(boxq.wait(red, self.dir, poll=0.2, out=out), 1, out.getvalue())
        rows = [json.loads(l) for l in (self.dir / "results.jsonl").read_text().splitlines()]
        self.assertEqual({r["id"]: r["verdict"] for r in rows}, {ok: "OK", red: "RED"})
        self.assertTrue(all(r["sha_submit"] and r["box"] == "small" for r in rows))

    def test_status_names_each_box_and_the_queue(self):
        self.submit(kind="cmd", box="small", slots=1)
        out = io.StringIO()
        boxq.status(self.dir, out=out)
        text = out.getvalue()
        for word in ("big", "small", "hbox", "queue: 1 waiting"):
            self.assertIn(word, text)
        self.assertNotIn("gone", text)

    def test_timings_are_learned_from_budget_lines(self):
        line = 'FN_TEST_BUDGET_RESULT {"module": "tests.m", "timings": [["tests.m.C.t1", 3.5], ["tests.m.C.t2", 1.0]]}'
        self.assertEqual(boxq.merge_timings(self.dir, line), 1)
        t = boxq.load_timings(self.dir)
        self.assertEqual(t["modules"]["tests.m"], 4.5)
        self.assertEqual(boxq.predicted("tests.m.C", t), 4.5)


if __name__ == "__main__":
    unittest.main()
