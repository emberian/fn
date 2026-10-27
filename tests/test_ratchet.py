"""Every baseline-rewriting tool shrinks only: a raise or a new row is refused
unless planning/repair/ACKS.md carries ratchet:<tool>:<row> (tools/ratchet.py)."""
import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests.scratch_git import run as scratch_git

from tools import clock_unit_check, list_codec_check, loop_call_check, owner_globals_check, ratchet, scenario_suite, throughput_gate

DASH = "—"


class Base(unittest.TestCase):
    def setUp(self):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        self.dir = Path(d.name)
        self.acks = self.dir / "ACKS.md"
        self.acks.write_text("# none\n")
        p = mock.patch.object(ratchet, "ACKS", self.acks)
        p.start()
        self.addCleanup(p.stop)

    def ack(self, tool, row):
        with open(self.acks, "a") as f:
            f.write(f"{ratchet.token(tool, row)} {DASH} decided in the test {DASH} the test\n")

    def quiet(self, fn, *a):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return fn(*a)

    def triad(self, write, read_rows, tool, row):
        """raise refused (file untouched), shrink passes, ACKed raise passes."""
        self.assertEqual(self.quiet(write, 5), 1, "a raise must be refused")
        self.assertEqual(read_rows(), {row: 3}, "a refused write leaves the baseline alone")
        self.assertEqual(self.quiet(write, 2), 0, "a shrink passes")
        self.assertEqual(read_rows(), {row: 2})
        self.ack(tool, row)
        self.assertEqual(self.quiet(write, 5), 0, "an ACKed raise passes")
        self.assertEqual(read_rows(), {row: 5})


class Helper(Base):
    def test_matching_is_exact(self):
        self.ack("t", "a b")
        self.assertEqual(ratchet.refused("t", {"x": 1}, {"x": 2}, self.acks) != [], True)
        self.assertEqual(ratchet.refused("t", {"a b": 1}, {"a b": 2}, self.acks), [])
        self.assertNotEqual(ratchet.refused("other", {"a b": 1}, {"a b": 2}, self.acks), [])

    def test_new_row_and_initial_capture(self):
        self.assertNotEqual(ratchet.refused("t", {}, {"n": 1}, self.acks), [])
        self.assertEqual(ratchet.refused("t", None, {"n": 1}, self.acks), [])
        self.assertEqual(ratchet.refused("t", {"n": 3}, {"n": 3}, self.acks), [])

    def test_a_malformed_ack_does_not_count(self):
        self.acks.write_text(f"ratchet:t:n {DASH} reason only\n")
        self.assertNotEqual(ratchet.refused("t", {"n": 1}, {"n": 2}, self.acks), [])

    def test_scaling_limit_is_the_target_unless_acked(self):
        b = {"article_ratio_target": 10.0, "article_ratio_ceiling": 15.0}
        self.assertEqual(ratchet.scaling_limit(b, self.acks), 10.0)
        self.ack("scaling_baseline", "article_ratio_ceiling")
        self.assertEqual(ratchet.scaling_limit(b, self.acks), 15.0)
        self.assertEqual(ratchet.scaling_limit({**b, "article_ratio_ceiling": 8.0}, self.acks), 10.0)

    def test_tiers_text_reads_the_declared_target(self):
        root = Path(__file__).resolve().parent.parent
        target = scenario_suite.scaling_target(root)
        why = [e[5] for e in scenario_suite.entries(root) if e[3] == "tests.test_native_scaling"][0]
        self.assertIn(f"at most {target}x", why)
        self.assertNotIn("{scaling_ratio_target}", why)


class DeletedBaseline(Base):
    """`git rm` a baseline, then --write any numbers: refused unless the path has
    never had history, or an ACKS.md *initial line says so."""

    def repo(self):
        import subprocess
        root = self.dir / "r"
        (root / "tools").mkdir(parents=True)
        run = lambda *a: scratch_git(["git", "-C", str(root), *a], check=True, capture_output=True)
        run("init", "-q")
        run("config", "user.email", "t@t")
        run("config", "user.name", "t")
        (root / "tools/b.json").write_text("{}")
        run("add", "-f", "tools/b.json")
        run("commit", "-qm", "b")
        (root / "tools/b.json").unlink()
        p = mock.patch.object(ratchet, "ROOT", root)
        p.start()
        self.addCleanup(p.stop)
        return root

    def test_deleted_then_rewritten_is_refused_but_a_never_tracked_path_is_not(self):
        root = self.repo()
        self.assertFalse(ratchet.initial_ok("t", root / "tools/b.json", self.acks))
        self.assertEqual(ratchet.old_rows("t", root / "tools/b.json", dict), {})
        self.assertNotEqual(ratchet.refused("t", ratchet.old_rows("t", root / "tools/b.json", dict),
                                            {"a": 5}, self.acks), [])
        self.assertTrue(ratchet.initial_ok("t", root / "tools/never.json", self.acks))
        self.assertIsNone(ratchet.old_rows("t", root / "tools/never.json", dict))

    def test_an_initial_ack_reopens_the_capture(self):
        root = self.repo()
        self.ack("t", "*initial")
        self.assertTrue(ratchet.initial_ok("t", root / "tools/b.json", self.acks))

    def test_a_tool_refuses_a_deleted_baseline_rewrite(self):
        root = self.repo()
        (root / "tools/loop_call_baseline.json").write_text(json.dumps({"total": 3, "sites": {"f": 3}}))
        import subprocess
        for a in (["add", "-f", "tools/loop_call_baseline.json"], ["commit", "-qm", "l"]):
            scratch_git(["git", "-C", str(root), *a], check=True, capture_output=True)
        path = root / "tools/loop_call_baseline.json"
        path.unlink()
        with mock.patch.object(loop_call_check, "BASELINE", path), \
                mock.patch.object(loop_call_check, "scan", return_value=[]), \
                mock.patch.object(loop_call_check, "counts", return_value={"f": 99}):
            self.assertEqual(self.quiet(loop_call_check.main, ["--write"]), 1)
            self.assertFalse(path.exists())
            self.ack("loop_call_check", "*initial")
            self.ack("loop_call_check", "f")
            self.assertEqual(self.quiet(loop_call_check.main, ["--write"]), 0)


class ListCodec(Base):
    def test_triad(self):
        path = self.dir / "b.json"
        path.write_text(json.dumps({"classes": {}, "sites": {"f.lisp": 3}, "total": 3}))
        read = lambda: json.loads(path.read_text())["sites"]

        def write(n):
            with mock.patch.object(list_codec_check, "BASELINE", path), \
                    mock.patch.object(list_codec_check, "scan", return_value=[]), \
                    mock.patch.object(list_codec_check, "classify"), \
                    mock.patch.object(list_codec_check, "counts", return_value={"f.lisp": n}):
                return list_codec_check.main(["--write"])
        self.triad(write, read, "list_codec_check", "f.lisp")


class LoopCall(Base):
    def test_triad(self):
        path = self.dir / "b.json"
        path.write_text(json.dumps({"total": 3, "sites": {"f.lisp": 3}}))
        read = lambda: json.loads(path.read_text())["sites"]

        def write(n):
            with mock.patch.object(loop_call_check, "BASELINE", path), \
                    mock.patch.object(loop_call_check, "scan", return_value=[]), \
                    mock.patch.object(loop_call_check, "counts", return_value={"f.lisp": n}):
                return loop_call_check.main(["--write"])
        self.triad(write, read, "loop_call_check", "f.lisp")


class ClockUnit(Base):
    def test_triad(self):
        (self.dir / "tools").mkdir()
        path = self.dir / "tools/clock_unit_baseline.json"
        path.write_text(json.dumps({"sites": {"f.lisp": 3}}))
        read = lambda: json.loads(path.read_text())["sites"]

        def write(n):
            found = {"f.lisp": [(i, "+") for i in range(n)]}
            with mock.patch.object(clock_unit_check, "scan", return_value=found):
                return clock_unit_check.main(["--write-baseline", "--root", str(self.dir)])
        self.triad(write, read, "clock_unit_check", "f.lisp")


class OwnerGlobals(Base):
    def test_triad(self):
        path = self.dir / "b.json"
        path.write_text(json.dumps({"f.lisp": 3}))
        read = lambda: {k: v for k, v in json.loads(path.read_text()).items() if not k.startswith("_")}

        def write(n):
            with mock.patch.object(owner_globals_check, "scan",
                                   return_value={"f.lisp": ["g"] * n}):
                return owner_globals_check.main(["--write-baseline", "--root", str(self.dir),
                                                 "--baseline", str(path)])
        self.triad(write, read, "owner_globals_check", "f.lisp")


class ThroughputGate(Base):
    def test_triad(self):
        tg = throughput_gate
        path = self.dir / "throughput-baseline.json"
        path.write_text(json.dumps({"metrics": {m: {"value": 2.0, "floor": 0.5} for m in tg.METRICS}}))
        read = lambda: {"post_median_ms": json.loads(path.read_text())["metrics"]["post_median_ms"]["value"]}

        def write(n):
            run = dict({m: 1.0 for m in tg.METRICS}, post_median_ms=float(n), revision="r" * 40,
                       core_sha256="c")
            for name in ("release", "dev"):
                (self.dir / f"{name}.json").write_text(json.dumps(run))
            args = mock.Mock(release=str(self.dir / "release.json"), dev=str(self.dir / "dev.json"),
                             allow_regression=False)
            with mock.patch.object(tg, "BASELINE", path), mock.patch.object(tg, "ROOT", self.dir):
                try:
                    return tg.write_baseline(args)
                except SystemExit:
                    return 1
        self.assertEqual(self.quiet(write, 3), 1, "a raise must be refused")
        self.assertEqual(read(), {"post_median_ms": 2.0}, "a refused write leaves the baseline alone")
        self.assertEqual(self.quiet(write, 1), 0, "a lowering passes")
        self.assertEqual(read(), {"post_median_ms": 1.0})
        self.ack("throughput_gate", "post_median_ms")
        self.assertEqual(self.quiet(write, 3), 0, "an ACKed raise passes")
        self.assertEqual(read(), {"post_median_ms": 3.0})


if __name__ == "__main__":
    unittest.main()
