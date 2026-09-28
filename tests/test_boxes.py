"""tools/boxes.sh: per-box load, memory and disk; --pick the lower load per core.

ssh is a local stub on PATH that answers each box's probe with a canned line.
"""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BOXES = ROOT / "tools" / "boxes.sh"


class BoxesTests(unittest.TestCase):
    def run_boxes(self, answers: dict[str, str], *words):
        with tempfile.TemporaryDirectory() as directory:
            ssh = Path(directory) / "ssh"
            cases = "".join(f'    *" {host} "*) printf "%s\\n" "{line}" ;;\n'
                            for host, line in answers.items())
            ssh.write_text('#!/bin/sh\ncase " $* " in\n' + cases + "    *) exit 255 ;;\nesac\n")
            ssh.chmod(0o755)
            env = {**os.environ, "PATH": f"{directory}:{os.environ['PATH']}"}
            return subprocess.run(["sh", str(BOXES), *words], env=env,
                                  capture_output=True, text=True, timeout=60)

    def test_pick_is_the_lower_load_per_core_not_the_lower_load(self):
        done = self.run_boxes({"hbox": "24 12.0 70 24 700 /tank/fn/scratch",
                               "persvati": "8 6.0 60 0 80 /home/e/fn-gates"}, "--pick")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout.strip(), "hbox")  # 0.50/core beats 0.75/core
        self.assertIn("persvati 0.750 load per core", done.stderr)

    def test_an_unreachable_box_is_never_picked_and_none_is_exit_3(self):
        done = self.run_boxes({"persvati": "24 20.0 60 0 80 /x"}, "--pick")
        self.assertEqual(done.stdout.strip(), "persvati")
        self.assertIn("hbox unreachable", done.stderr)
        self.assertEqual(self.run_boxes({}, "--pick").returncode, 3)

    def test_the_listing_counts_the_arc_as_free(self):
        done = self.run_boxes({"hbox": "24 12.0 50 24 700 /tank/fn/scratch"})
        self.assertIn("free mem   74 GiB (ARC 24 GiB of it)", done.stdout)
        self.assertIn("persvati  unreachable", done.stdout)
        self.assertEqual(self.run_boxes({}, "--bogus").returncode, 2)

    def test_pick_passes_over_a_box_reserved_by_someone_else_but_not_ones_own(self):
        lease = "R 1900000000 25 17:05Z curve-lane a scale curve (quiet box)"
        answers = {"hbox": "24 1.0 70 24 700 /tank/fn/scratch\n" + lease,
                   "persvati": "24 12.0 60 0 80 /home/e/fn-gates"}
        with mock_env(FN_BOX_AS="other-lane"):
            done = self.run_boxes(answers, "--pick")
        self.assertEqual(done.stdout.strip(), "persvati")  # hbox is quieter but reserved
        self.assertIn("hbox reserved by curve-lane until 17:05Z (25 min left): a scale curve",
                      done.stderr)
        with mock_env(FN_BOX_AS="curve-lane"):
            self.assertEqual(self.run_boxes(answers, "--pick").stdout.strip(), "hbox")
        with mock_env(FN_BOX_AS="other-lane"):
            held = self.run_boxes(answers, "check", "hbox")
            self.assertEqual(held.returncode, 4)
            self.assertIn("reserved by curve-lane", held.stderr)
            self.assertEqual(self.run_boxes(answers, "check", "persvati").returncode, 0)
            self.assertIn("hbox reserved by curve-lane", self.run_boxes(answers).stdout)
        self.assertEqual(self.run_boxes(answers, "reserve", "hbox", "--why", "x").returncode, 2)

    # waiver-ok: capability -- the lease uses flock(1) and GNU date's -d @N;
    # the laptop (BSD date, no flock) is a machine this tree has not built
    # them for, so the case runs on the build boxes only.
    @unittest.skipUnless(shutil.which("flock") and subprocess.run(
        ["date", "-d", "@0"], capture_output=True).returncode == 0, "needs flock and GNU date")
    def test_reserve_and_release_are_a_lease_on_the_box(self):
        with tempfile.TemporaryDirectory() as directory:
            ssh = Path(directory) / "ssh"
            # The box is this machine with HOME in the scratch directory.
            ssh.write_text('#!/bin/sh\nfor last; do :; done\nHOME=%s exec sh -c "$last"\n' % directory)
            ssh.chmod(0o755)
            env = {**os.environ, "FN_BOXES_SSH": str(ssh)}

            def boxes(who, *words):
                return subprocess.run(["sh", str(BOXES), *words], capture_output=True, text=True,
                                      env={**env, "FN_BOX_AS": who}, timeout=60)
            took = boxes("a", "reserve", "hbox", "--for", "5", "--why", "it's a curve")
            self.assertEqual(took.returncode, 0, took.stderr)
            self.assertIn("hbox reserved by a until", took.stdout)
            self.assertIn("it's a curve", (Path(directory) / ".fn-box-reservation").read_text())
            self.assertEqual(boxes("b", "reserve", "hbox", "--for", "5", "--why", "y").returncode, 4)
            self.assertEqual(boxes("b", "release", "hbox").returncode, 4)
            self.assertEqual(boxes("b", "check", "hbox").returncode, 4)
            self.assertEqual(boxes("a", "check", "hbox").returncode, 0)
            self.assertEqual(boxes("a", "reserve", "hbox", "--for", "9", "--why", "more").returncode, 0)
            self.assertEqual(boxes("a", "release", "hbox").returncode, 0)
            self.assertEqual(boxes("b", "check", "hbox").returncode, 0)
            self.assertEqual(boxes("b", "reserve", "hbox", "--for", "1", "--why", "z").returncode, 0)
            self.assertEqual(boxes("a", "release", "hbox", "--force").returncode, 0)
            self.assertFalse((Path(directory) / ".fn-box-reservation").exists())


class mock_env:
    def __init__(self, **values):
        self.values, self.saved = values, {}

    def __enter__(self):
        for key, value in self.values.items():
            self.saved[key] = os.environ.get(key)
            os.environ[key] = value

    def __exit__(self, *_):
        for key, value in self.saved.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


if __name__ == "__main__":
    unittest.main()
