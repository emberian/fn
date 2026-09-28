"""tools/boxes.sh: per-box load, memory and disk; --pick the lower load per core.

ssh is a local stub on PATH that answers each box's probe with a canned line.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
BOXES = ROOT / "tools" / "boxes.sh"


class BoxesTests(unittest.TestCase):
    def run_boxes(self, answers: dict[str, str], *words):
        with tempfile.TemporaryDirectory() as directory:
            ssh = Path(directory) / "ssh"
            cases = "".join(f'    *" {host} "*) echo "{line}" ;;\n'
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


if __name__ == "__main__":
    unittest.main()
