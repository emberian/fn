"""The raw-Lisp native tests, run by something.

tests/native_*_raw.lisp drive deployed host functions under SBCL against
recording stubs, and two of them had a shell wrapper and no runner: no
Makefile target, no unittest module, nothing (found by the owner-defects lane
on 2026-09-22, which wired its own through tests/test_native_owner.py).  A
test nobody runs is a claim, so this module runs every `tests/*_raw.sh`,
one case each, and skips with the reason when SBCL is not on PATH.
"""
from __future__ import annotations

import pathlib
import shutil
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPTS = sorted(ROOT.glob("tests/test_*_raw.sh"))


@unittest.skipUnless(shutil.which("sbcl"), "no sbcl on PATH")
class RawScriptTests(unittest.TestCase):
    def test_every_raw_script_has_a_case_here(self):
        self.assertTrue(SCRIPTS, "no tests/test_*_raw.sh found")

    def run_script(self, script: pathlib.Path) -> None:
        result = subprocess.run(["sh", str(script)], capture_output=True, text=True,
                                cwd=ROOT, timeout=600)
        self.assertEqual(result.returncode, 0,
                         f"{script.name} exited {result.returncode}:\n"
                         f"{result.stdout[-2000:]}\n{result.stderr[-2000:]}")
        self.assertIn("passed", result.stdout.splitlines()[-1],
                      f"{script.name} did not end with its passing line")


def _add_cases() -> None:
    for script in SCRIPTS:
        name = "test_" + script.stem.removeprefix("test_")

        def case(self, script=script):
            self.run_script(script)

        setattr(RawScriptTests, name, case)


_add_cases()

if __name__ == "__main__":
    unittest.main()
