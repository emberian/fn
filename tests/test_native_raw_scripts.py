"""The raw-Lisp native tests, run by something.

tests/native_*_raw.lisp drive deployed host functions under SBCL against
recording stubs, and two of them had a shell wrapper and no runner: no
Makefile target, no unittest module, nothing (found by the owner-defects lane
on 2026-09-22, which wired its own through tests/test_native_owner.py).  A
test nobody runs is a claim, so this module runs every `tests/*_raw.sh`,
one case each, and skips with the reason when no SBCL is found.

The SBCL is the one the image ships on (tests/native_process.py runtime_sbcl:
FN_SBCL, else the runtime named by the FN_NATIVE_HOST image's wrapper, else
`sbcl` on PATH), passed to every script as FN_SBCL: the host code names
symbols an older system SBCL does not export (PKT-614: hbox's /usr/bin/sbcl
2.2.9 lacks sb-bsd-sockets:sockopt-error).
"""
from __future__ import annotations

import os
import pathlib
import subprocess
import unittest

from tests.native_process import runtime_sbcl

ROOT = pathlib.Path(__file__).resolve().parents[1]
SCRIPTS = sorted(ROOT.glob("tests/test_*_raw.sh"))
IMAGE = pathlib.Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
RUNTIME = runtime_sbcl(IMAGE)


@unittest.skipUnless(RUNTIME, "no SBCL runtime for the image and none on PATH")
class RawScriptTests(unittest.TestCase):
    def test_every_raw_script_has_a_case_here(self):
        self.assertTrue(SCRIPTS, "no tests/test_*_raw.sh found")

    def test_every_raw_harness_has_a_runner(self):
        # native_peer_authored_accept_raw.lisp had no runner until
        # entry-guards-2 (2026-09-27) and had drifted from the host.
        runners = " ".join(path.read_text(encoding="utf-8")
                           for path in ROOT.glob("tests/test_*")
                           if path.suffix in (".py", ".sh"))
        unrun = [path.name for path in sorted(ROOT.glob("tests/native_*_raw.lisp"))
                 if path.name not in runners]
        self.assertEqual(unrun, [], "raw harnesses no test runs")

    def run_script(self, script: pathlib.Path) -> None:
        sbcl, env = RUNTIME
        env = dict(env, FN_SBCL=sbcl)
        result = subprocess.run(["sh", str(script)], capture_output=True, text=True,
                                cwd=ROOT, env=env, timeout=600)
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
