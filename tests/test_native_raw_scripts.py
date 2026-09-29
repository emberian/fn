"""The raw-Lisp native tests, run by something.

tests/native_*_raw.lisp drive deployed host functions under SBCL against
recording stubs, and two of them had a shell wrapper and no runner: no
Makefile target, no unittest module, nothing (found by the owner-defects lane
on 2026-09-22, which wired its own through tests/test_native_owner.py).  A
test nobody runs is a claim, so this module runs every `tests/*_raw.sh`,
one case each, and skips with the reason when no SBCL is found.

The SBCL is the one the image ships on (tests/native_harness.py runtime_sbcl:
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

from tests.native_harness import runtime_sbcl

ROOT = pathlib.Path(__file__).resolve().parents[1]
# Every script whose header says `# witness: raw` (tools/witness_check.py):
# the *_raw.sh wrappers and the other sbcl-only witnesses, which nothing ran
# until 2026-09-29 (five were red at load, found by tooling-truth-2).
RAW_MARK = "# witness: raw"
SCRIPTS = sorted(path for path in ROOT.glob("tests/*.sh")
                 if RAW_MARK in path.read_text(encoding="utf-8", errors="replace").splitlines())
# Red when first run (hbox, the toolchain SBCL, 2026-09-29 at 02bd7993e): the
# harness drifted from the host it loads.  Expected failures, so each is
# reported every run and one that passes again fails as an unexpected
# success: drop it here then.  Shrink-only.
KNOWN_BROKEN = {
    "test_native_live_config_cache_raw.sh":
        "its stub core refuses FN-NATIVE-ADMIN-HOST-OWNER-REQUESTP (owner: online-reclaim's host call)",
    "test_native_feed_peer_octets.sh":
        "FNN-OWNER-TRANSIT-SERIALIZED undefined: the harness predates host/native/feed-service's owner transit",
    "test_native_io_progress.sh":
        "FN-OUTCOME-HOST-CONDITION-EXIT-CODE undefined: the harness predates io.lisp's outcome map",
    "test_native_owner_publication.sh":
        "expected FNN-STORE-ERROR, got ACL2::W undefined (SCN-027's witness)",
}
IMAGE = pathlib.Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
RUNTIME = runtime_sbcl(IMAGE)


@unittest.skipUnless(RUNTIME, "no SBCL runtime for the image and none on PATH")
class RawScriptTests(unittest.TestCase):
    def test_every_raw_script_has_a_case_here(self):
        self.assertTrue(SCRIPTS, "no tests/*.sh marked raw found")
        self.assertEqual(sorted(set(KNOWN_BROKEN) - {s.name for s in SCRIPTS}), [],
                         "KNOWN_BROKEN names a script that is gone or not raw")

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
        self.assertRegex(result.stdout.splitlines()[-1].lower(), r"\bpass(ed)?\b",
                      f"{script.name} did not end with its passing line")


def _add_cases() -> None:
    for script in SCRIPTS:
        name = "test_" + script.stem.removeprefix("test_")

        def case(self, script=script):
            self.run_script(script)

        if script.name in KNOWN_BROKEN:
            case = unittest.expectedFailure(case)

        setattr(RawScriptTests, name, case)


_add_cases()

if __name__ == "__main__":
    unittest.main()
