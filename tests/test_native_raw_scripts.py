"""The raw SBCL harnesses, every one run by something.

A raw harness (tests/native_*_raw.lisp) reads deployed host source and the
ACL2 definitions it calls, evaluates them in a plain SBCL and drives them
against recording stubs (docs/testing.md).  Until 2026-10-04 each needed a
runner of its own -- a one-line tests/*.sh wrapper or a test module naming
it -- and 30 had neither: each was run once by hand and nothing re-ran it.
So this module DISCOVERS them: every tests/native_*_raw.lisp (and *_raw-mock.lisp) is either

  * named by another test module or tests/*.sh script, which runs it (with
    the arguments, fixture directory or ACL2 world it needs), or
  * run here, one case each, as `sbcl --noinform --script FILE` from the
    tree's root, passing when it exits 0 and its last line says PASS.

A tests/*.sh script whose header says `# witness: raw` (tools/witness_check.py)
is more than a harness -- tests/test_native_crypto_saved_image.sh saves a
core and starts it -- and is run here too, one case each, with `sh`.

There is no third way: a harness nothing names is run here, so adding one
needs no wiring and none can go unrun.

The SBCL is the one the image ships on (tests/native_harness.py runtime_sbcl:
FN_SBCL, else the runtime named by the FN_NATIVE_HOST image's wrapper, else
`sbcl` on PATH), also passed to each harness as FN_SBCL: the host code names
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
HARNESSES = sorted([*ROOT.glob("tests/native_*_raw.lisp"), *ROOT.glob("tests/native_*_raw-mock.lisp")])


def runners_of(harness: pathlib.Path, root: pathlib.Path = ROOT) -> list[str]:
    """The test modules and tests/*.sh scripts other than this one that name HARNESS."""
    here = pathlib.Path(__file__).name
    return sorted(path.name for path in root.glob("tests/test_*")
                  if path.suffix in (".py", ".sh") and path.name != here
                  and harness.name in path.read_text(encoding="utf-8", errors="replace"))


DIRECT = [harness for harness in HARNESSES if not runners_of(harness)]
RAW_MARK = "# witness: raw"
SCRIPTS = sorted(path for path in ROOT.glob("tests/*.sh")
                 if RAW_MARK in path.read_text(encoding="utf-8", errors="replace").splitlines())
IMAGE = pathlib.Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
RUNTIME = runtime_sbcl(IMAGE)


class DiscoveryTests(unittest.TestCase):
    def test_there_are_harnesses_to_run(self):
        self.assertTrue(HARNESSES, "no tests/native_*_raw.lisp found")
        self.assertTrue(DIRECT, "every raw harness is named by another runner; "
                                "check the discovery, not the tree")

    def test_no_wrapper_only_execs_a_harness(self):
        # A tests/*.sh whose only command runs one harness under --script
        # duplicates this module and hides the harness from it.
        wrappers = []
        for script in sorted(ROOT.glob("tests/*.sh")):
            commands = [line.strip() for line in
                        script.read_text(encoding="utf-8", errors="replace").splitlines()
                        if line.strip() and not line.lstrip().startswith("#")
                        and line.strip() not in ("set -eu", 'cd "$(dirname "$0")/.."')]
            if len(commands) == 1 and "--script tests/native_" in commands[0]:
                wrappers.append(script.name)
        self.assertEqual(wrappers, [], "delete these: tests/test_native_raw_scripts.py "
                                       "runs every unnamed harness itself")


@unittest.skipUnless(RUNTIME, "no SBCL runtime for the image and none on PATH")
class RawHarnessTests(unittest.TestCase):
    def run_harness(self, harness: pathlib.Path) -> None:
        sbcl, env = RUNTIME
        command = ([sbcl, "--noinform", "--script", str(harness.relative_to(ROOT))]
                   if harness.suffix == ".lisp" else ["sh", str(harness.relative_to(ROOT))])
        result = subprocess.run(command, capture_output=True, text=True, cwd=ROOT,
                                env=dict(env, FN_SBCL=sbcl), stdin=subprocess.DEVNULL,
                                timeout=600)
        tail = f"{result.stdout[-2000:]}\n{result.stderr[-2000:]}"
        self.assertEqual(result.returncode, 0,
                         f"{harness.name} exited {result.returncode}:\n{tail}")
        lines = result.stdout.strip().splitlines()
        self.assertTrue(lines and "PASS" in lines[-1].upper(),
                        f"{harness.name} did not end with its passing line:\n{tail}")


def _add_cases() -> None:
    for harness in DIRECT + SCRIPTS:
        def case(self, harness=harness):
            self.run_harness(harness)
        setattr(RawHarnessTests, "test_" + harness.stem.removeprefix("native_").replace("-", "_"), case)


_add_cases()

if __name__ == "__main__":
    unittest.main()
