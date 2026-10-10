"""The three make-check steps that need the certified world run where it is.

On a tree without certificates or an ACL2 launcher, protocol_emit --wire,
host_check's translate and system_books exit 2 with NOT RUN, a capability
skip that tools/check_steps.py does not count red (coordinator ruling
2026-10-10, MAKE-CHECK-CERT-WORLD-NOT-RUN).  The condition of that ruling is
that a tree WITH the world runs them, so nothing reaches dev skipped: this
module is that witness, on the train's box step and any certified tree.
"""
import os
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

STEPS = (
    ("protocol_emit", [sys.executable, "tools/protocol_emit.py", "--wire", "--check"]),
    ("host_check", [sys.executable, "tools/host_check.py"]),
    ("system_books", [sys.executable, "tools/system_books.py", "check"]),
)


def world() -> str | None:
    """Why this tree cannot run the steps, or None when it can."""
    if not os.environ.get("FN_ACL2"):
        return "no ACL2 launcher (FN_ACL2)"
    for book in ("books/wire-export", "books/image-world", "books/image-world-dtn"):
        if not (ROOT / (book + ".cert")).is_file():
            return "no certificate for " + book
    return None


class CertifiedWorldTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        missing = world()
        if missing:
            raise unittest.SkipTest("capability -- " + missing +
                                    "; the train's box step runs this module")

    def test_each_world_step_runs_rather_than_reporting_not_run(self):
        for name, command in STEPS:
            with self.subTest(step=name):
                done = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                      timeout=3600)
                said = done.stdout + done.stderr
                self.assertNotEqual(done.returncode, 2, said[-2000:])
                self.assertNotIn("NOT RUN", said, said[-2000:])


if __name__ == "__main__":
    unittest.main()
