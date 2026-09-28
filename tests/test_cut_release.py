"""tools/cut_release.sh: a dry run of its local prefix (--to 4) on HEAD.

Gate 04 regenerates CHANGELOG.md at REV and checks that the file survives its
own commit byte for byte (a scratch commit onto REV, no ref moved); --to
stops after the named gate and a dry run never stops at a red."""
from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


# A git-archive snapshot on a box has no git identity (openbsd-datasize,
# 2026-09-27); the test names one rather than reading the user's.
IDENTITY = {"GIT_AUTHOR_NAME": "fn test", "GIT_AUTHOR_EMAIL": "test@fn.invalid",
            "GIT_COMMITTER_NAME": "fn test", "GIT_COMMITTER_EMAIL": "test@fn.invalid"}


class CutReleaseDryRunTests(unittest.TestCase):
    def test_the_local_prefix(self):
        with tempfile.TemporaryDirectory(dir=ROOT / "build") as out:
            r = subprocess.run(["sh", str(ROOT / "tools" / "cut_release.sh"), "--dry-run", "--to", "4", "--out", out],
                               capture_output=True, text=True, timeout=300,
                               env={**os.environ, **IDENTITY})
            self.assertEqual(r.returncode, 0, r.stderr)
            verdict = (Path(out) / "verdict.txt").read_text().splitlines()
            self.assertTrue(verdict[-1].startswith("VERDICT DRY-RUN"), verdict[-1])
            self.assertEqual([l.split()[0] for l in verdict if l[:2].isdigit()], ["01", "02", "03", "04"])
            log = (Path(out) / "04-changelog.log").read_text()
            self.assertIn("byte-stable across its own commit", log)

    def test_a_bad_vm_name_is_refused(self):
        r = subprocess.run(["sh", str(ROOT / "tools" / "cut_release.sh"), "--dry-run", "--openbsd-vm", "a b"],
                           capture_output=True, text=True, timeout=60)
        self.assertEqual(r.returncode, 2)


if __name__ == "__main__":
    unittest.main()
