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


# Gate 04's scratch commit needs an identity; a box or a snapshot tree may
# have none configured (hbox, a git-archive tree: `Author identity unknown').
ENV = dict(os.environ, GIT_AUTHOR_NAME="cut-release-test", GIT_AUTHOR_EMAIL="cut-release-test@invalid",
           GIT_COMMITTER_NAME="cut-release-test", GIT_COMMITTER_EMAIL="cut-release-test@invalid")


PREHISTORY = ["v1.0.0", "v2.0.0", "v3.0.0", "v4.0.0", "v5.0.0"]


class CutReleaseDryRunTests(unittest.TestCase):
    def test_the_local_prefix(self):
        with tempfile.TemporaryDirectory(dir=ROOT / "build") as out:
            r = subprocess.run(["sh", str(ROOT / "tools" / "cut_release.sh"), "--dry-run", "--to", "4", "--out", out],
                               capture_output=True, text=True, timeout=300, env=ENV)
            self.assertEqual(r.returncode, 0, r.stderr)
            verdict = (Path(out) / "verdict.txt").read_text().splitlines()
            self.assertTrue(verdict[-1].startswith("VERDICT DRY-RUN"), verdict[-1])
            self.assertEqual([l.split()[0] for l in verdict if l[:2].isdigit()], ["01", "02", "03", "04"])
            log = (Path(out) / "04-changelog.log").read_text()
            self.assertIn("byte-stable across its own commit", log)

    def gate01(self, version, tags):
        """Gate 01's verdict word for VERSION in a scratch repository holding
        the script, tools/release_sequence.py, the sequence file, VERSION and
        its checklist, with TAGS (each on its own earlier commit)."""
        with tempfile.TemporaryDirectory(dir=ROOT / "build") as tmp:
            repo = Path(tmp) / "repo"
            for rel in ("tools/cut_release.sh", "tools/release_sequence.py", "planning/release-sequence.json"):
                (repo / rel).parent.mkdir(parents=True, exist_ok=True)
                (repo / rel).write_bytes((ROOT / rel).read_bytes())
            git = lambda *a: subprocess.run(["git", "-C", str(repo), *a], check=True, env=ENV,
                                            capture_output=True, text=True).stdout
            git("init", "-q")
            git("add", "-A")
            git("commit", "-q", "--no-gpg-sign", "-m", "base")
            for t in tags:
                git("commit", "-q", "--no-gpg-sign", "--allow-empty", "-m", t)
                git("tag", t)
            (repo / "VERSION").write_text(version + "\n")
            (repo / "planning" / f"release-v{version}.md").write_text("# checklist\n")
            git("add", "-A")
            git("commit", "-q", "--no-gpg-sign", "-m", "cut")
            out = Path(tmp) / "out"
            subprocess.run(["sh", str(repo / "tools" / "cut_release.sh"), "--dry-run", "--to", "1", "--out", str(out)],
                           capture_output=True, text=True, timeout=120, env=ENV, check=True)
            line = next(l for l in (out / "verdict.txt").read_text().splitlines() if l.startswith("01 "))
            return line.split()[2], line

    def test_gate_01_follows_the_release_sequence(self):
        # D37 (planning/release-sequence.json), never a numeric comparison.
        cases = [("6.6.0", [], "GREEN"),
                 ("6.7.0", [], "RED"),
                 ("6.7.0", ["v6.6.0", "v6.6.1", "v6.6.2", "v6.6.3", "v6.6.4"], "RED"),
                 ("6.7.0", ["v6.6.5"], "GREEN"),
                 ("6.6.6.6", ["v6.6.5", "v6.7.0", "v6.7.3"], "RED"),
                 ("6.6.6", ["v6.6.5", "v6.7.0", "v6.7.3"], "GREEN"),
                 ("6.6.6.6", ["v6.6.5", "v6.7.0", "v6.7.3", "v6.6.6"], "GREEN"),
                 # The prehistory tags (DEVHIST.md) are not releases: 6.6.0 is still first.
                 ("6.6.0", PREHISTORY, "GREEN"),
                 ("6.6.1", PREHISTORY, "RED"),
                 ("6.6.1", PREHISTORY + ["v6.6.0"], "GREEN"),
                 ("5.0.0", PREHISTORY[:4], "RED")]
        for version, tags, want in cases:
            word, line = self.gate01(version, tags)
            self.assertEqual(word, want, f"{version} after {tags}: {line}")

    def test_a_bad_vm_name_is_refused(self):
        r = subprocess.run(["sh", str(ROOT / "tools" / "cut_release.sh"), "--dry-run", "--openbsd-vm", "a b"],
                           capture_output=True, text=True, timeout=60)
        self.assertEqual(r.returncode, 2)


if __name__ == "__main__":
    unittest.main()
