"""The box step's artifacts are read from build/, and a committed copy that
reappears is refused by name (coordinator ruling 2026-10-09 19:50 on the
registers DECISION): tools/box_artifacts.py for specs/wire-grammar.json."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests.scratch_git import run as scratch_git

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import box_artifacts  # noqa: E402


def git(root: Path, *args: str) -> str:
    return scratch_git(["git", "-C", str(root), *args], check=True, capture_output=True,
                          text=True).stdout.strip()


class BoxArtifacts(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        git(self.root, "init", "-q")
        git(self.root, "config", "user.email", "t@example.invalid")
        git(self.root, "config", "user.name", "t")
        (self.root / "books").mkdir()
        (self.root / "books" / "a.lisp").write_text("(a)\n")
        git(self.root, "add", "books/a.lisp")
        git(self.root, "commit", "-q", "-m", "one")
        self.head = git(self.root, "rev-parse", "HEAD")

    def emit(self, name="wire-grammar.json", doc=None, sha=None):
        (self.root / "build" / "box").mkdir(parents=True, exist_ok=True)
        (self.root / "build" / "box" / name).write_text(json.dumps(doc or {"entries": []}))
        box_artifacts.write_stamp(self.root, sha or self.head, "hbox", sha or self.head)

    def test_current_artifact_is_read(self):
        self.emit(doc={"entries": [{"name": "fn-x"}]})
        self.assertEqual(box_artifacts.load("wire-grammar.json", self.root)["entries"][0]["name"],
                         "fn-x")

    def test_absent_artifact_is_refused_by_name(self):
        with self.assertRaisesRegex(box_artifacts.Refused, r"build/box/wire-grammar.json is absent"):
            box_artifacts.load("wire-grammar.json", self.root)

    def test_committed_copy_is_refused_even_beside_a_current_artifact(self):
        for name, committed in box_artifacts.ARTIFACTS.items():
            self.emit(name)
            target = self.root / committed
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("{}")
            with self.assertRaisesRegex(box_artifacts.Refused, "is committed again"):
                box_artifacts.load(name, self.root)
            target.unlink()

    def test_another_historys_artifact_is_refused(self):
        git(self.root, "checkout", "-q", "-b", "other")
        (self.root / "books" / "b.lisp").write_text("(b)\n")
        git(self.root, "add", "books/b.lisp")
        git(self.root, "commit", "-q", "-m", "other")
        other = git(self.root, "rev-parse", "HEAD")
        git(self.root, "checkout", "-q", "-")
        self.emit(sha=other)
        with self.assertRaisesRegex(box_artifacts.Refused, "not an ancestor of HEAD"):
            box_artifacts.load("wire-grammar.json", self.root)

    def test_an_ancestors_artifact_is_read_and_its_lag_reported(self):
        self.emit()
        (self.root / "books" / "a.lisp").write_text("(a changed)\n")
        git(self.root, "commit", "-q", "-am", "two")
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            box_artifacts.load("wire-grammar.json", self.root)
        self.assertIn("predates 1 change(s)", err.getvalue())
        self.assertIn("books/a.lisp", err.getvalue())

    def test_unknown_name_is_refused(self):
        with self.assertRaises(box_artifacts.Refused):
            box_artifacts.path("teeth-obligations.json", self.root)


class ScratchGitSigning(unittest.TestCase):
    def test_scratch_commits_and_tags_ignore_global_and_system_signing(self):
        import os
        from unittest import mock
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            global_config = base / "global.gitconfig"
            system_config = base / "system.gitconfig"
            config = ("[commit]\n gpgsign = true\n[tag]\n gpgsign = true\n"
                      "[gpg]\n program = /signing-must-not-run\n"
                      "[fixture]\n inherited = yes\n")
            global_config.write_text(config)
            system_config.write_text(config)
            with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(global_config),
                                              "GIT_CONFIG_SYSTEM": str(system_config)}):
                repo = base / "repo"
                scratch_git(["git", "init", "-q", "-b", "main", str(repo)], check=True)
                git(repo, "config", "user.email", "t@example.invalid")
                git(repo, "config", "user.name", "t")
                for setting in ("commit.gpgsign", "tag.gpgsign"):
                    self.assertEqual(git(repo, "config", "--local", "--get", setting), "false")
                inherited = scratch_git(["git", "-C", str(repo), "config", "--get",
                                         "fixture.inherited"], capture_output=True)
                self.assertEqual(inherited.returncode, 1)
                git(repo, "commit", "-q", "--allow-empty", "-m", "unsigned")
                git(repo, "tag", "unsigned")
                # Tools that call Git themselves still get the local settings.
                subprocess.run(["git", "-C", str(repo), "commit", "-q", "--allow-empty",
                                "-m", "local settings"], check=True, capture_output=True,
                               timeout=10)
                subprocess.run(["git", "-C", str(repo), "tag", "local-settings"],
                               check=True, capture_output=True, timeout=10)
                clone = base / "clone"
                scratch_git(["git", "clone", "-q", str(repo), str(clone)], check=True)
                for setting in ("commit.gpgsign", "tag.gpgsign"):
                    self.assertEqual(git(clone, "config", "--local", "--get", setting), "false")

    def test_inherited_command_scope_signing_cannot_override_the_scratch_repo(self):
        import os
        from unittest import mock
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            inherited = {
                "GIT_CONFIG_COUNT": "3",
                "GIT_CONFIG_KEY_0": "commit.gpgsign", "GIT_CONFIG_VALUE_0": "true",
                "GIT_CONFIG_KEY_1": "tag.gpgsign", "GIT_CONFIG_VALUE_1": "true",
                "GIT_CONFIG_KEY_2": "gpg.program", "GIT_CONFIG_VALUE_2": "/signer-must-not-run",
                "GIT_CONFIG_PARAMETERS": "'commit.gpgsign'='true' 'tag.gpgsign'='true'",
                "GIT_CONFIG_KEY_99": "fixture.orphan", "GIT_CONFIG_VALUE_99": "must-be-cleared",
            }
            with mock.patch.dict(os.environ, inherited):
                git(repo, "init", "-q")
                git(repo, "config", "user.name", "t")
                git(repo, "config", "user.email", "t@example.invalid")
                control = subprocess.run(
                    ["git", "-C", str(repo), "config", "--get", "commit.gpgsign"],
                    capture_output=True, text=True, check=True, timeout=10)
                self.assertEqual(control.stdout.strip(), "true")
                git(repo, "commit", "-q", "--allow-empty", "-m", "unsigned")
                git(repo, "tag", "unsigned")
                self.assertEqual(git(repo, "log", "-1", "--format=%G?"), "N")
                self.assertEqual(git(repo, "config", "--get", "commit.gpgsign"), "false")
                self.assertEqual(git(repo, "config", "--get", "tag.gpgsign"), "false")
                probe = scratch_git(["git", "-C", str(repo), "config", "--get",
                                     "fixture.orphan"], capture_output=True)
                self.assertEqual(probe.returncode, 1)


if __name__ == "__main__":
    unittest.main()
