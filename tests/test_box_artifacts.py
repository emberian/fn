"""The box step's artifacts and the teeth manifest are read from build/, and a
committed copy that reappears is refused by name (coordinator ruling
2026-10-09 19:50 on the registers DECISION): tools/box_artifacts.py for
specs/wire-grammar.json, tools/keystone_emit.py
for planning/teeth-obligations.json."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import box_artifacts  # noqa: E402
import keystone_emit  # noqa: E402


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
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


class TeethManifest(unittest.TestCase):
    def test_manifest_lives_under_build(self):
        self.assertEqual(keystone_emit.MANIFEST, ROOT / "build" / "teeth-obligations.json")
        self.assertEqual(keystone_emit.COMMITTED, ROOT / "planning" / "teeth-obligations.json")

    def test_committed_manifest_is_a_finding(self):
        base = {"entries": []}
        self.assertEqual(keystone_emit.manifest_findings({}, base, "", None), [])
        found = keystone_emit.manifest_findings({}, base, "", {"entries": []})
        self.assertEqual(len(found), 1)
        self.assertIn("planning/teeth-obligations.json is committed again", found[0])

    def test_base_record_may_carry_its_entries(self):
        entries = [{"name": "fn-k", "class": "generated"}]
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / "teeth-base.json"
            base.write_text(json.dumps({"revision": "0" * 40, "entries": entries}))
            saved = keystone_emit.BASE
            keystone_emit.BASE = base
            try:
                manifest, revision = keystone_emit.base_manifest()
            finally:
                keystone_emit.BASE = saved
        self.assertEqual((manifest, revision), ({"entries": entries}, "0" * 40))


if __name__ == "__main__":
    unittest.main()
