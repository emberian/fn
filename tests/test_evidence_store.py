"""The evidence index and the fetch-by-hash archive (tools/evidence_store.py).

What these hold: a committed index line names bytes the archive has and a
reader gets exactly those bytes back by hash; the working tree shadows the
index the way a git working tree shadows HEAD; an object that is missing or
does not hash to its name is UNAVAILABLE (uncertain), never "absent"; and a
union merge that kept two versions of one path is refused, not resolved.
"""

from __future__ import annotations

import gzip
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import evidence_store as store  # noqa: E402

REL = "planning/evidence/manifests/certify-20261002T000000Z-1.json"


class Sandbox(unittest.TestCase):
    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        base = Path(self._dir.name)
        self.root = base / "tree"
        self.archive = base / "archive"
        self.cache = base / "cache"
        (self.root / "planning/evidence/manifests").mkdir(parents=True)
        self._env = mock.patch.dict(os.environ, {
            "FN_EVIDENCE_ARCHIVE": str(self.archive),
            "FN_EVIDENCE_CACHE": str(self.cache)})
        self._env.start()
        store._INDEX.clear()

    def tearDown(self):
        self._env.stop()
        self._dir.cleanup()

    def write(self, rel: str, data: bytes) -> None:
        (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
        (self.root / rel).write_bytes(data)


class IndexTests(Sandbox):
    def test_render_and_parse_round_trip_sorted_with_a_header(self):
        entries = {"planning/evidence/b.md": ("b" * 64, 2),
                   "planning/evidence/a b.md": ("a" * 64, 1)}
        text = store.render_index(entries)
        self.assertTrue(text.startswith("# fn evidence index"))
        body = [line for line in text.splitlines() if not line.startswith("#")]
        self.assertEqual(body, [f"{'a' * 64} 1 planning/evidence/a b.md",
                                f"{'b' * 64} 2 planning/evidence/b.md"])
        self.assertEqual(store.parse_index(text), entries)

    def test_a_union_merge_that_kept_two_versions_is_refused(self):
        text = f"{'a' * 64} 1 planning/evidence/x.md\n{'b' * 64} 1 planning/evidence/x.md\n"
        with self.assertRaisesRegex(ValueError, "indexed twice"):
            store.parse_index(text)
        # The same line twice (both sides added the same run) is one entry.
        same = f"{'a' * 64} 1 planning/evidence/x.md\n" * 2
        self.assertEqual(len(store.parse_index(same)), 1)

    def test_a_malformed_line_is_refused(self):
        with self.assertRaisesRegex(ValueError, "malformed"):
            store.parse_index("not-a-sha 1 planning/evidence/x.md\n")

    def test_the_gitattributes_merge_the_index_by_union(self):
        attributes = (TOOLS.parent / ".gitattributes").read_text(encoding="utf-8")
        self.assertIn(f"{store.INDEX_REL} merge=union", attributes)


class PutAndReadTests(Sandbox):
    def test_put_archives_then_indexes_and_a_reader_gets_the_bytes_by_hash(self):
        data = b'{"status": "passed"}\n'
        self.write(REL, data)
        entries = store.put(self.root, [REL])
        sha = store.sha256_bytes(data)
        self.assertEqual(entries, {REL: (sha, len(data))})
        self.assertEqual(store.read_index(self.root), {REL: (sha, len(data))})
        stored = self.archive / store.object_rel(sha)
        self.assertEqual(gzip.decompress(stored.read_bytes()), data)
        (self.root / REL).unlink()
        self.assertTrue(store.exists(self.root, REL))
        self.assertTrue(store.is_dir(self.root, "planning/evidence/manifests"))
        self.assertEqual(store.read_bytes(self.root, REL), data)
        self.assertEqual(store.glob(self.root, "planning/evidence/manifests/certify-*.json"),
                         [REL])
        self.assertEqual(store.materialize(self.root, REL).read_bytes(), data)

    def test_the_working_tree_shadows_the_index(self):
        self.write(REL, b"old\n")
        store.put(self.root, [REL])
        self.write(REL, b"new, not yet put\n")
        self.assertEqual(store.read_bytes(self.root, REL), b"new, not yet put\n")

    def test_a_path_named_by_neither_is_absent(self):
        self.assertFalse(store.exists(self.root, "planning/evidence/none.md"))
        with self.assertRaises(FileNotFoundError):
            store.read_bytes(self.root, "planning/evidence/none.md")

    def test_a_corrupt_object_is_unavailable_not_absent(self):
        self.write(REL, b"bytes\n")
        sha, _ = store.put(self.root, [REL])[REL]
        (self.root / REL).unlink()
        (self.archive / store.object_rel(sha)).write_bytes(gzip.compress(b"other\n"))
        with self.assertRaisesRegex(store.EvidenceUnavailable, "does not hash"):
            store.read_bytes(self.root, REL)

    def test_an_indexed_object_the_archive_lacks_is_unavailable(self):
        self.write(REL, b"bytes\n")
        sha, _ = store.put(self.root, [REL])[REL]
        (self.root / REL).unlink()
        shutil.rmtree(self.archive)
        with self.assertRaises(store.EvidenceUnavailable):
            store.read_bytes(self.root, REL)


class RemoteFetchTests(Sandbox):
    """`HOST:/path` archives go through one rsync; the result is verified."""

    def fake_rsync(self, remote_dir: Path, corrupt: bool = False):
        calls = []

        def run(command, *args, **kwargs):
            calls.append(command)
            if command[0] != "rsync":
                return subprocess.CompletedProcess(command, 1, "", "")
            listing = Path(command[command.index("--files-from") + 1]).read_text()
            source, target = command[-2], command[-1]
            source_dir = remote_dir if ":" in source else Path(source)
            target_dir = remote_dir if ":" in target else Path(target)
            for rel in listing.split():
                src = source_dir / rel
                if src.is_file():
                    (target_dir / rel).parent.mkdir(parents=True, exist_ok=True)
                    data = src.read_bytes()
                    if corrupt:
                        data = gzip.compress(b"tampered")
                    (target_dir / rel).write_bytes(data)
            return subprocess.CompletedProcess(command, 0, "", "")
        return run, calls

    def test_put_pushes_and_a_fresh_cache_fetches_by_hash(self):
        remote = Path(self._dir.name) / "remote"
        remote.mkdir()
        os.environ["FN_EVIDENCE_ARCHIVE"] = f"box:{remote}"
        run, calls = self.fake_rsync(remote)
        data = b"evidence\n"
        self.write(REL, data)
        with mock.patch.object(store.subprocess, "run", side_effect=run):
            sha, _ = store.put(self.root, [REL])[REL]
            self.assertTrue((remote / store.object_rel(sha)).is_file())
            (self.root / REL).unlink()
            shutil.rmtree(self.cache)
            self.assertEqual(store.read_bytes(self.root, REL), data)
        rsyncs = [command for command in calls if command[0] == "rsync"]
        self.assertEqual(len(rsyncs), 2)
        self.assertTrue(rsyncs[1][-2].startswith("box:"))

    def test_a_tampered_transfer_is_refused_and_not_cached(self):
        remote = Path(self._dir.name) / "remote"
        remote.mkdir()
        data = b"evidence\n"
        sha = store.store_object(remote, data)
        store.write_index(self.root, {REL: (sha, len(data))})
        os.environ["FN_EVIDENCE_ARCHIVE"] = f"box:{remote}"
        run, _ = self.fake_rsync(remote, corrupt=True)
        with mock.patch.object(store.subprocess, "run", side_effect=run):
            with self.assertRaisesRegex(store.EvidenceUnavailable, "did not arrive verified"):
                store.read_bytes(self.root, REL)
        self.assertFalse((self.cache / store.object_rel(sha)).exists())


class TransitionTests(Sandbox):
    def test_tree_entries_hash_the_tracked_evidence(self):
        root = self.root
        for command in (["init", "-q"], ["config", "user.email", "t@example"],
                        ["config", "user.name", "t"], ["config", "commit.gpgsign", "false"]):
            subprocess.run(["git", "-C", str(root), *command], check=True)
        self.write("planning/evidence/a.md", b"a\n")
        self.write("planning/evidence/d/b.json", b"{}\n")
        subprocess.run(["git", "-C", str(root), "add", "."], check=True)
        subprocess.run(["git", "-C", str(root), "commit", "-q", "-m", "m"], check=True)
        self.assertEqual(store.tree_entries(root), {
            "planning/evidence/a.md": (store.sha256_bytes(b"a\n"), 2),
            "planning/evidence/d/b.json": (store.sha256_bytes(b"{}\n"), 3)})


if __name__ == "__main__":
    unittest.main()
