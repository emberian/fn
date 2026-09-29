"""Compaction over the record log, on the native images (lane log-recovery;
planning/design-2026-09-27-storage-log.md sections 4 and 6; books/store-log-
segments.lisp, T8 fn-lg-segment-drop-preserves-the-open).

A store's `store compact` publishes a state checkpoint with the log
ROTATED (the active segment closed; the next created and fenced in staging/,
renamed into journal/, and journal/ fenced before the checkpoint's F row
names it) and, once the checkpoint is installed, DROPS the
segments it covers.  The cases, each over a store the served node filled:

* compaction: journal/ holds only the new segment, every article is served
  (`store inspect`) exactly as before, the node commits after it, and a
  second compaction drops the next segment; export then import of the
  compacted store gives the same archive;
* a process death at each rotation and drop cut (developer image,
  FN_NATIVE_LOG_FAULT = rotate-created | rotate-fenced | rotate-renamed | rotate-headed |
  rotate-durable | drop-unlinked | drop-durable): the next writable open
  (`store recover`) serves every article as before, sweeps a spare that was
  never renamed, finishes an interrupted drop, and a later compaction
  succeeds;
* content reclamation: `store reclaim` under released-by-all-holders
  rewrites the history (books/store-log-reclaim.lisp), checkpoints it with
  the log rotated and drops the covered segment: no file of the store holds
  a released article's body, and a rerun reclaims nothing;
* the open's refusals by name: a segment missing between the checkpoint's
  first segment and the active one (history-short-of-checkpoint), the
  checkpoint gone after a drop (checkpoint-damaged), a stale segment after
  the active one (log-chain-broken); each exit 1.
"""
from __future__ import annotations

import os
import shutil
import tempfile
import unittest
from pathlib import Path

from tests.test_native_commit_log import Node, msgid, post_concurrently

DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST", "")
PRODUCTION = os.environ.get("FN_NATIVE_HOST", "")

ROTATION_CUTS = ("rotate-created", "rotate-fenced", "rotate-renamed", "rotate-headed", "rotate-durable",
                 "drop-unlinked", "drop-durable")
# The spare's cuts: the next segment is staged, not yet named in journal/.
SPARE_CUTS = ("rotate-created", "rotate-fenced")


GENESIS = "000000.log"


def segments(store: Path):
    """The history's segments in journal/ (NNNNNN.log).  Format 10's genesis,
    journal/000000.log (books/store-genesis.lisp), is position 0 of the log
    and never rotated or dropped, so it is not listed; `genesis_kept' checks
    it.  journal/ held the owner's decision journal until batch AX moved it
    to decisions/."""
    return sorted(p.name for p in (store / "journal").iterdir()
                  if p.name.endswith(".log") and p.name != GENESIS)


def genesis_kept(store: Path) -> bool:
    return (store / "journal" / GENESIS).is_file()



def reclaim_counts(stdout: bytes) -> dict:
    """The counts ACL2 printed (host/native/checkpoint.lisp
    fnn-reclaim-counts-line): reclaimable, reclaimable-octets, held,
    reclaimed and freed-octets, from the line that carries them."""
    for line in stdout.decode("utf-8", "replace").splitlines():
        if " reclaimable=" in " " + line:
            fields = dict(word.split("=", 1) for word in line.split() if "=" in word)
            return {k: int(fields[k]) for k in
                    ("reclaimable", "reclaimable-octets", "held", "reclaimed", "freed-octets")}
    raise AssertionError("no counts line in %r" % stdout)

class LogCompactionMixin:
    image = ""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="fn-lcp-")
        self.root = Path(self.dir.name)

    def tearDown(self):
        self.dir.cleanup()

    def filled(self, first: int, count: int, node=None) -> Node:
        node = node or Node(self, self.image, root=self.root)
        if not (node.store_path / "journal").exists():
            node.init()
        node.start()
        try:
            replies, errors = post_concurrently(node.port, range(first, first + count), 4)
        finally:
            node.stop()
        self.assertEqual(errors, [])
        self.assertTrue(all(r.startswith(b"240") for r in replies.values()), replies)
        return node

    def inspect_all(self, node: Node, ids, store=None):
        out = {}
        for i in ids:
            if store is None:
                result = node.invoke("operator", str(node.config), "store", "inspect", msgid(i))
            else:
                result = node.invoke("store", str(store), "inspect", msgid(i))
            self.assertEqual(result.returncode, 0, (i, result.stderr[-600:]))
            out[i] = result.stdout
        return out

    def compact(self, node: Node, env=None):
        return node.invoke("operator", str(node.config), "store", "compact", env=env)

    def test_compaction_rotates_drops_and_serves_the_same_history(self):
        node = self.filled(0, 12)
        self.assertEqual(segments(node.store_path), ["000001.log"])
        before = self.inspect_all(node, range(12))
        done = self.compact(node)
        self.assertEqual(done.returncode, 0, done.stderr[-800:])
        self.assertIn(b"compacted steps=checkpoint,drop records=", done.stdout)
        self.assertIn(b"segment=2 dropped=1", done.stdout)
        self.assertEqual(segments(node.store_path), ["000002.log"])
        self.assertEqual(self.inspect_all(node, range(12)), before)
        # The node reopens over the checkpoint and segment 2 and commits.
        self.filled(12, 6, node)
        before = self.inspect_all(node, range(18))
        done = self.compact(node)
        self.assertEqual(done.returncode, 0, done.stderr[-800:])
        self.assertEqual(segments(node.store_path), ["000003.log"])
        self.assertEqual(self.inspect_all(node, range(18)), before)
        # Export of the compacted store (the checkpoint's records then the
        # log's), import, export again: the same archive.
        archive, again = self.root / "archive", self.root / "again"
        exported = node.invoke("store", str(node.store_path), "export", str(archive))
        self.assertEqual(exported.returncode, 0, exported.stderr[-800:])
        self.assertIn(b"exported records=", exported.stdout)
        imported_root = self.root / "imported"
        imported = node.invoke("store", str(imported_root), "import", str(archive))
        self.assertEqual(imported.returncode, 0, imported.stderr[-800:])
        self.assertEqual(segments(imported_root), ["000001.log"])
        reexported = node.invoke("store", str(imported_root), "export", str(again))
        self.assertEqual(reexported.returncode, 0, reexported.stderr[-800:])
        files = lambda d: {p.relative_to(d): p.read_bytes() for p in sorted(d.rglob("*")) if p.is_file()}
        self.assertEqual(files(again), files(archive))
        # `store ROOT inspect` on both stores (the operator's form prints
        # another report).
        self.assertEqual(self.inspect_all(node, range(18), store=imported_root),
                         self.inspect_all(node, range(18), store=node.store_path))

    def store_holds(self, node: Node, needle: bytes) -> bool:
        return any(needle in p.read_bytes() for p in node.store_path.rglob("*") if p.is_file())

    def test_reclaim_over_the_log_removes_the_released_payloads(self):
        """`store reclaim` on a store (books/store-log-reclaim.lisp):
        the rewritten history's checkpoint with the log rotated, then the drop;
        the released articles' payload octets are on no file of the store."""
        node = self.filled(0, 8)
        self.assertTrue(self.store_holds(node, b"body of 3\r\n"))
        rule = node.invoke("operator", str(node.config), "retention", "set", "released-by-all-holders")
        self.assertEqual(rule.returncode, 0, rule.stderr[-600:])
        dry = node.invoke("operator", str(node.config), "store", "reclaim", "--dry-run")
        self.assertEqual(dry.returncode, 0, dry.stderr[-600:])
        self.assertIn(b"dry-run would-reclaim=8", dry.stdout)
        # The counts read each article through the arena (lane
        # matrix-reds-reclaim): before, they parsed its handle, so every
        # octet count was 0 and a reclaimed article counted as reclaimable.
        before = reclaim_counts(dry.stdout)
        self.assertEqual(before["reclaimable"], 8, dry.stdout)
        self.assertGreater(before["reclaimable-octets"], 0, dry.stdout)
        self.assertEqual(before["reclaimed"], 0, dry.stdout)
        self.assertEqual(segments(node.store_path), ["000001.log"])
        done = node.invoke("operator", str(node.config), "store", "reclaim")
        self.assertEqual(done.returncode, 0, done.stderr[-800:])
        self.assertIn(b"reclaimed=8", done.stdout)
        self.assertEqual(segments(node.store_path), ["000002.log"])
        for i in range(8):
            self.assertFalse(self.store_holds(node, b"body of %d\r\n" % i), i)
        again = node.invoke("operator", str(node.config), "store", "reclaim")
        self.assertEqual(again.returncode, 0, again.stderr[-800:])
        self.assertIn(b"reclaimed=0", again.stdout)
        after = reclaim_counts(again.stdout)
        self.assertEqual(after["reclaimable"], 0, again.stdout)
        self.assertEqual(after["reclaimable-octets"], 0, again.stdout)
        self.assertEqual(after["reclaimed"], 8, again.stdout)
        recovered = node.invoke("store", str(node.store_path), "recover")
        self.assertEqual(recovered.returncode, 0, recovered.stderr[-800:])

    def test_refusals_by_name(self):
        node = self.filled(0, 6)
        self.assertEqual(self.compact(node).returncode, 0)
        self.filled(6, 3, node)
        self.assertEqual(self.compact(node).returncode, 0)
        self.assertEqual(segments(node.store_path), ["000003.log"])
        self.filled(9, 2, node)
        pristine = self.root / "pristine"
        shutil.copytree(node.store_path, pristine)

        def reopened_refusal(word):
            result = node.invoke("store", str(node.store_path), "recover")
            self.assertEqual(result.returncode, 1, (word, result.stdout, result.stderr[-600:]))
            self.assertIn(("reason=" + word).encode(), result.stdout + result.stderr)
            shutil.rmtree(node.store_path)
            shutil.copytree(pristine, node.store_path)

        # A stale segment after the active one: segment 3's bytes as 000004.log
        # chain from segment 2's trailer, not segment 3's last.
        shutil.copyfile(node.store_path / "journal" / "000003.log", node.store_path / "journal" / "000004.log")
        reopened_refusal("log-chain-broken")
        # The checkpoint's first segment missing: history-short-of-checkpoint.
        (node.store_path / "journal" / "000003.log").rename(node.store_path / "journal" / "000005.log")
        reopened_refusal("history-short-of-checkpoint")
        # The checkpoint gone after the drop: checkpoint-damaged.
        (node.store_path / "store-checkpoint.fnsc").unlink()
        reopened_refusal("checkpoint-damaged")


@unittest.skipUnless(DEVELOPER, "FN_NATIVE_DEVELOPER_HOST names the developer image")
class DeveloperLogCompactionTests(LogCompactionMixin, unittest.TestCase):
    image = DEVELOPER

    def test_a_death_at_each_rotation_and_drop_cut(self):
        node = self.filled(0, 8)
        before = self.inspect_all(node, range(8))
        pristine = self.root / "pristine"
        shutil.copytree(node.store_path, pristine)
        for cut in ROTATION_CUTS:
            with self.subTest(cut=cut):
                shutil.rmtree(node.store_path)
                shutil.copytree(pristine, node.store_path)
                killed = self.compact(node, env={"FN_NATIVE_LOG_FAULT": cut})
                self.assertEqual(killed.returncode, -9, (cut, killed.stdout, killed.stderr[-600:]))
                recovered = node.invoke("store", str(node.store_path), "recover")
                self.assertEqual(recovered.returncode, 0, (cut, recovered.stderr[-800:]))
                self.assertEqual(self.inspect_all(node, range(8)), before, cut)
                present = segments(node.store_path)
                # the genesis survives every rotation and drop cut
                self.assertTrue(genesis_kept(node.store_path), cut)
                if cut.startswith("drop"):
                    # the checkpoint was installed: the recover finished the drop
                    self.assertEqual(present, ["000002.log"], cut)
                elif cut in SPARE_CUTS:
                    # the spare was staged, never named: segment 1 is still
                    # the active one, and the writable open swept the spare
                    self.assertEqual(present, ["000001.log"], cut)
                    self.assertEqual([p.name for p in (node.store_path / "staging").glob(".stage-segment-*")],
                                     [], cut)
                else:
                    # no checkpoint names segment 2 yet: the open scans 1 then 2
                    self.assertEqual(present, ["000001.log", "000002.log"], cut)
                again = self.compact(node)
                self.assertEqual(again.returncode, 0, (cut, again.stderr[-800:]))
                self.assertEqual(self.inspect_all(node, range(8)), before, cut)
                self.assertEqual(len(segments(node.store_path)), 1, cut)


@unittest.skipUnless(PRODUCTION, "FN_NATIVE_HOST names the production image")
class ProductionLogCompactionTests(LogCompactionMixin, unittest.TestCase):
    image = PRODUCTION


if __name__ == "__main__":
    unittest.main()
