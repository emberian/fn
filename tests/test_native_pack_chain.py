"""Compaction of a scale store over the record log (P5, SCN-046; format 9).

On format 9 there are no packs (design 2026-09-27 storage-log section 6,
section 9 row 5): `operator CONFIG store compact' publishes a state
checkpoint with the log ROTATED and DROPS the segments it covers
(books/store-log-segments.lisp, T8 fn-lg-segment-drop-preserves-the-open).
What P5 required of compacting a store bigger than one unit of work stays:
a store of CUT_N probe articles (default 4500) and, gated, the scale store
of N (default 20000) compact; the committed history (the `store export'
archive, file for file) and every sampled article are unchanged; the open
after it replays the same counts; the next POST takes the next number; a
second compaction covers the new suffix.  The kill cuts of the rotation and
the drop are tests.test_native_log_compaction's.

Retired with the pack chain (design section 9 row 5; books and host code go
in lane log-recovery's pack deletion):
* test_every_chain_publication_cut_from_both_entries -- the pack chain's
  candidate/selection/pack-chain-link cuts (the log's are rotate-* and drop-*,
  tests.test_native_log_compaction);
* test_pack_chain_link_cut_leaves_exactly_the_selected_links -- chain links;
* test_eio_at_each_link_publication_cut_from_both_entries -- a link's
  immutable publication and the selection marker (no such files on format 9);
* test_chain_reclaim_retire_and_suffix_cuts_resume -- pack-reclaim and
  pack-retire (`checkpoint pack*' refuses reason=record-log on format 9).

FN_P5_TIMEOUT (default 1800 s) bounds each native call.  Articles are 2 KiB:
the profile's max-article-octets, which the in-process `probe N article'
commits as well-formed articles the served reader frames.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import unittest

# The module, not its TestCase: a TestCase imported by name is collected and
# run again as this module's own (the checkpoint suite ran twice here).
from tests import test_native_checkpoint as checkpoint

IMAGE = checkpoint.IMAGE

N = int(os.environ.get("FN_P5_N", "20000"))
CUT_N = int(os.environ.get("FN_P5_CUT_N", "4500"))
# A scale store built once (planning/evidence/pack-chain-open-2026-09-26/
# chain_fixture.py build, tools/fixtures.py chain-20000): the scale test
# copies it instead of probing.
FIXTURE = os.environ.get("FN_P5_FIXTURE")
PROFILE_FLAGS = ("--profile", "scale", "--max-transactions", "1048576",
                 "--max-article-octets", "2048")


def decode_view(recorded):
    """The served view chain_fixture.py wrote: numbers as keys, octets base64."""
    def dec(value):
        return base64.b64decode(value) if isinstance(value, str) \
            else tuple(dec(v) for v in value)
    return {(int(key) if key.isdigit() else key): dec(value)
            for key, value in recorded.items()}


def segments(store):
    return sorted(p.name for p in (Path(store) / "journal").iterdir() if p.is_file())


def archive_tree(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(Path(root).rglob("*")) if p.is_file()}


@unittest.skipUnless(IMAGE.exists(), "build/fn-host-developer is required")
class NativePackChainTests(unittest.TestCase):
    image = IMAGE
    # A scale store's probe and its compaction take minutes, not seconds.
    native_timeout = int(os.environ.get("FN_P5_TIMEOUT", "1800"))
    served_timeout = native_timeout
    setUp = checkpoint.NativeCheckpointTests.setUp
    tearDown = checkpoint.NativeCheckpointTests.tearDown
    native = checkpoint.NativeCheckpointTests.native
    owner_config = checkpoint.NativeCheckpointTests.owner_config
    run_owner = checkpoint.NativeCheckpointTests.run_owner
    stop_owner = checkpoint.NativeCheckpointTests.stop_owner
    operator_post = checkpoint.NativeCheckpointTests.operator_post
    served_view = checkpoint.NativeCheckpointTests.served_view
    assert_view_kept_and_next_number = checkpoint.NativeCheckpointTests.assert_view_kept_and_next_number

    def scale_store(self, name, n):
        store = self.base / name
        config, port = self.owner_config(store, name)
        # Lane membership-budget: the T = 2^20 profile's full store reserves
        # about 37 GB, past this module's 24 GB unit; the store is made for
        # hbox (FN_INIT_BUDGET_MB names that target) and run directly.
        init = self.native("operator", config, "init", *PROFILE_FLAGS, "fn.letters", "fn.test",
                           env=dict(self.env, FN_INIT_BUDGET_MB="98304"))
        self.assertIn("accepted operator init", init.stderr)
        self.native("store", store, "probe", str(n), "article")
        return store, config, port

    def history(self, store, label):
        archive = self.base / ("archive-" + label)
        exported = self.native("store", store, "export", archive)
        self.assertIn("exported records=", exported.stdout)
        tree = archive_tree(archive)
        shutil.rmtree(archive)
        return tree

    def recovered(self, store, n):
        out = self.native("store", store, "recover").stdout
        self.assertIn("transactions={} articles={}".format(n, n), out)

    def compacted(self, out, n):
        match = re.search(r"compacted steps=checkpoint,drop records=(\d+) .*"
                          r"segment=(\d+) dropped=(\d+)", out)
        self.assertIsNotNone(match, out)
        self.assertEqual(int(match.group(1)), n, out)
        return int(match.group(2)), int(match.group(3))

    def inspect(self, store, msgids):
        return {m: self.native("store", store, "inspect", m).stdout for m in msgids}

    def test_a_multi_unit_store_compacts_over_the_log(self):
        store, config, _ = self.scale_store("cut-base", CUT_N)
        sample = ["<capacity-{}@example.invalid>".format(k)
                  for k in (0, 1, 1774, 1775, 4095, CUT_N // 2, CUT_N - 1)]
        before = self.history(store, "before")
        seen = self.inspect(store, sample)
        self.assertEqual(segments(store), ["000001.log"])
        segment, dropped = self.compacted(
            self.native("operator", config, "store", "compact").stdout, CUT_N)
        self.assertEqual((segment, dropped), (2, 1))
        self.assertEqual(segments(store), ["000002.log"])
        self.assertEqual(self.history(store, "after"), before)
        self.assertEqual(self.inspect(store, sample), seen)
        self.recovered(store, CUT_N)
        # The suffix after the checkpoint: one more record, the next number.
        owner = self.run_owner(config)
        try:
            self.operator_post(config, "<p5-next@example.invalid>", "p5-next")
        finally:
            self.stop_owner(owner)
        self.recovered(store, CUT_N + 1)
        segment, dropped = self.compacted(
            self.native("operator", config, "store", "compact").stdout, CUT_N + 1)
        self.assertEqual((segment, dropped), (3, 1))
        self.assertEqual(segments(store), ["000003.log"])
        self.assertEqual(self.inspect(store, sample), seen)
        self.recovered(store, CUT_N + 1)

    @unittest.skipUnless(os.environ.get("FN_P5_SCALE") == "1" or FIXTURE,
                         "N=20,000: building the scale store takes about 20 minutes on "
                         "tmpfs; set FN_P5_FIXTURE to a fixture from "
                         "planning/evidence/pack-chain-open-2026-09-26/chain_fixture.py "
                         "(built once), or FN_P5_SCALE=1 to build it here")
    def test_scale_store_compacts_into_a_chain(self):
        if FIXTURE:
            # The same store, view and compaction, built once
            # (chain_fixture.py build): copy it; the fixture is never opened.
            n, store, config, port, sample, before, before_retention, compacted = \
                self.scale_fixture("scale-chain")
        else:
            n = N
            store, config, port = self.scale_store("scale-chain", n)
            sample = ["<capacity-{}@example.invalid>".format(k)
                      for k in (0, 1, 4095, 4096, 4097, n // 2, n - 2, n - 1)]
            before = self.served_view(config, port, sample)
            before_retention = self.native("store", store, "retention").stdout
            compacted = self.native("operator", config, "store", "compact").stdout
        segment, dropped = self.compacted(compacted, n)
        self.assertEqual((segment, dropped), (2, 1))
        self.assertEqual(segments(store), ["000002.log"])
        self.recovered(store, n)
        self.assert_view_kept_and_next_number(store, config, port, sample,
                                              before, before_retention,
                                              "scale-chain")
        # The post is the uncovered suffix: the next compaction covers it.
        again = self.native("operator", config, "store", "compact").stdout
        self.assertEqual(self.compacted(again, n + 1), (3, 1))
        self.assertEqual(segments(store), ["000003.log"])

    def scale_fixture(self, name):
        fixture = Path(FIXTURE)
        origin = json.loads((fixture / "origin.json").read_text(encoding="ascii"))
        recorded = json.loads((fixture / "before-view.json").read_text(encoding="ascii"))
        store = self.base / name
        shutil.copytree(fixture / "store", store, symlinks=True)
        # The copy is a store placed here deliberately, on another filesystem
        # than the one tools/fixtures.py built it on: it is rebound before
        # use (PKT-579).
        self.native("store", store, "rebind-filesystem")
        if not (store / "keys" / "node-secret.key").exists():
            self.native("store", store, "node-secret", "create")
        config, port = self.owner_config(store, name)
        return (origin["n"], store, config, port, recorded["sample"],
                decode_view(recorded["view"]),
                (fixture / "retention.txt").read_text(encoding="utf-8"),
                (fixture / "compact.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
