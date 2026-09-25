"""Chained packs on the native developer image (P5, SCN-046).

A scale-profile store with more than one link's worth of transactions is
compacted into a chain; reads and the next number are unchanged; `status`
shows the chain; and every process-death cut of the chain publication, from
both entries (`operator CONFIG store compact` and `checkpoint pack STORE
select`), reopens to the whole history and resumes to a complete chain.

FN_P5_N (default 20000) sets the size of the scale store and FN_P5_CUT_N
(default 9000) the size of the cut campaign's store.  Articles are 2 KiB: the
profile's max-article-octets, which the in-process `probe' commits.
"""
import os
from pathlib import Path
import re
import shutil
import unittest

from tests.test_native_checkpoint import IMAGE, NativeCheckpointTests
from tools import run_store

N = int(os.environ.get("FN_P5_N", "20000"))
CUT_N = int(os.environ.get("FN_P5_CUT_N", "9000"))
PROFILE_FLAGS = ("--profile", "scale", "--max-transactions", "1048576",
                 "--max-article-octets", "2048")
CUTS = ("candidate-file", "candidate-link", "candidate-directory",
        "selection-file", "selection-replace", "selection-directory",
        "pack-chain-link")


def links_for(n):
    return -(-n // 4096)


@unittest.skipUnless(IMAGE.exists(), "build/fn-host-developer is required")
class NativePackChainTests(NativeCheckpointTests):

    def scale_store(self, name, n):
        store = self.base / name
        config, port = self.owner_config(store, name)
        init = self.native("operator", config, "init", *PROFILE_FLAGS, "fn.letters")
        self.assertIn("accepted operator init", init.stderr)
        self.native("store", store, "probe", str(n))
        return store, config, port

    def chain(self, store):
        status = self.native("store", store, "status").stdout
        match = re.search(r"pack-chain (none|links=(\d+) boundary=(\d+))", status)
        self.assertIsNotNone(match, status)
        return (0, 0) if match.group(1) == "none" else (int(match.group(2)),
                                                        int(match.group(3)))

    def recovered(self, store, n):
        out = self.native("store", store, "recover").stdout
        self.assertIn("transactions={} articles={}".format(n, n), out)

    def test_scale_store_compacts_into_a_chain(self):
        store, config, port = self.scale_store("scale-chain", N)
        sample = ["<capacity-{}@example.invalid>".format(k)
                  for k in (0, 1, 4095, 4096, 4097, N // 2, N - 2, N - 1)]
        before = self.served_view(config, port, sample)
        before_retention = self.native("store", store, "retention").stdout
        compacted = self.native("operator", config, "store", "compact")
        self.assertIn("compacted steps=pack,select,reclaim,retire records={} "
                      "generation={} links={} reclaimed={} retired=0".format(
                          N, links_for(N) - 1, links_for(N), N),
                      compacted.stdout)
        self.assertEqual(self.chain(store), (links_for(N), N))
        self.assertEqual(self.transaction_bytes(store), {})
        self.recovered(store, N)
        self.assert_view_kept_and_next_number(store, config, port, sample,
                                              before, before_retention,
                                              "scale-chain")
        # The post is the uncovered suffix: the next compaction packs only it.
        again = self.native("operator", config, "store", "compact")
        self.assertIn("links=1 reclaimed=1 retired=0", again.stdout)
        self.assertEqual(self.chain(store), (links_for(N) + 1, N + 1))

    def test_every_chain_publication_cut_from_both_entries(self):
        base, config0, _ = self.scale_store("cut-base", CUT_N)
        whole = links_for(CUT_N)
        entries = {
            "compact": lambda store, config: ("operator", config, "store", "compact"),
            "pack": lambda store, config: ("checkpoint", "pack", store, "select"),
        }
        for entry, argv in entries.items():
            for point in CUTS:
                for occurrence in (1, 2):
                    with self.subTest(entry=entry, point=point, occurrence=occurrence):
                        name = "cut-{}-{}-{}".format(entry, point, occurrence)
                        store = self.base / name
                        shutil.copytree(base, store, symlinks=True)
                        config, _ = self.owner_config(store, name)
                        self.stopped_then_killed(argv(store, config), point, occurrence)
                        # The old chain or the old chain plus one complete link.
                        links, boundary = self.chain(store)
                        self.assertIn(links, (occurrence - 1, occurrence), point)
                        self.assertEqual(boundary, min(links * 4096, CUT_N))
                        self.recovered(store, CUT_N)
                        # Resume: the same entry completes the chain.
                        self.native(*argv(store, config))
                        self.assertEqual(self.chain(store), (whole, CUT_N))
                        self.recovered(store, CUT_N)
                        shutil.rmtree(store)


if __name__ == "__main__":
    unittest.main()
