"""Chained packs on the native developer image (P5, SCN-046).

A scale-profile store with more than one link's worth of transactions is
compacted into a chain; reads and the next number are unchanged; `status`
shows the chain; and every process-death cut of the chain publication, from
both entries (`operator CONFIG store compact` and `checkpoint pack STORE
select`), reopens to the whole history and resumes to a complete chain.

FN_P5_N (default 20000) sets the size of the scale store and FN_P5_CUT_N
(default 4500: two links, so both occurrences of every cut are reached) the
size of the cut and EIO campaigns' store.  FN_P5_TIMEOUT (default 1800 s)
bounds each native call; a 20,000-record open costs minutes
(planning/evidence/bounds-p5-2026-09-25.md).  Articles are 2 KiB: the
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
CUT_N = int(os.environ.get("FN_P5_CUT_N", "4500"))
PROFILE_FLAGS = ("--profile", "scale", "--max-transactions", "1048576",
                 "--max-article-octets", "2048")
CUTS = ("candidate-file", "candidate-link", "candidate-directory",
        "selection-file", "selection-replace", "selection-directory",
        "pack-chain-link")
# EIO before each syscall of one link's publication: the candidate's
# immutable publication (host/native/immutable-publish.lisp) and the
# selection marker's replacement (host/native/checkpoint.lisp).  A failure
# before the name is visible refuses; a failed directory barrier after it is
# uncertain.
EIO_CUTS = (
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "stage", run_store.EXIT_REFUSED),
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "file-barrier", run_store.EXIT_REFUSED),
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "link", run_store.EXIT_REFUSED),
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "namespace", run_store.EXIT_UNCERTAIN),
    ("FN_CHECKPOINT_TEST_FAIL", "selection-file", run_store.EXIT_REFUSED),
    ("FN_CHECKPOINT_TEST_FAIL", "selection-replace", run_store.EXIT_REFUSED),
    ("FN_CHECKPOINT_TEST_FAIL", "selection-directory", run_store.EXIT_UNCERTAIN),
)


def links_for(n):
    return -(-n // 4096)


@unittest.skipUnless(IMAGE.exists(), "build/fn-host-developer is required")
class NativePackChainTests(unittest.TestCase):
    image = IMAGE
    # A scale store's probe and its compaction take minutes, not seconds.
    native_timeout = int(os.environ.get("FN_P5_TIMEOUT", "1800"))
    # A stop hook is reached after the open and the capture of the store.
    stop_deadline = native_timeout
    setUp = NativeCheckpointTests.setUp
    tearDown = NativeCheckpointTests.tearDown
    native = NativeCheckpointTests.native
    owner_config = NativeCheckpointTests.owner_config
    run_owner = NativeCheckpointTests.run_owner
    stop_owner = NativeCheckpointTests.stop_owner
    operator_post = NativeCheckpointTests.operator_post
    served_view = NativeCheckpointTests.served_view
    transaction_bytes = NativeCheckpointTests.transaction_bytes
    stopped_then_killed = NativeCheckpointTests.stopped_then_killed
    assert_view_kept_and_next_number = NativeCheckpointTests.assert_view_kept_and_next_number

    def scale_store(self, name, n):
        store = self.base / name
        config, port = self.owner_config(store, name)
        init = self.native("operator", config, "init", *PROFILE_FLAGS, "fn.letters", "fn.test")
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


    def test_eio_at_each_link_publication_cut_from_both_entries(self):
        base, config0, _ = self.scale_store("eio-base", CUT_N)
        self.native("operator", config0, "store", "compact")
        whole = links_for(CUT_N)
        self.assertEqual(self.chain(base), (whole, CUT_N))
        # One more record: the next compaction publishes one link on the head.
        self.native("store", base, "post", "<eio-next@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        entries = {
            "compact": lambda store, config: ("operator", config, "store", "compact"),
            "pack": lambda store, config: ("checkpoint", "pack", store, "select"),
        }
        for entry, argv in entries.items():
            for variable, point, expected in EIO_CUTS:
                with self.subTest(entry=entry, point=point):
                    name = "eio-{}-{}".format(entry, point)
                    store = self.base / name
                    shutil.copytree(base, store, symlinks=True)
                    config, _ = self.owner_config(store, name)
                    env = dict(self.env)
                    env[variable] = point
                    self.native(*argv(store, config), expected=expected, env=env)
                    # The old chain, or the old chain and the one new link.
                    links, boundary = self.chain(store)
                    self.assertIn(links, (whole, whole + 1), point)
                    self.assertEqual(boundary, CUT_N if links == whole else CUT_N + 1)
                    self.recovered(store, CUT_N + 1)
                    self.native(*argv(store, config))
                    self.assertEqual(self.chain(store), (whole + 1, CUT_N + 1))
                    self.recovered(store, CUT_N + 1)
                    shutil.rmtree(store)


if __name__ == "__main__":
    unittest.main()
