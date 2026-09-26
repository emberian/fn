"""Chained packs on the native developer image (P5, SCN-046).

A scale-profile store with more than one link's worth of transactions is
compacted into a chain; reads and the next number are unchanged; `status`
shows the chain; and every process-death cut of the chain publication, from
both entries (`operator CONFIG store compact` and `checkpoint pack STORE
select`), reopens to the whole history and resumes to a complete chain.

FN_P5_N (default 20000) sets the size of the scale store and FN_P5_CUT_N
(default 4500: three links of 4 MiB, so both occurrences of every cut are
reached) the size of the cut and EIO campaigns' store.  FN_P5_TIMEOUT (default 1800 s)
bounds each native call; a 20,000-record open costs minutes
(planning/evidence/bounds-p5-2026-09-25.md).  Articles are 2 KiB: the
profile's max-article-octets, which the in-process `probe N article' commits
as well-formed articles the served reader frames.
"""
import base64
import json
import os
from pathlib import Path
import re
import shutil
import unittest

from tests.test_native_checkpoint import IMAGE, NativeCheckpointTests
from tools import run_store

N = int(os.environ.get("FN_P5_N", "20000"))
CUT_N = int(os.environ.get("FN_P5_CUT_N", "4500"))
# A chain fixture built once (planning/evidence/pack-chain-open-2026-09-26/
# chain_fixture.py build): the scale test copies it instead of probing.
FIXTURE = os.environ.get("FN_P5_FIXTURE")
PROFILE_FLAGS = ("--profile", "scale", "--max-transactions", "1048576",
                 "--max-article-octets", "2048")
CUTS = ("candidate-file", "candidate-link", "candidate-directory",
        "selection-file", "selection-replace", "selection-directory",
        "pack-chain-link")
# EIO before each syscall of one link's publication: the candidate's
# immutable publication (host/native/immutable-publish.lisp) and the
# selection marker's replacement (host/native/checkpoint.lisp).  A failure
# of a syscall that cannot have published the name refuses; a failed link or
# rename leaves the name's visibility unknown, and a failed directory barrier
# leaves its durability unknown: both are uncertain.
EIO_CUTS = (
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "stage", run_store.EXIT_REFUSED),
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "file-barrier", run_store.EXIT_REFUSED),
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "link", run_store.EXIT_UNCERTAIN),
    ("FN_IMMUTABLE_PUBLISH_TEST_FAIL", "namespace", run_store.EXIT_UNCERTAIN),
    ("FN_CHECKPOINT_TEST_FAIL", "selection-file", run_store.EXIT_REFUSED),
    ("FN_CHECKPOINT_TEST_FAIL", "selection-replace", run_store.EXIT_UNCERTAIN),
    ("FN_CHECKPOINT_TEST_FAIL", "selection-directory", run_store.EXIT_UNCERTAIN),
)


def decode_view(recorded):
    """The served view chain_fixture.py wrote: numbers as keys, octets base64."""
    def dec(value):
        return base64.b64decode(value) if isinstance(value, str) \
            else tuple(dec(v) for v in value)
    return {(int(key) if key.isdigit() else key): dec(value)
            for key, value in recorded.items()}


def fewest_links(n):
    """A link holds at most 4096 events (and at most 4 MiB), so a whole chain
    over N records has at least this many links.  The partition itself is
    ACL2's (fn-ccc-fit); the tests read it from `status', never compute it:
    2 KiB articles fill the 4 MiB first, near 1,775 records a link."""
    return -(-n // 4096)


@unittest.skipUnless(IMAGE.exists(), "build/fn-host-developer is required")
class NativePackChainTests(unittest.TestCase):
    image = IMAGE
    # A scale store's probe and its compaction take minutes, not seconds.
    native_timeout = int(os.environ.get("FN_P5_TIMEOUT", "1800"))
    # A stop hook is reached after the open and the capture of the store.
    stop_deadline = native_timeout
    # The owner's greeting waits for its open (LISTENING after 196.0 s over
    # the 12-link, 20,000-record chain fixture on hbox, 154.4 s before
    # compaction on tmpfs: planning/evidence/pack-chain-open-2026-09-26.md),
    # and its stop for the close.
    served_timeout = native_timeout
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
        self.native("store", store, "probe", str(n), "article")
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
        match = re.search(r"compacted steps=pack,select,reclaim,retire records=(\d+) "
                          r"generation=(\d+) links=(\d+) reclaimed=(\d+) retired=0",
                          compacted)
        self.assertIsNotNone(match, compacted)
        links = int(match.group(3))
        self.assertEqual((int(match.group(1)), int(match.group(2)), int(match.group(4))),
                         (n, links - 1, n))
        self.assertGreaterEqual(links, max(2, fewest_links(n)))
        self.assertEqual(self.chain(store), (links, n))
        self.assertEqual(self.transaction_bytes(store), {})
        self.recovered(store, n)
        self.assert_view_kept_and_next_number(store, config, port, sample,
                                              before, before_retention,
                                              "scale-chain")
        # The post is the uncovered suffix: the next compaction packs only it.
        again = self.native("operator", config, "store", "compact")
        self.assertIn("links=1 reclaimed=1 retired=0", again.stdout)
        self.assertEqual(self.chain(store), (links + 1, n + 1))

    def scale_fixture(self, name):
        fixture = Path(FIXTURE)
        origin = json.loads((fixture / "origin.json").read_text(encoding="ascii"))
        recorded = json.loads((fixture / "before-view.json").read_text(encoding="ascii"))
        store = self.base / name
        shutil.copytree(fixture / "store", store, symlinks=True)
        config, port = self.owner_config(store, name)
        return (origin["n"], store, config, port, recorded["sample"],
                decode_view(recorded["view"]),
                (fixture / "retention.txt").read_text(encoding="utf-8"),
                (fixture / "compact.txt").read_text(encoding="utf-8"))

    def test_every_chain_publication_cut_from_both_entries(self):
        base, config0, _ = self.scale_store("cut-base", CUT_N)
        # The uncut compaction of a copy gives the whole chain's length.
        reference = self.base / "cut-reference"
        shutil.copytree(base, reference, symlinks=True)
        self.native("checkpoint", "pack", reference, "select")
        whole, boundary = self.chain(reference)
        self.assertEqual(boundary, CUT_N)
        self.assertGreaterEqual(whole, max(2, fewest_links(CUT_N)))
        shutil.rmtree(reference)
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
                        if links == 0:
                            self.assertEqual(boundary, 0)
                        elif links == whole:
                            self.assertEqual(boundary, CUT_N)
                        else:
                            self.assertTrue(0 < boundary < CUT_N, boundary)
                        self.recovered(store, CUT_N)
                        # Resume: the same entry completes the chain.
                        self.native(*argv(store, config))
                        self.assertEqual(self.chain(store), (whole, CUT_N))
                        self.recovered(store, CUT_N)
                        shutil.rmtree(store)


    def test_eio_at_each_link_publication_cut_from_both_entries(self):
        base, config0, _ = self.scale_store("eio-base", CUT_N)
        self.native("operator", config0, "store", "compact")
        whole, boundary = self.chain(base)
        self.assertEqual(boundary, CUT_N)
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


    def test_chain_reclaim_retire_and_suffix_cuts_resume(self):
        """Interrupted covered-file reclaim across a multi-link chain,
        interrupted retirement of generations outside the chain, and the
        uncovered suffix's recovery around both: every cut reopens to the whole
        history, and the reclaim and retire entries finish the work."""
        base, _, _ = self.scale_store("life-base", CUT_N)
        reference = self.base / "life-reference"
        shutil.copytree(base, reference, symlinks=True)
        self.native("checkpoint", "pack", reference, "select")
        whole, _ = self.chain(reference)
        self.assertGreaterEqual(whole, 2)
        shutil.rmtree(reference)
        compact = lambda config: ("operator", config, "store", "compact")
        # 1. Reclaim of the covered prefix of the whole chain, cut after the
        #    first, second and a late covered unlink (the last one the
        #    developer stop selector can name: it takes occurrences up to 4096,
        #    host/native/checkpoint.lisp fnn-checkpoint-test-stop-after) and at
        #    the directory barrier, where no covered file is left.
        late = min(CUT_N, 4096)
        for point, occurrence, left in (("pack-reclaim-unlink", 1, CUT_N - 1),
                                        ("pack-reclaim-unlink", 2, CUT_N - 2),
                                        ("pack-reclaim-unlink", late, CUT_N - late),
                                        ("pack-reclaim-directory", 1, 0)):
            with self.subTest(point=point, occurrence=occurrence):
                name = "life-reclaim-{}-{}".format(point, occurrence)
                store = self.base / name
                shutil.copytree(base, store, symlinks=True)
                config, _ = self.owner_config(store, name)
                self.stopped_then_killed(compact(config), point, occurrence)
                self.assertEqual(self.chain(store), (whole, CUT_N))
                self.assertEqual(len(self.transaction_bytes(store)), left)
                self.recovered(store, CUT_N)
                resumed = self.native("checkpoint", "pack-reclaim", store)
                self.assertIn("reclaimed transaction-prefix={}".format(left),
                              resumed.stdout)
                self.assertEqual(self.transaction_bytes(store), {})
                self.recovered(store, CUT_N)
                # Nothing is left: the verb refuses before any durable change.
                refused = self.native(*compact(config), expected=run_store.EXIT_REFUSED)
                self.assertIn("already-compact", refused.stderr)
                self.assertEqual(self.chain(store), (whole, CUT_N))
                shutil.rmtree(store)
        # 2. The compacted chain and an uncovered suffix of one record.
        config0, _ = self.owner_config(base, "life-base")
        self.native(*compact(config0))
        self.assertEqual(self.chain(base), (whole, CUT_N))
        self.native("store", base, "post", "<life-suffix@example.invalid>",
                    self.payload, "-", "-", "fn.letters")
        self.recovered(base, CUT_N + 1)
        # Two interrupted link publications leave two complete candidates that
        # were never selected: generations outside the chain.
        for attempt in (1, 2):
            self.stopped_then_killed(compact(config0), "selection-file", 1)
            self.assertEqual(self.chain(base), (whole, CUT_N))
            self.recovered(base, CUT_N + 1)
        # 3. Each retirement cut of the next compaction, which packs the
        #    suffix into a new link and retires the two orphans.
        for point, occurrence, left in (("pack-retire-unlink", 1, 1),
                                        ("pack-retire-unlink", 2, 0),
                                        ("pack-retire-directory", 1, 0)):
            with self.subTest(point=point, occurrence=occurrence):
                name = "life-retire-{}-{}".format(point, occurrence)
                store = self.base / name
                shutil.copytree(base, store, symlinks=True)
                config, _ = self.owner_config(store, name)
                self.stopped_then_killed(compact(config), point, occurrence)
                self.assertEqual(self.chain(store), (whole + 1, CUT_N + 1))
                self.assertEqual(self.transaction_bytes(store), {})
                self.recovered(store, CUT_N + 1)
                retired = self.native("checkpoint", "pack-retire", store)
                self.assertIn("retired pack-generations={}".format(left), retired.stdout)
                self.assertEqual(self.chain(store), (whole + 1, CUT_N + 1))
                self.recovered(store, CUT_N + 1)
                refused = self.native(*compact(config), expected=run_store.EXIT_REFUSED)
                self.assertIn("already-compact", refused.stderr)
                shutil.rmtree(store)


if __name__ == "__main__":
    unittest.main()
