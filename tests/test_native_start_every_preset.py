"""Every node type starts at every preset through the image's own launcher.

A bare launch of an image -- no SBCL_USER_ARGS, no FN_TEST_HEAP_MB, no
installed layout -- decides its heap per command, as packaging/fn's installed
branch does (tools/build_native_host.sh splices packaging/fn's fn_decide_heap
into the launcher): the image's `heap -- ARGV` probe, ACL2's fn-mo-serve-decide
for a served run (fn-heap-command-decide for other commands).
The launcher used to run every command at the small preset's figure (1767 MB
at 207ed2afd), so a default-profile store was refused at cold start
(:default-pool-read-headroom-unavailable, books/page-read-startup.lisp
fn-prstartup-plan) and a BP node more so, and nothing started bare noticed
(train 27, CONVERGE row 35b: tests.test_bp_node_native, tests.test_native_owner).

For each preset (small, development, scale) and each node type -- the
operator's served run, the developer store owner (`owner run`) and a BP node
(`bp-node serve`), on the developer image and on the DTN developer image where
it has the verb (the DTN image omits the NNTP service, so its served run is not an NNTP start) -- the node must reach its LISTENING announcement.  Init may
refuse a requested preset's target budget; once written, the run launches at
resident LIMIT with its pools and serves at the gate's C'.  Its probe refuses
unobserved memory, pools or observed store reopen that cannot fit, or address
space that cannot hold the reservation.  The teeth: the same node at
85% of its decided heap, named explicitly, is refused at cold start by ACL2 and
never announces.
"""

import re
import unittest

from tests.native_harness import (EXIT, Node, environment, free_port, executable, native_image,
                                  requires, run, start)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
DTN = native_image("FN_NATIVE_DTN_DEVELOPER_HOST")
# The presets as `operator CONFIG init` takes them: the small preset is the
# development profile under its named fields (tests/test_native_heap_from_profile.py
# SMALL_FLAGS; tools/build_native_host.sh probes the same).
PRESETS = {
    "small": ("--profile", "development", "--max-transactions", "16384",
              "--max-history-octets", "8388608", "--max-record-octets", "196608",
              "--max-groups-per-article", "16", "--max-open-suffix", "128"),
    "development": ("--profile", "development"),
    "scale": ("--profile", "scale"),
}
GROUP = "fn.test"


def probe(image, words):
    """(heap MB or None, text): the image's own `heap -- WORDS` answer."""
    done = run([str(image), "--fn", "heap", "--", *[str(w) for w in words]],
               env=environment(), timeout=120)
    text = done.stdout.decode("utf-8", "replace")
    figure = re.match(r"heap=(\d+) MB", text)
    return (int(figure.group(1)) if figure else None), text


# Every case starts the developer image (the bp-node case adds the DTN image
# where it is built), so the class skips, naming it, when that image is absent.
@requires(DEVELOPER)
class StartEveryPresetTests(unittest.TestCase):
    def node(self, image, preset):
        # No heap opt-out is named: image_heap makes Node start the bare image.
        node = Node(self, image, name="{}-{}".format(image.name, preset),
                    image_heap="the bare launcher decides its own heap (this test's subject)")
        init = node.operator("init", *PRESETS[preset], GROUP, expect=None, timeout=600)
        if init.returncode != 0:
            text = (init.stdout + init.stderr).decode("utf-8", "replace")
            # waiver-ok: capability -- init refuses :machine-cannot-hold-profile by
            # name when this machine's memory cannot hold the preset; that preset is
            # a machine this tree has not been given, not a broken start.
            if "machine-cannot-hold-profile" in text:
                self.skipTest("{}: the machine cannot hold the {} preset".format(image.name, preset))
            self.fail("init {} exited {}: {}".format(preset, init.returncode, text))
        return node

    def served_words(self, node):
        return ("operator", node.config, "run")

    def owner_words(self, node):
        return ("owner", "run", node.store_path, "0", "0", "8")

    def bp_words(self, node, port):
        journal = node.root / "bp-journal"
        return ("bp-node", "serve", str(port), journal, node.store_path, node.root / "bp-rj",
                node.root / "bp-wf", "dtn://receiver/", "dtn://sender/", "dtn://receiver/",
                "native-policy", "dtn://receiver/", "127.0.0.1", str(free_port()),
                "0", "3600000", "2", "32", "1048576", "0", "0")

    def started(self, words, announce, image, node, env=None):
        process = start([str(image), "--fn", *[str(w) for w in words]], cwd=node.root,
                        env=environment(env))
        self.addCleanup(process.stop, 5)
        process.announcement(announce, timeout=120)
        self.assertIsNone(process.poll(), "{} exited after announcing".format(words[0]))
        # The open's first history root refresh is funded: the reserve is the
        # run ledger's (N-FRESH, hroot reserve 0 at open), so an empty store
        # opens without "HISTORY root refresh not built".
        self.assertNotIn(b"HISTORY root refresh not built", process.stderr.since(0),
                         "{}: the open's history root refresh was refused".format(words[0]))
        return process

    def test_the_served_run_starts_at_every_preset(self):
        for preset in PRESETS:
            with self.subTest(preset=preset):
                node = self.node(DEVELOPER, preset)
                self.started(self.served_words(node), b"LISTENING ", DEVELOPER, node)

    def test_the_store_owner_starts_at_every_preset(self):
        for preset in PRESETS:
            with self.subTest(preset=preset):
                node = self.node(DEVELOPER, preset)
                heap, text = probe(DEVELOPER, self.owner_words(node))
                self.assertIsNotNone(heap, text)
                self.assertNotIn("profile=none", text, "the owner probe must read the store's profile")
                self.started(self.owner_words(node), b"LISTENING ", DEVELOPER, node)

    def test_the_bp_node_starts_at_every_preset(self):
        for image in [i for i in (DEVELOPER, DTN) if executable(i)]:
            for preset in PRESETS:
                with self.subTest(image=image.name, preset=preset):
                    node = self.node(image, preset)
                    self.started(self.bp_words(node, free_port()), b"BP NODE LISTENING ",
                                 image, node)

    def test_a_heap_below_the_decided_figure_is_refused_by_name(self):
        """85% of the figure each command's own probe decides, named
        explicitly (a caller's SBCL_USER_ARGS wins over the launcher's
        decision), is refused by ACL2 at cold start: the served run and the
        developer store owner (the pool or the store's protected runtime), the
        BP node (its session funding).

        Since L-RUN-LAUNCH the probe launches at the run's resident LIMIT
        (books/heap-command.lisp fn-mo-serve-decide: the core's content and
        LIMIT, plus the pools) and the owner protects the smaller of the
        profile's store and that launch (books/peer-flight-startup.lisp
        fn-prstartup-serve-protected).  Under a limit below the development
        profile's store the protected runtime is the launch's own, so the
        decided figure is tight again: every case runs under
        `systemd-run --scope -p MemoryMax=1G' (probe and start alike); under a
        generous limit the profile's bound is the smaller and 85% of the
        decided heap still holds it (by design: the dynamic space is address
        space, the gate keeps the resident set within LIMIT).

        The BP node's pools (its session funding, about 1 GB at the
        development profile) exceed 1G, so under 1G its probe refuses by name
        (machine-cannot-hold-the-pools, books/heap-command.lisp K-L2p) and its
        85% case runs under 2G."""
        node = self.node(DEVELOPER, "development")

        def scope(limit):
            return ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=" + limit,
                    "-p", "MemorySwapMax=0"]
        bp = self.bp_words(node, free_port())
        held = run(scope("1G") + [str(DEVELOPER), "--fn", "heap", "--", *[str(w) for w in bp]],
                   env=environment(), timeout=120)
        self.assertNotEqual(held.returncode, 0)
        self.assertIn("refused machine-cannot-hold-the-pools",
                      held.stdout.decode("utf-8", "replace") + held.stderr.decode("utf-8", "replace"))
        for label, words, refusal, limit in (
                ("served run", self.served_words(node), b"cold startup refused", "1G"),
                ("store owner", self.owner_words(node), b"cold startup refused", "1G"),
                ("bp node", bp, b"refused", "2G")):
            with self.subTest(command=label):
                done = run(scope(limit) + [str(DEVELOPER), "--fn", "heap", "--", *[str(w) for w in words]],
                           env=environment(), timeout=120)
                text = done.stdout.decode("utf-8", "replace")
                figure = re.match(r"heap=(\d+) MB", text)
                self.assertIsNotNone(figure, text + done.stderr.decode("utf-8", "replace"))
                heap = int(figure.group(1))
                process = start(scope(limit) + [str(DEVELOPER), "--fn", *[str(w) for w in words]], cwd=node.root,
                                env=environment({"SBCL_USER_ARGS":
                                                 "--dynamic-space-size {}MB".format(heap * 85 // 100)}))
                self.addCleanup(process.stop, 5)
                status = process.wait(timeout=120)
                self.assertNotEqual(status, 0)
                self.assertNotIn(b"LISTENING", process.stdout.since(0))
                self.assertIn(refusal, process.stderr.since(0))

if __name__ == "__main__":
    unittest.main()
