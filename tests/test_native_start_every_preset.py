"""Every node type starts at every preset through the image's own launcher.

A bare launch of an image -- no SBCL_USER_ARGS, no FN_TEST_HEAP_MB, no
installed layout -- decides its heap per command, as packaging/fn's installed
branch does (tools/build_native_host.sh splices packaging/fn's fn_decide_heap
into the launcher): the image's `heap -- ARGV` probe, ACL2's fn-heap-decide.
The launcher used to run every command at the small preset's figure (1767 MB
at 207ed2afd), so a default-profile store was refused at cold start
(:default-pool-read-headroom-unavailable, books/page-read-startup.lisp
fn-prstartup-plan) and a BP node more so, and nothing started bare noticed
(train 27, CONVERGE row 35b: tests.test_bp_node_native, tests.test_native_owner).

For each preset (small, development, scale) and each node type -- the
operator's served run, the developer store owner (`owner run`) and a BP node
(`bp-node serve`), on the developer image and on the DTN developer image where
it has the verb (the DTN image omits the NNTP service, so its served run is not an NNTP start) -- the node must reach its LISTENING announcement.  A preset the
machine cannot hold is refused by the probe by name (machine-cannot-hold-profile)
and is reported as skipped, never as started.  The teeth: the same node at
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

        The store owner's probe once decided 3026 MB against about 1850 MB its
        cold start needs (1700 refused for read headroom, 1600 for protected
        runtime), so 85% still started.  Cause: the probe left OBSERVED nil,
        which sizes the history by the profile's whole bound; the operator's
        run observes the store on disk (host/native/heap.lisp
        fnn-heap-command-profile-base, the owner clause), and now the owner's
        probe does too (1934 MB).  Connections do not move the figure."""
        node = self.node(DEVELOPER, "development")
        for label, words, refusal in (
                ("served run", self.served_words(node), b"cold startup refused"),
                ("store owner", self.owner_words(node), b"cold startup refused"),
                ("bp node", self.bp_words(node, free_port()), b"refused")):
            with self.subTest(command=label):
                heap, text = probe(DEVELOPER, words)
                self.assertIsNotNone(heap, text)
                process = start([str(DEVELOPER), "--fn", *[str(w) for w in words]], cwd=node.root,
                                env=environment({"SBCL_USER_ARGS":
                                                 "--dynamic-space-size {}MB".format(heap * 85 // 100)}))
                self.addCleanup(process.stop, 5)
                status = process.wait(timeout=120)
                self.assertNotEqual(status, 0)
                self.assertNotIn(b"LISTENING", process.stdout.since(0))
                self.assertIn(refusal, process.stderr.since(0))


if __name__ == "__main__":
    unittest.main()
