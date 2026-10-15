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

from tests.native_harness import (Acl2Session, EXIT, Node, acl2_boolean, environment, free_port, executable, native_image,
                                  requires, run, start)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
from tests.bp_producer import post_articles

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

    def bp_durable_exchange(self, node, words, process):
        """A3: canonical article handoff and exact durable receipt, not a TCPCL ACK."""
        sender = node.root / "sizing-sender"
        init = run([str(DEVELOPER), "--fn", "store", str(sender), "init", GROUP],
                   env=environment(), timeout=120)
        self.assertEqual(init.returncode, EXIT.OK, init.stderr)
        msgid = b"<bp-sizing-100@example.invalid>"
        article = (b"Path: sender.bp.gate.invalid!not-for-mail\r\n"
                   b"From: sender@example.invalid\r\nNewsgroups: fn.test\r\n"
                   b"Subject: BP at decided heap\r\nDate: Mon, 12 Oct 2026 12:00:00 +0000\r\n"
                   b"Message-ID: " + msgid + b"\r\n\r\nDurable sizing exchange\r\n")
        article = post_articles(self, DEVELOPER, sender, [(msgid, article)])[msgid]
        request = node.root / "sizing-request.adu"
        with Acl2Session(DEVELOPER) as bridge:
            request.write_bytes(bridge.bp_request(
                [b"work-sizing", bridge.subject(msgid, article), b"dtn://sender/", b"dtn://receiver/",
                 b"native-policy", b"origin-native", b"wire-auth", b"terms-native"], article))
        sent = run([str(DEVELOPER), "--fn", "bp-service", "run", "127.0.0.1", str(words[2]),
                    str(request), str(node.root / "sizing-sender-fnbs"), "dtn://sender/", "dtn://receiver/",
                    "work-sizing", "work-sizing-attempt", "0", "3600000", "2", "32", "1048576", "0", "0"],
                   env=environment(), timeout=120)
        self.assertEqual(sent.returncode, EXIT.OK, sent.stderr)
        process.output_until(b"BP node delivery request-accepted", timeout=120)
        self.assertIn(b"BP application handoff durable", process.stdout.since(0))
        process.stop(grace=5)
        readback = run([str(DEVELOPER), "--fn", "store", str(node.store_path), "status", "--replay"],
                       env=environment(), timeout=300)
        self.assertEqual(readback.returncode, EXIT.OK, readback.stderr)
        self.assertRegex(readback.stdout, rb"transactions=\d+ articles=1 ")
        receipt = run([str(DEVELOPER), "--fn", "app-journal", "receipt-replay", str(node.store_path),
                       str(words[5]), str(request)], env=environment(), timeout=120)
        self.assertEqual(receipt.returncode, EXIT.OK, receipt.stderr)
        encoded = re.search(rb"receipt replay octets=(\d+) hex=([0-9a-f]+)", receipt.stdout)
        self.assertIsNotNone(encoded, receipt.stdout)
        receipt_octets = bytes.fromhex(encoded.group(2).decode("ascii"))
        self.assertEqual(len(receipt_octets), int(encoded.group(1)))
        with Acl2Session(DEVELOPER) as bridge:
            # The journal's exact canonical receipt binds the request that
            # was accepted, including its content identity and receipt ID.
            self.assertTrue(acl2_boolean(bridge.call(
                "(let* ((decoded (fn-bpa-decode-exact '" + bridge.literal(receipt_octets)
                + ")) (receipt (fn-bpa-result-message decoded))"
                + " (request (fn-bpaj-request '" + bridge.literal(request.read_bytes()) + ")))"
                + " (and (fn-bpa-result-okp decoded) (fn-bpa-receiptp receipt)"
                + " (equal (fn-bpa-receipt-id receipt) (fn-bpaj-receipt-id request))"
                + " (equal (fn-bpa-receipt-work-id receipt) (fn-bpa-request-work-id request))"
                + " (equal (fn-bpa-receipt-subject receipt) (fn-bpa-request-subject request))))")))
        inspected = run([str(DEVELOPER), "--fn", "store", str(node.store_path), "inspect",
                         msgid.decode("ascii")], env=environment(), timeout=120)
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr)
        # The receiving store records the verified hop: its own path identity
        # (policy path-identity, set in the node fixture) and "!!" ahead of the
        # sender's Path (books/path-update fn-pu-edit-path); every other octet
        # is the sender's article.
        self.assertTrue(article.startswith(b"Path: "), article[:80])
        self.assertEqual(inspected.stdout,
                         b"Path: receiver.bp.gate.invalid!!" + article[len(b"Path: "):])

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
        # The image probe calls fn-mo-serve-run-decide, which composes
        # fn-mo-serve-total-pools with this BP run's captured session charge.
        # Native startup then checks fn-bpsp-node-startup at that heap.
        # started() checks listening and history-root readiness. The durable
        # BP exchange is in test_a_heap_below_the_decided_figure_is_refused_by_name.
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
        (machine-cannot-hold-the-pools, books/heap-command.lisp K-L2p).
        A 2G limit can still refuse the replayed store at capacity zero: the resident
        partition does not imply an unobserved store fits. The positive BP
        start and 85% tooth use the machine observations, rather than a fixed
        2G assumption about the developer image."""
        node = self.node(DEVELOPER, "development")

        def scope(limit):
            if limit is None:
                return []
            return ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=" + limit,
                    "-p", "MemorySwapMax=0"]
        bp = self.bp_words(node, free_port())
        node.operator("policy", "set", "path-identity", "receiver.bp.gate.invalid", expect=EXIT.OK)
        node.operator("bp-boundary", "add", "sender-boundary", "sender.bp.gate.invalid",
                      "dtn://sender/", bp[2], GROUP, "32768", "16", "contact", bp[13], expect=EXIT.OK)
        held = run(scope("1G") + [str(DEVELOPER), "--fn", "heap", "--", *[str(w) for w in bp]],
                   env=environment(), timeout=120)
        self.assertNotEqual(held.returncode, 0)
        self.assertIn("refused machine-cannot-hold-the-pools",
                      held.stdout.decode("utf-8", "replace") + held.stderr.decode("utf-8", "replace"))
        # The 2G probe has no charged-totals header for this freshly initialized
        # store. Its owner replays the totals and refuses when even C'=0 cannot
        # fit. Validate ACL2's diagnostic relation, without pinning the figures.
        two_g = run(scope("2G") + [str(DEVELOPER), "--fn", "heap", "--", *[str(w) for w in bp]],
                    env=environment(), timeout=120)
        two_text = two_g.stdout.decode("utf-8", "replace")
        two_heap = re.match(r"heap=(\d+) MB", two_text)
        two_stack = re.search(r"stack=(\d+) KB", two_text)
        self.assertIsNotNone(two_heap, two_text + two_g.stderr.decode("utf-8", "replace"))
        self.assertIsNotNone(two_stack, two_text)
        too_small = start(scope("2G") + [str(DEVELOPER), "--fn", *[str(w) for w in bp]],
                          cwd=node.root, env=environment({"SBCL_USER_ARGS":
                          "--dynamic-space-size {}MB --control-stack-size {}KB".format(
                              two_heap.group(1), two_stack.group(1))}))
        self.addCleanup(too_small.stop, 5)
        self.assertNotEqual(too_small.wait(timeout=120), 0)
        refusal_text = too_small.stdout.since(0) + too_small.stderr.since(0)
        self.assertNotIn(b"LISTENING", refusal_text)
        capacity = re.search(rb"refused memory-cannot-hold-the-store capacity=0 of \d+ "
                             rb"bound-by=store sum=(\d+) MB limit=(\d+) MB", refusal_text)
        self.assertIsNotNone(capacity, refusal_text)
        self.assertGreater(int(capacity.group(1)), int(capacity.group(2)),
                           "the zero-reader store itself exceeds ACL2's LIMIT")
        for label, words, refusal, limit in (
                ("served run", self.served_words(node), b"cold startup refused", "1G"),
                ("store owner", self.owner_words(node), b"cold startup refused", "1G"),
                ("bp node", bp, b"refused", None)):
            with self.subTest(command=label):
                done = run(scope(limit) + [str(DEVELOPER), "--fn", "heap", "--", *[str(w) for w in words]],
                           env=environment(), timeout=120)
                text = done.stdout.decode("utf-8", "replace")
                figure = re.match(r"heap=(\d+) MB", text)
                self.assertIsNotNone(figure, text + done.stderr.decode("utf-8", "replace"))
                heap = int(figure.group(1))
                if label == "bp node":
                    # This image probe drives fn-mo-serve-run-decide; native
                    # fn-bpsp-node-startup must hold at its 100% heap before
                    # bp_durable_exchange exercises the persisted request/receipt.
                    stack = re.search(r"stack=(\d+) KB", text)
                    self.assertIsNotNone(stack, text)
                    full = start(scope(limit) + [str(DEVELOPER), "--fn", *[str(w) for w in words]],
                                 cwd=node.root, env=environment({"SBCL_USER_ARGS":
                                 "--dynamic-space-size {}MB --control-stack-size {}KB".format(heap, stack.group(1))}))
                    self.addCleanup(full.stop, 5)
                    full.announcement(b"BP NODE LISTENING ", timeout=120)
                    self.assertIn(b"BP session funding installed", full.stdout.since(0))
                    probe_limit = re.search(r"machine=(\d+) MB", text)
                    self.assertIsNotNone(probe_limit, text)
                    startup = full.stdout.since(0) + full.stderr.since(0)
                    capacity = re.search(rb"memory capacity=(\d+) of \d+ bound-by=\S+ sum=\d+ MB limit=(\d+) MB", startup)
                    self.assertIsNotNone(capacity, startup)
                    self.assertGreater(int(capacity.group(1)), 0)
                    self.assertEqual(int(capacity.group(2)), int(probe_limit.group(1)),
                                     "BP owner and probe must install the same LIMIT")
                    self.bp_durable_exchange(node, words, full)
                process = start(scope(limit) + [str(DEVELOPER), "--fn", *[str(w) for w in words]], cwd=node.root,
                                env=environment({"SBCL_USER_ARGS":
                                                 "--dynamic-space-size {}MB".format(heap * 85 // 100)
                                                 + (" --control-stack-size {}KB".format(stack.group(1))
                                                    if label == "bp node" else "")}))
                self.addCleanup(process.stop, 5)
                status = process.wait(timeout=120)
                self.assertNotEqual(status, 0)
                self.assertNotIn(b"LISTENING", process.stdout.since(0))
                self.assertIn(refusal, process.stderr.since(0))
                if label == "bp node":
                    self.assertRegex(process.stderr.since(0),
                        rb"cold startup refused: the process heap does not hold the store's protected runtime"
                        rb"|BP session funding refused \(:REFUSED :BP-SESSION-CAPACITY-NOT-HELD\)")

if __name__ == "__main__":
    unittest.main()
