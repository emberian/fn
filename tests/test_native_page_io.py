"""PRF-1057 / SCN-216: actual cold pread ownership through timeout.

The hold occurs after issue/acquisition and before pread, off both locks.
Reclaim retires the old file while the original worker remains live; its
close must wait. Client cancellation does not publish into a new request.
Late short/error results remain named store faults, not swallowed threads.
Runs on the unfunded line's issued rows and persistent workers
(books/page-read-direct.lisp, PRF-1234; lane cold-read-ownership).
"""
import re
import time
import unittest

from tests.native_harness import Client, EXIT, requires, scratch
from tests import test_native_expiry as expiry  # module access: no second run of its test classes here
from tests.test_native_expiry import DEVELOPER, ExpiryMixin, msgid


def page_io_logical_lines(data):
    """Collapse pretty-print whitespace only within the exact issued token6."""
    token = re.compile(rb"(PAGE-IO [^\r\n]*token=)\((\d+(?:\s+\d+){5})\)")
    data = token.sub(lambda m: m.group(1) + b"(" + b" ".join(m.group(2).split()) + b")", data)
    # A settled fault answer is a two-element list the printer may wrap too.
    fault = re.compile(rb"(PAGE-IO settled [^\r\n]*answer=)\((:FAULT)\s+(:[A-Z]+)\)")
    return fault.sub(lambda m: m.group(1) + b"(" + m.group(2) + b" " + m.group(3) + b")",
                     data).splitlines()


class PageIOObservationTests(unittest.TestCase):
    def test_wrapped_exact_token_keeps_held_and_settlement_events_distinct(self):
        text = (b"PAGE-IO held token=(1 2 3\n  4 5 99999999999999999999) file=3\n"
                b"PAGE-IO settled token=(1 2\n 3 4 5 99999999999999999999) answer=:CANCELLED\n")
        lines = page_io_logical_lines(text)
        self.assertEqual(len(lines), 2)
        self.assertRegex(lines[0], rb"PAGE-IO held token=.* file=3$")
        self.assertRegex(lines[1], rb"PAGE-IO settled token=.* answer=:CANCELLED$")
        self.assertNotRegex(lines[0], rb"answer=:PUBLISH")

    def test_wrapped_fault_answer_is_one_observation(self):
        text = (b"PAGE-IO settled token=(0 0 1 0 658\n   12345) answer=(:FAULT\n"
                b"                     :READ)\nowner core/store fault\n")
        lines = page_io_logical_lines(text)
        self.assertEqual(lines[0], b"PAGE-IO settled token=(0 0 1 0 658 12345) answer=(:FAULT :READ)")
        self.assertEqual(lines[1], b"owner core/store fault")

    def test_incomplete_token_cannot_join_a_later_event(self):
        text = b"PAGE-IO held token=(1 2 3\nPAGE-IO settled token=(4 5 6) answer=:PUBLISH\n"
        self.assertEqual(page_io_logical_lines(text), text.splitlines())

    def test_wrong_shape_is_preserved_as_an_unmatched_observation(self):
        text = b"PAGE-IO held token=(1 2 3\n 4 5) file=3\n"
        self.assertEqual(page_io_logical_lines(text), text.splitlines())


@requires(DEVELOPER)
class PageIOTests(unittest.TestCase):
    image = DEVELOPER
    post_all = ExpiryMixin.post_all
    filled = ExpiryMixin.filled
    owner_lines = ExpiryMixin.owner_lines
    node = ExpiryMixin.node
    copy_of = expiry.DeveloperExpiryTests.copy_of

    # The unfunded served line (books/page-read-direct.lisp, lane
    # cold-read-ownership): an operator run refuses a [resources] cold pool
    # (UNSUPPORTED-PROFILE cold_resources) until stage 6 installs it, so these
    # nodes run the default profile, whose cold reads hold an issued row and
    # one of the fixed persistent workers.

    def setUp(self):
        self.root = scratch(self, "fn-page-io-")

    def wait_line(self, owner, pattern, count=1):
        end = time.monotonic() + 120
        while True:
            lines = [line for line in page_io_logical_lines(owner.stderr.since(0))
                     if re.search(pattern, line)]
            if len(lines) >= count or time.monotonic() > end:
                break
            time.sleep(0.2)
        self.assertGreaterEqual(len(lines), count, owner.stderr.since(0)[-6000:])
        return lines[-1]

    def held(self, node, mode=""):
        release = node.store_path.parent / "page-io-release"
        env = {"FN_NATIVE_PAGE_IO_HOLD": str(release)}
        if mode:
            env["FN_NATIVE_PAGE_IO_RESULT"] = mode
        owner = node.start(timeout=600, env=env)
        client = Client(node.port, timeout=120, greeting=None)
        self.addCleanup(client.close, False)
        client.send(("ARTICLE %s\r\n" % msgid("p0")).encode("ascii"))
        line = self.wait_line(owner, rb"PAGE-IO held token=.* file=\d+")
        file_id = re.search(rb"file=(\d+)", line).group(1)
        return owner, client, release, file_id

    def test_matching_success_publishes_and_advances_the_original_request(self):
        node = self.filled()
        owner, client, release, _file = self.held(node)
        release.write_bytes(b"release")
        self.assertTrue(client.line().startswith(b"220"))
        self.assertIn(b"body of p0", client.block())
        self.wait_line(owner, rb"PAGE-IO settled token=.* answer=:PUBLISH")
        self.assertTrue(client.command("DATE").startswith(b"111"))
        node.stop(expect=None, grace=300)

    def test_cancel_retire_and_reuse_keep_the_old_fd_until_actual_completion(self):
        # The retirement is an operator compaction while serving: its
        # publication reseats EVERY handle the dropped log segment named at
        # the checkpoint's frames, so the segment becomes quiet
        # (fn-xrt-quiet-files) while the original worker still owns its
        # descriptor -- the close must wait for the worker's actual return.
        # (A recorded reclaim cannot retire the file here: the arena keeps a
        # reclaimed record's handle, and its extent, valid until the next
        # open -- books/payload-arena.lisp, no delete export -- so a file that
        # held a reclaimed payload stays named until restart.  That is a
        # known gap of Q16, filed by lane cold-read-ownership-2, not an
        # ownership question.)
        base = self.filled()
        for mode in ("", "stale", "duplicate"):
            with self.subTest(completion=mode or "success"):
                node = self.copy_of(base, "late-" + (mode or "success"))
                owner, old, release, file_id = self.held(node, mode)
                self.assertTrue(old.line().startswith(b"403 article temporarily unavailable"))
                self.wait_line(owner, rb"PAGE-IO cancelled token=")
                old.close(False)
                # A new socket/request, while the original worker still owns
                # a descriptor from the previous reader generation.
                new = Client(node.port, timeout=120, greeting=None)
                self.addCleanup(new.close, False)
                asked = node.operator("store", "compact", timeout=1200, expect=None)
                self.assertEqual(asked.returncode, EXIT.OK, asked.stdout + asked.stderr)
                self.wait_line(owner, rb"CHECKPOINT release reseated=[1-9]\d* incomplete=0 ")
                self.wait_line(owner, rb"PAGE-IO close-held file=" + file_id + rb"$")
                text = owner.stderr.since(0)
                self.assertNotRegex(text, rb"PAGE-IO closed file=" + file_id + rb"\r?\n")
                # The new request's read is issued at the reseated extent (the
                # checkpoint's frame, another file), never through the held
                # descriptor; the device holds it too, so it answers 403.
                stat = new.command("STAT " + msgid("p0"))
                self.assertTrue(stat.startswith(b"403 article temporarily unavailable"), stat)
                held = [l for l in page_io_logical_lines(owner.stderr.since(0))
                        if re.search(rb"PAGE-IO held token=.* file=\d+$", l)]
                self.assertEqual(len(held), 2, held)
                self.assertNotEqual(re.search(rb"file=(\d+)$", held[1]).group(1), file_id, held)
                release.write_bytes(b"release")
                self.wait_line(owner, rb"PAGE-IO settled token=.* answer=:CANCELLED")
                self.wait_line(owner, rb"PAGE-IO closed file=" + file_id + rb"$")
                if mode:
                    self.wait_line(owner, ("PAGE-IO %s answer=:STALE" % mode).encode("ascii"))
                # No late 220/body is delivered into this replacement request.
                self.assertTrue(new.command("DATE").startswith(b"111"))
                self.assertIsNotNone(new.article(msgid("n0")))
                # The reclaimed-free retirement served on: p0 reads its octets
                # through the checkpoint's frame.
                self.assertIn(b"body of p0", new.article(msgid("p0")) or b"")
                new.close(False)
                node.stop(expect=None, grace=300)

    def test_a_publication_never_retires_the_history_image(self):
        # c05 finding F1 (lane def-holder): the history image's file,
        # registered at the open and preread OFF the extent lock
        # (fn-pgs-fill-realize), is a CHECKED exclusion of retirement:
        # fnn-owner-release-extents faults by name if that id ever enters
        # the retired set (the file resource's :excluded root history-image,
        # books/page-read-direct.lisp).  A store whose checkpoint carries
        # the image is opened (the image adopted; its file id printed under
        # the hold selector), then compacted while serving (the covered
        # segments and the previous checkpoint retire): the image's file is
        # never closed, nothing is refused, and the node serves on.
        base = self.filled()
        owner = base.start(timeout=600)
        try:
            asked = base.operator("store", "compact", timeout=1200, expect=None)
            self.assertEqual(asked.returncode, EXIT.OK, asked.stdout + asked.stderr)
        finally:
            base.stop(expect=None, grace=300)
        node = self.copy_of(base, "image")
        release = node.store_path.parent / "page-io-release"
        owner = node.start(timeout=600, env={"FN_NATIVE_PAGE_IO_HOLD": str(release)})
        line = self.wait_line(owner, rb"PAGE-IO image file=\d+")
        image_id = re.search(rb"file=(\d+)", line).group(1)
        client = Client(node.port, timeout=120, greeting=None)
        self.addCleanup(client.close, False)
        self.assertIn(b"body of n0", client.article(msgid("n0")) or b"")
        asked = node.operator("store", "compact", timeout=1200, expect=None)
        self.assertEqual(asked.returncode, EXIT.OK, asked.stdout + asked.stderr)
        self.wait_line(owner, rb"CHECKPOINT release reseated=\d+ incomplete=\d+ ")
        text = owner.stderr.since(0)
        self.assertNotRegex(text, rb"PAGE-IO closed file=" + image_id + rb"\r?\n")
        self.assertNotIn(b"would be retired", text)
        self.assertIn(b"body of n0", client.article(msgid("n0")) or b"")
        self.assertIn(b"body of p0", client.article(msgid("p0")) or b"")
        client.close(False)
        node.stop(expect=None, grace=300)

    def test_a_late_short_or_error_is_settled_and_fences_the_store(self):
        base = self.filled()
        for mode in ("short", "error", "runtime-error"):
            with self.subTest(observation=mode):
                node = self.copy_of(base, "fault-" + mode)
                owner, old, release, _file = self.held(node, mode)
                self.assertTrue(old.line().startswith(b"403 article temporarily unavailable"))
                old.close(False)
                release.write_bytes(b"release")
                self.wait_line(owner, rb"PAGE-IO settled token=.* answer=\(:FAULT :(READ|ERROR)\)")
                node.exited(EXIT.FAULT, timeout=120, process=owner)
                text = owner.stderr.since(0)
                self.assertIn(b"arena-extent-read", text)
                if mode == "runtime-error":
                    self.assertIn(b"cold executor runtime failure", text)
                self.assertNotIn(b"answer=:PUBLISH", text)
                self.assertNotIn(b"outcome uncertain", text)

    def test_failed_dispatch_retains_worker_and_settles_without_buffer(self):
        node = self.filled()
        release = node.store_path.parent / "never-launched-release"
        owner = node.start(timeout=600, env={
            "FN_NATIVE_PAGE_IO_HOLD": str(release),
            "FN_NATIVE_PAGE_IO_RESULT": "launch-error",
        })
        client = Client(node.port, timeout=120, greeting=None)
        self.addCleanup(client.close, False)
        client.send(("ARTICLE %s\r\n" % msgid("p0")).encode("ascii"))
        self.wait_line(owner, rb"PAGE-IO dispatch-failed token=.* worker=retained buffer=none")
        self.wait_line(owner, rb"PAGE-IO settled token=.* answer=\(:FAULT :ERROR\)")
        node.exited(EXIT.FAULT, timeout=120, process=owner)
        text = owner.stderr.since(0)
        self.assertNotIn(b"PAGE-IO held", text)
        self.assertNotIn(b"answer=:PUBLISH", text)
        self.assertIn(b"arena-extent-read: injected job dispatch error", text)
