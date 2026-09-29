"""PRF-1057 / SCN-216: actual cold pread ownership through timeout.

The hold occurs after issue/acquisition and before pread, off both locks.
Reclaim retires the old file while the original worker remains live; its
close must wait. Client cancellation does not publish into a new request.
Late short/error results remain named store faults, not swallowed threads.
"""
import re
import unittest

from tests.native_harness import Client, EXIT, requires, scratch
from tests.test_native_expiry import DEVELOPER, DeveloperExpiryTests, ExpiryMixin, msgid


@requires(DEVELOPER)
class PageIOTests(unittest.TestCase):
    image = DEVELOPER
    node = ExpiryMixin.node
    post_all = ExpiryMixin.post_all
    filled = ExpiryMixin.filled
    reclaim = ExpiryMixin.reclaim
    owner_lines = ExpiryMixin.owner_lines
    recorded_base = DeveloperExpiryTests.recorded_base
    copy_of = DeveloperExpiryTests.copy_of

    def setUp(self):
        self.root = scratch(self, "fn-page-io-")

    def wait_line(self, owner, pattern, count=1):
        lines = self.owner_lines(owner, re.compile(pattern), count, deadline=120)
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
        base = self.recorded_base()
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
                result = self.reclaim(node, "--recorded")
                self.assertIn(b"installed", result.stdout, result.stdout + result.stderr)
                self.wait_line(owner, rb"PAGE-IO close-held file=" + file_id + rb"$")
                text = owner.stderr.since(0)
                self.assertNotRegex(text, rb"PAGE-IO closed file=" + file_id + rb"\r?\n")
                self.assertTrue(new.command("STAT " + msgid("p0")).startswith(b"430 article reclaimed"))
                release.write_bytes(b"release")
                self.wait_line(owner, rb"PAGE-IO settled token=.* answer=:CANCELLED")
                self.wait_line(owner, rb"PAGE-IO closed file=" + file_id + rb"$")
                if mode:
                    self.wait_line(owner, ("PAGE-IO %s answer=:STALE" % mode).encode("ascii"))
                # No late 220/body is delivered into this replacement request.
                self.assertTrue(new.command("DATE").startswith(b"111"))
                self.assertIsNotNone(new.article(msgid("n0")))
                new.close(False)
                node.stop(expect=None, grace=300)

    def test_a_late_short_or_error_is_settled_and_fences_the_store(self):
        base = self.filled()
        for mode in ("short", "error"):
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
                self.assertNotIn(b"answer=:PUBLISH", text)
                self.assertNotIn(b"outcome uncertain", text)
