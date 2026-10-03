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

from tests.native_harness import Client, EXIT, keep_diagnostics, requires, scratch
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


def page_io_primitive_trace(data, token):
    """Locate literal observations for one token; no settlement oracle.

    Missing/malformed observations refuse this trace comparison. The
    diagnostic queue can drop lines, so absence does not establish that a
    primitive operation failed to occur.
    """
    lines = page_io_logical_lines(data)
    token_text = b"(" + b" ".join(str(n).encode("ascii") for n in token) + b")"
    observations = {}
    for kind in (b"direct-admit", b"fd-capture", b"job-result", b"physical-return", b"direct-settle"):
        prefix = b"PAGE-IO observed " + kind + b" token=" + token_text + b" "
        matches = [(index, line) for index, line in enumerate(lines) if line.startswith(prefix)]
        # Duplicate/stale settlement injections intentionally add events;
        # the first literal settlement is the original owner's handoff.
        if not matches:
            raise ValueError("missing primitive observation: " + kind.decode("ascii"))
        observations[kind.decode("ascii")] = matches[0]
    return observations


def page_io_issue_arguments(admission):
    """Transport the literal native issue inputs, never derive them from TOKEN.

    Older or dropped observations cannot supply a model issue input. The
    certified model, when a full matching trace exists, owns its interpretation.
    """
    match = re.search(rb" cid=(\d+) inc=(\d+) eoff=(\d+) elen=(\d+) trailer=(\d+)$", admission)
    if not match:
        raise ValueError("missing literal native issue arguments")
    return tuple(int(value) for value in match.groups())


def page_io_join_trace(data, token):
    """Exact physical join call/return observations; no inferred wait edge."""
    text = b"(" + b" ".join(str(n).encode("ascii") for n in token) + b")"
    rows = {}
    for kind in ("call", "return"):
        prefix = b"PAGE-IO observed executor-join-" + kind.encode("ascii") + b" token=" + text + b" "
        matches = [(index, line) for index, line in enumerate(page_io_logical_lines(data))
                   if line.startswith(prefix)]
        if len(matches) != 1:
            raise ValueError("missing or duplicate actual join-" + kind)
        rows[kind] = matches[0]
    return rows


def page_io_native_collection(data):
    """Transport collector status plus opaque bytes, without reading Lisp.

    COMPLETE describes the collected prefix only. The missing physical wait,
    pin and other owner edges prevent full PageIO model comparison regardless
    of collector status. Actual model replay also requires matching digests.
    """
    match = re.search(rb"NATIVE-HM \((:COMPLETE|:PENDING|:UNAVAILABLE)\s", data)
    if not match:
        raise ValueError("missing native collector readout")
    return {"collector_status": match.group(1).decode("ascii"),
            "opaque_readout": data[match.start():],
            "full_comparison": "unavailable"}


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

    def test_primitive_trace_cannot_substitute_another_token(self):
        kinds = (b"direct-admit", b"fd-capture", b"job-result", b"physical-return", b"direct-settle")
        data = b"\n".join(b"PAGE-IO observed " + k + b" token=(0 1 2 3 4 5) value=:OK" for k in kinds)
        self.assertEqual(len(page_io_primitive_trace(data, (0, 1, 2, 3, 4, 5))), 5)
        with self.assertRaisesRegex(ValueError, "missing primitive"):
            page_io_primitive_trace(data, (1, 1, 2, 3, 4, 5))

    def test_a_missing_return_cannot_be_reconstructed_from_settlement(self):
        data = b"\n".join(b"PAGE-IO observed " + k + b" token=(0 1 2 3 4 5) value=:OK"
                            for k in (b"direct-admit", b"fd-capture", b"job-result", b"direct-settle"))
        with self.assertRaisesRegex(ValueError, "physical-return"):
            page_io_primitive_trace(data, (0, 1, 2, 3, 4, 5))

    def test_model_inputs_cannot_be_reconstructed_from_a_token(self):
        token_only = b"PAGE-IO observed direct-admit token=(0 1 2 3 4 5) row=(0 1)"
        with self.assertRaisesRegex(ValueError, "missing literal native issue"):
            page_io_issue_arguments(token_only)
        literal = token_only + b" cid=7 inc=8 eoff=9 elen=10 trailer=99999999999999999999"
        self.assertEqual(page_io_issue_arguments(literal), (7, 8, 9, 10, 99999999999999999999))


    def test_complete_collector_is_not_full_physical_model_coverage(self):
        collection = page_io_native_collection(b"NATIVE-HM (:COMPLETE NIL ((:ACQUIRE \"ACTOR-1\" :EXTENT)))\n")
        self.assertEqual(collection["collector_status"], ":COMPLETE")
        self.assertEqual(collection["full_comparison"], "unavailable")
        with self.assertRaisesRegex(ValueError, "missing native collector"):
            page_io_native_collection(b"PAGE-IO settled token=(0 1 2 3 4 5) answer=:PUBLISH\n")


    def test_join_return_cannot_be_inferred_from_physical_job_return(self):
        data = b"PAGE-IO observed physical-return token=(0 1 2 3 4 5) row=(0 1)\n"
        with self.assertRaisesRegex(ValueError, "join-call"):
            page_io_join_trace(data, (0, 1, 2, 3, 4, 5))
        data += b"PAGE-IO observed executor-join-call token=(0 1 2 3 4 5) alive=T\n"
        with self.assertRaisesRegex(ValueError, "join-return"):
            page_io_join_trace(data, (0, 1, 2, 3, 4, 5))
        data += b"PAGE-IO observed executor-join-return token=(0 1 2\n 3 4 5) alive=NIL\n"
        self.assertLess(page_io_join_trace(data, (0, 1, 2, 3, 4, 5))["call"][0],
                        page_io_join_trace(data, (0, 1, 2, 3, 4, 5))["return"][0])


@requires(DEVELOPER)
class PageIOTests(unittest.TestCase):
    image = DEVELOPER
    post_all = ExpiryMixin.post_all
    filled = ExpiryMixin.filled
    owner_lines = ExpiryMixin.owner_lines

    # The unfunded served line (books/page-read-direct.lisp, lane
    # cold-read-ownership): an operator run refuses a [resources] cold pool
    # (UNSUPPORTED-PROFILE cold_resources) until stage 6 installs it, so these
    # nodes run the default profile, whose cold reads hold an issued row and
    # one of the fixed persistent workers.

    def setUp(self):
        self.observed_nodes = []
        # Registered first: retain bounded owner streams after every node's
        # cleanup, including passing schedules, when the existing keeper is
        # explicitly selected by the experiment's diagnostic directory.
        keep_diagnostics(self, self.observed_nodes)
        self.root = scratch(self, "fn-page-io-")

    def node(self, name="node"):
        node = ExpiryMixin.node(self, name)
        self.observed_nodes.append(node)
        return node

    def copy_of(self, base, name):
        node = expiry.DeveloperExpiryTests.copy_of(self, base, name)
        self.observed_nodes.append(node)
        return node

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
        self.addCleanup(release.write_bytes, b"cleanup physical hold")
        owner = node.start(timeout=600, env=env)
        client = Client(node.port, timeout=120, greeting=None)
        self.addCleanup(client.close, False)
        client.send(("ARTICLE %s\r\n" % msgid("p0")).encode("ascii"))
        line = self.wait_line(owner, rb"PAGE-IO held token=.* file=\d+")
        file_id = re.search(rb"file=(\d+)", line).group(1)
        return owner, client, release, file_id

    def assert_primitive_handoff(self, owner, file_id, verdict, answer):
        """Check actual fd binding and job/owner boundary observations.

        The certified HM comparison additionally needs actual lock/pin
        observations and matching model/native dependencies; this finite
        chronology assertion does not claim that comparison or a proof.
        """
        lines = page_io_logical_lines(owner.stderr.since(0))
        held = next(line for line in lines if re.search(rb"PAGE-IO held token=.* file=" + file_id + rb"$", line))
        token = tuple(int(n) for n in re.search(rb"token=\(([^)]+)\)", held).group(1).split())
        trace = page_io_primitive_trace(owner.stderr.since(0), token)
        issue = page_io_issue_arguments(trace["direct-admit"][1])
        self.assertEqual(str(issue[1]).encode("ascii"), file_id)
        positions = [trace[kind][0] for kind in
                     ("direct-admit", "fd-capture", "job-result", "physical-return", "direct-settle")]
        self.assertEqual(positions, sorted(positions), trace)
        capture = re.search(rb" file=(\d+) fd=(\d+)$", trace["fd-capture"][1])
        self.assertIsNotNone(capture, trace)
        self.assertEqual(capture.group(1), file_id)
        bound = [(i, line) for i, line in enumerate(lines)
                 if re.search(rb"PAGE-IO observed fd-open file=" + file_id + rb" fd=" + capture.group(2) +
                              rb" dev=\d+ ino=\d+$", line)]
        self.assertEqual(len(bound), 1, lines)
        self.assertLess(bound[0][0], trace["fd-capture"][0])
        self.assertTrue(trace["direct-settle"][1].endswith(b" verdict=" + verdict + b" answer=" + answer), trace)
        return trace

    def observed_articles(self, node, *tags):
        """Capture complete native replies to compare across later schedules."""
        node.start(timeout=600)
        client = Client(node.port, timeout=120, greeting=None)
        try:
            replies = {tag: client.article(msgid(tag)) for tag in tags}
            for tag, reply in replies.items():
                self.assertIsNotNone(reply, tag)
            return replies
        finally:
            client.close(False)
            node.stop(expect=EXIT.OK, grace=300)

    def test_matching_success_publishes_and_advances_the_original_request(self):
        node = self.filled()
        expected = self.observed_articles(node, "p0")
        owner, client, release, _file = self.held(node)
        release.write_bytes(b"release")
        self.assertTrue(client.line().startswith(b"220"))
        self.assertEqual(client.block(), expected["p0"])
        self.wait_line(owner, rb"PAGE-IO settled token=.* answer=:PUBLISH")
        self.assert_primitive_handoff(owner, _file, b":OK", b":PUBLISH")
        self.assertTrue(client.command("DATE").startswith(b"111"))
        client.close(False)
        node.stop(expect=EXIT.OK, grace=300)
        collection = page_io_native_collection(owner.stderr.since(0))
        self.assertEqual(collection["collector_status"], ":COMPLETE", collection)
        for label in (b":FD-OPEN", b":ISSUE", b":IO-BEGIN", b":JOB-RESULT", b":RETURN", b":SETTLE", b":EXTENT"):
            self.assertIn(label, collection["opaque_readout"])
        self.assertEqual(collection["full_comparison"], "unavailable")
        self.assertEqual(self.observed_articles(node, "p0"), expected)

    def test_sigterm_held_read_joins_then_reopens_exact_content(self):
        node = self.filled()
        node.start(timeout=600)
        before = Client(node.port, timeout=120, greeting=None)
        try:
            expected = before.article(msgid("p0"))
            self.assertIsNotNone(expected)
        finally:
            before.close(False)
            node.stop(expect=EXIT.OK, grace=300)
        owner, client, release, file_id = self.held(node)
        # Always release our own physical hold before the node cleanup, even
        # when an assertion fails. No timeout/kill substitutes for a receipt.
        self.assertTrue(client.line().startswith(b"403 article temporarily unavailable"))
        held = self.wait_line(owner, rb"PAGE-IO held token=.* file=" + file_id + rb"$")
        token = tuple(int(n) for n in re.search(rb"token=\(([^)]+)\)", held).group(1).split())
        self.wait_line(owner, rb"PAGE-IO cancelled token=")
        client.close(False)
        owner.terminate()  # Actual SIGTERM, not a synthetic owner outcome.
        token_text = rb"\(" + rb"\s+".join(str(n).encode("ascii") for n in token) + rb"\)"
        self.wait_line(owner, rb"PAGE-IO observed executor-join-call token=" + token_text + rb" alive=T$")
        self.assertIsNone(owner.poll(), owner.diagnostics())
        self.assertNotRegex(owner.stderr.since(0),
                            rb"PAGE-IO observed executor-join-return token=" + token_text)
        release.write_bytes(b"release physical hold")
        # Only the actual physical return/receipt and completed cleanup allow
        # this expected clean outcome; faults or pending joins fail distinctly.
        node.exited(EXIT.OK, timeout=120)
        joins = page_io_join_trace(owner.stderr.since(0), token)
        trace = self.assert_primitive_handoff(owner, file_id, b":OK", b":CANCELLED")
        self.assertTrue(joins["return"][1].endswith(b"alive=NIL"), joins)
        self.assertLess(joins["call"][0], trace["physical-return"][0])
        self.assertLess(trace["physical-return"][0], joins["return"][0])
        self.assertLess(joins["return"][0], trace["direct-settle"][0])
        # Process exit releases remaining descriptors. No individual native
        # fd-close label is invented for OS exit or missing cleanup paths.
        node.start(timeout=600)
        after = Client(node.port, timeout=120, greeting=None)
        try:
            self.assertEqual(after.article(msgid("p0")), expected)
        finally:
            after.close(False)
            node.stop(expect=EXIT.OK, grace=300)


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
        expected = self.observed_articles(base, "p0", "n0")
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
                trace = self.assert_primitive_handoff(owner, file_id, b":OK", b":CANCELLED")
                lines = page_io_logical_lines(owner.stderr.since(0))
                close = next(i for i, line in enumerate(lines)
                             if re.search(rb"PAGE-IO observed fd-close file=" + file_id + rb" fd=\d+$", line))
                self.assertLess(trace["direct-settle"][0], close, lines)
                if mode:
                    self.wait_line(owner, ("PAGE-IO %s answer=:STALE" % mode).encode("ascii"))
                # No late 220/body is delivered into this replacement request.
                self.assertTrue(new.command("DATE").startswith(b"111"))
                self.assertEqual(new.article(msgid("n0")), expected["n0"])
                # The reclaimed-free retirement served on: p0 reads its octets
                # through the checkpoint's frame.
                self.assertEqual(new.article(msgid("p0")), expected["p0"])
                new.close(False)
                node.stop(expect=EXIT.OK, grace=300)
                self.assertEqual(self.observed_articles(node, "p0", "n0"), expected)

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
                verdict = b":READ" if mode == "short" else b":ERROR"
                self.assert_primitive_handoff(owner, _file, verdict, b"(:FAULT " + verdict + b")")
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
