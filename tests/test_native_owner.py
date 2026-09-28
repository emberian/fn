"""Developer-image owner diagnostic: writable NNTP POST with no Python peer."""
import os
import re
import socket
import struct
import subprocess
import sys
import time
import unittest

from tests.native_harness import (
    EXIT, ROOT, Client, Node, dot_stuff, environment, native_image, native_peer_add,
    runtime_sbcl)

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


class NativeOwnerHandlerStructureTests(unittest.TestCase):
    def test_transit_take_uses_transfer_decision_and_store_outcome(self):
        # A transit take is a normal queued submission.  Treating the tag as
        # a fault stopped the whole owner before Store ran; the later reply
        # then surfaced only a secondary broken pipe.
        source = (ROOT / "host/native/owner.lisp").read_text()
        start = source.index("(defun fnn-owner-drain-one")
        end = source.index("(defun fnn-owner-complete-bound-submission", start)
        drain = source[start:end]
        self.assertIn("(eq taken :taken-control)", drain)
        self.assertNotIn("(not (eq taken :taken))", drain)
        self.assertIn("'fn-owner-transit-decide", drain)
        self.assertIn("'fn-owner-transit-evidence", drain)
        # The outcome and its service-log line go through one helper.
        self.assertIn("fnn-owner-transit-complete", drain)
        self.assertNotIn("'fn-owner-transit-outcome", drain)
        helper_start = source.index("(defun fnn-owner-transit-complete")
        helper = source[helper_start:start]
        self.assertIn("'fn-owner-transit-log-line", helper)
        self.assertIn("'fn-owner-transit-outcome", helper)
        self.assertIn("(fnn-owner-log)", helper)
        self.assertIn("(eq word :uncertain)", drain)

    def test_condition_handlers_and_cleanup_enclose_the_served_body(self):
        # Balanced source alone missed a live failure: handler clauses became
        # cleanup calls, and (e) invoked an undefined function on every EOF.
        # The served connection lives in host/native/mux.lisp (lane
        # connection-multiplexing): every event runs inside fnn-mux-guarded,
        # whose handlers are the per-connection worker's, and each ends in
        # fnn-mux-finish, the worker's unwind.  This checks macro structure;
        # the saved-image tests establish behavior.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head, read_forms
        forms = read_forms((ROOT / "host/native/mux.lisp").read_text())
        guarded = next(form for form in forms if head(form) == "defmacro"
                       and str(form[1]) == "fnn-mux-guarded")
        text = (ROOT / "host/native/mux.lisp").read_text()
        start = text.index("(defmacro fnn-mux-guarded")
        body = text[start:text.index("(defun fnn-mux-arm-idle", start)]
        order = ["(fnn-store-indeterminate (e)", "(fnn-store-fault (e)",
                 "(fnn-owner-connection-fault (e)",
                 "((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)",
                 "(fnn-tls-error (e)", "(serious-condition (e)"]
        at = [body.index(clause) for clause in order]
        self.assertEqual(at, sorted(at))
        self.assertEqual(body.count("(fnn-mux-finish ,l ,c)"), 6)
        self.assertTrue(guarded)
        finish = next(form for form in forms if head(form) == "defun"
                      and str(form[1]) == "fnn-mux-finish")
        start = text.index("(defun fnn-mux-finish")
        cleanup = text[start:text.index("(defmacro fnn-mux-guarded", start)]
        # Cleanup: the owner close (CID), the exposure release (the id
        # fn-exp-open registered, kept even when a fault path cleared CID;
        # PRF-161), the TLS channel, then the socket.
        steps = ["'fn-owner-close", "'fn-owner-exposure-release",
                 "(fnn-tls-close-channel", "(fnn-socket-shut"]
        at = [cleanup.index(step) for step in steps]
        self.assertEqual(at, sorted(at))
        self.assertTrue(finish)

    def test_no_os_error_after_publication_is_classified_as_a_refusal(self):
        # Campaign W2, 2026-09-24: an EIO at a finish cut escaped fnn-finish
        # and the owner's catch-all answered a durable article `441 ...
        # refused'.  Both finish cuts sit inside a handler that fences and
        # raises indeterminate, and no Store attempt maps an OS error to a
        # refusal word.
        sys.path.insert(0, str(ROOT / "tools"))
        from ledger import head, read_forms
        io_forms = read_forms((ROOT / "host/native/io.lisp").read_text())
        finish = next(form for form in io_forms if head(form) == "defun"
                      and str(form[1]) == "fnn-finish")

        def calls(form, parents=()):
            if isinstance(form, list):
                if (head(form) == "fnn-at" and len(form) == 3
                        and str(form[2]).startswith(":finish-")):
                    yield str(form[2]), [head(p) for p in parents]
                for child in form:
                    yield from calls(child, parents + (form,))
        cuts = dict(calls(finish))
        self.assertEqual(set(cuts), {":finish-consumed", ":finish-durable"})
        for cut, heads in cuts.items():
            self.assertEqual(heads[-1], "handler-case", cut)
        owner = (ROOT / "host/native/owner.lisp").read_text()
        self.assertNotIn("((or fnn-store-error fnn-os-error) () :refused)", owner)
        start = owner.index("(defmacro fnn-owner-attempt-handlers")
        end = owner.index("(defun fnn-owner-attempt ", start)
        self.assertIn("(fnn-os-error (e)", owner[start:end])
        self.assertIn(":uncertain)))", owner[start:end])

    def test_the_served_listener_passes_a_documented_accept_queue(self):
        # `ss -ltn` read `LISTEN 0 1` against the 915 node: the owner took
        # fnn-listen's default backlog, which is written for the one-client
        # diagnostic reader.  The accept thread hands each connection to a
        # worker, so a queue of one drops the client that arrives while it is
        # doing that.  The connection LIMIT is fn-own-open's and stays there.
        source = (ROOT / "host/native/owner.lisp").read_text()
        self.assertIn("(defconstant +fnn-owner-listen-backlog+", source)
        start = source.index("(defun fnn-owner-run ")
        self.assertIn(":backlog +fnn-owner-listen-backlog+", source[start:])

    def test_the_chunk_loop_keeps_its_suffix_and_reads_a_clock_per_step(self):
        # tests/native_owner_chunk_loop_raw.lisp evaluates the deployed
        # connection life (host/native/mux.lisp), fnn-owner-handle-chunk and
        # fnn-owner-advance-clock against recording stubs, so the two 915
        # defects have a check that needs no image.  The harness extracts the
        # closure of its roots from the host and refuses a stale stub or an
        # unstubbed callee by name, so a host change fails it at load, not as
        # a scenario's wrong answer; and it checks the time model's disk
        # clock event on the batched POST path.
        runtime = runtime_sbcl(IMAGE)
        if runtime is None:
            raise unittest.SkipTest("no SBCL runtime for the image and none on PATH")
        sbcl, sbcl_env = runtime
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_owner_chunk_loop_raw.lisp"],
            cwd=ROOT, env=sbcl_env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=180, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("suffix, refusal, no-progress, clock and time-event passed", output)


    def test_developer_selectors_gate_arm_the_owner_and_stop_synchronously(self):
        # tests/native_developer_selectors_raw.lisp evaluates the deployed
        # fnn-main, fnn-developer-selector and its gate, fnn-post-entry-fault,
        # fnn-owner-run-normalized, the control reply and the control stop
        # against recording stubs; the stop itself runs for real in forked
        # children.  Campaign dabebb84 findings F1 and F3 to F7.
        runtime = runtime_sbcl(IMAGE)
        if runtime is None:
            raise unittest.SkipTest("no SBCL runtime for the image and none on PATH")
        sbcl, sbcl_env = runtime
        result = subprocess.run(
            [sbcl, "--noinform", "--script",
             "tests/native_developer_selectors_raw.lisp"],
            cwd=ROOT, env=sbcl_env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=300, check=False)
        output = result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, 0, output)
        self.assertIn("native developer selectors passed", output)


class NativeOwnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(
                "developer native image missing: {} "
                "(FN_NATIVE_PROFILE=developer tools/build_native_host.sh)".format(IMAGE))

    def setUp(self):
        self.node = Node(self, IMAGE, listener=False, control=False)
        self.store = self.node.store_path
        self.node.store("init", "fn.test", expect=EXIT.OK)

    def connect_owner(self, port):
        client = Client(port, timeout=30, greeting=(b"200",))
        self.addCleanup(client.close, False)
        return client

    def inspect(self, message_id):
        return self.node.store("inspect", message_id)

    def assert_live_writer_and_reader(self, port, writer, reader, message_id):
        first, final = writer.post(self.article(message_id, b"surviving native owner body\r\n"))
        self.assertTrue(first.startswith(b"340 "))
        self.assertTrue(final.startswith(b"240 "))

        # This connection predates the post and deliberately retains its
        # pinned archive snapshot.  Prove it is still served without asking
        # that old snapshot to expose a later commit.
        status, _ = reader.multiline(b"CAPABILITIES")
        self.assertTrue(status.startswith(b"101 "))

        # A fresh reader pins the post-commit archive and proves the healthy
        # writer's article became visible without restarting the service.
        current_reader = self.connect_owner(port)
        self.assertTrue(current_reader.command(b"GROUP fn.test").startswith(b"211 "))
        answer, received = current_reader.multiline(b"ARTICLE " + message_id)
        self.assertTrue(answer.startswith(b"220 "), answer)
        self.assertIn(b"Message-ID: " + message_id + b"\r\n", received)
        self.assertIn(b"surviving native owner body\r\n", received)

    @staticmethod
    def article(message_id, body=b"native owner body\r\n"):
        return (b"From: sender@example.invalid\r\n"
                b"Newsgroups: fn.test\r\n"
                b"Subject: native owner\r\n"
                b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
                b"Message-ID: " + message_id + b"\r\n\r\n" + body)

    def test_client_disconnect_is_not_a_global_owner_fault(self):
        process, port = self.node.start_store_owner(once=False)
        with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
            self.assertTrue(client.makefile("rb", buffering=0).readline().startswith(b"200 "))
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
        self.assertIsNone(process.poll(), "owner stopped after an ordinary disconnect")

    def test_reset_peer_does_not_stop_concurrent_writer_or_reader(self):
        process, port = self.node.start_store_owner(once=False)
        resetter = self.connect_owner(port)
        reader = self.connect_owner(port)
        writer = self.connect_owner(port)
        # Force an attributable transport reset.  The peer owns this
        # socket and no shared owner transition is in progress.
        resetter.sock.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
        resetter.close(quit=False)
        time.sleep(0.1)
        self.assert_live_writer_and_reader(
            port, writer, reader, b"<after-native-reset@example.invalid>")
        self.assertIsNone(process.poll(), "peer reset stopped the owner")

    def test_local_handler_fault_uses_core_fault_and_preserves_other_clients(self):
        process, port = self.node.start_store_owner(once=False, fault="connectionhandler")
        faulted = self.connect_owner(port)
        reader = self.connect_owner(port)
        writer = self.connect_owner(port)
        self.assertEqual(
            faulted.command(b"CAPABILITIES"),
            b"403 internal fault; this connection is closed and the server continues\r\n")
        self.assert_live_writer_and_reader(
            port, writer, reader, b"<after-native-handler-fault@example.invalid>")
        self.assertIsNone(process.poll(), "local handler fault stopped the owner")

    def test_invalid_complete_feed_evidence_is_process_fault(self):
        feed = self.store / "feed"
        feed.mkdir()
        (feed / "bad.fnfd").write_bytes(b"not-a-valid-complete-feed-frame")
        result = self.node.invoke("owner", "run", self.store, "0", "1", "8",
                                  expect=EXIT.FAULT)
        self.assertIn(b"invalid complete FNFD evidence", result.stderr)

    def test_empty_v1_feed_namespace_is_preserved_as_conflicting_evidence(self):
        (self.store / "feed" / "v1").mkdir(parents=True)
        result = self.node.invoke("owner", "run", self.store, "0", "1", "8",
                                  expect=EXIT.FAULT)
        self.assertIn(b"empty FNFD v1 namespace", result.stderr)
        self.assertTrue((self.store / "feed" / "v1").is_dir())

    def test_configured_source_address_opens_native_transit_session(self):
        configured = native_peer_add(
            IMAGE, self.store, ["source", "source.invalid", "127.0.0.1", "9", "fn.*", "-",
                                "127.0.0.1", "true"], environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())

        process, port = self.node.start_store_owner()
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            status, capabilities = client.multiline(b"CAPABILITIES")
            self.assertTrue(status.startswith(b"101 "))
            self.assertIn(b"IHAVE\r\n", capabilities.splitlines(keepends=True))
            self.assertTrue(client.command(b"IHAVE <native-transit@example.invalid>")
                            .startswith(b"335 "))
            # EOF, not QUIT: the once-owner finishes on the closed connection.
            client.close(quit=False)
        self.node.exited(EXIT.OK, process=process)

    def test_once_sigterm_closes_client_with_incomplete_post(self):
        process, port = self.node.start_store_owner()
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"POST").startswith(b"340 "))
            client.send(b"From: incomplete")
            # Keep the client's descriptor open: this is SIGTERM,
            # not the easier ordinary-EOF shutdown path.
            process.terminate()
            _out, err = process.communicate(timeout=15)
            self.assertEqual(process.returncode, EXIT.OK, err.decode())

    def test_two_client_uncertainty_fences_before_later_mutation(self):
        process, port = self.node.start_store_owner(once=False, fault="postpublish")
        one = self.connect_owner(port)
        two = self.connect_owner(port)
        first, final = one.post(self.article(b"<uncertain-native-owner@example.invalid>"))
        self.assertTrue(first.startswith(b"340 "))
        # The poster is told, before the fence closes its connection
        # (campaign W1, 2026-09-24: it read a bare close).
        self.assertEqual(
            final, b"441 posting failed; the outcome is uncertain, do not repost\r\n")
        try:
            two.send(b"POST\r\n")
        except OSError:
            pass
        self.node.exited(EXIT.UNCERTAIN, process=process)
        # The already-open second session was shut down by the fence; it
        # cannot enter fn-owner-chunk after the ambiguous publication.
        try:
            later = two.line()
        except (OSError, EOFError):
            later = b""
        self.assertFalse(later.startswith(b"340 "), later)

        committed = self.inspect("<uncertain-native-owner@example.invalid>")
        self.assertEqual(committed.returncode, EXIT.OK, committed.stderr.decode())
        self.assertNotEqual(self.inspect("<later-native-owner@example.invalid>").returncode,
                            EXIT.OK)

    def test_uncertain_commit_reconciles_its_durable_feed_intent_on_restart(self):
        configured = native_peer_add(
            IMAGE, self.store, ["sink", "sink.example.invalid", "127.0.0.1", "9", "-", "fn.*",
                                "127.0.0.2", "true"], environment(), ROOT)
        self.assertEqual(configured.returncode, 0, configured.stderr.decode())

        msgid = b"<native-owner-feed-recovery@example.invalid>"
        article = self.article(msgid)
        process, port = self.node.start_store_owner(once=False, fault="postpublish")
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"POST").startswith(b"340 "))
            client.send(dot_stuff(article) + b".\r\n")
            client.close(quit=False)
        self.node.exited(EXIT.UNCERTAIN, process=process)

        journal = self.store / "feed" / "sink.fnfd"
        self.assertTrue(journal.is_file())
        intent_size = journal.stat().st_size
        self.assertGreater(intent_size, 0)

        # Opening the same native owner resolves the retained intent against
        # the physically committed Store record before it serves a client.
        restarted, port = self.node.start_store_owner()
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
            client.close(quit=False)
        self.node.exited(EXIT.OK, process=restarted)
        self.assertGreater(journal.stat().st_size, intent_size)

        inspected = self.inspect(msgid.decode("ascii"))
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr.decode())
        self.assertTrue(inspected.stdout.endswith(article), inspected.stdout[-80:])

    def test_post_is_committed_and_readable_after_owner_exit(self):
        process, port = self.node.start_store_owner()
        article = self.article(
            b"<native-owner@example.invalid>",
            (b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ\r\n"
             * 145))
        self.assertGreater(len(article), 8192)
        self.assertLessEqual(len(article), 32768)
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            first, final = client.post(article)
            self.assertTrue(first.startswith(b"340 "))
            self.assertTrue(final.startswith(b"240 "))
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
            client.close(quit=False)
        self.node.exited(EXIT.OK, process=process)
        inspected = self.inspect("<native-owner@example.invalid>")
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr.decode())
        # The injection transition prepends the ACL2-produced Path field.  The
        # accepted source article, including the 9 KiB body, remains exact.
        self.assertTrue(inspected.stdout.startswith(
            b"Path: fn.example.invalid!not-for-mail\r\n"), inspected.stdout[:80])
        self.assertTrue(inspected.stdout.endswith(article), inspected.stdout[-80:])

    def test_article_over_the_body_limit_is_refused_and_the_owner_survives(self):
        # The 915 node's first defect.  An article whose CRLF-canonical size
        # passes fn-own-body-limit (books/owner.lisp; *fn-record-max-payload*
        # is 32768) closes the wire mid-article -- books/wire.lisp
        # fn-wire-after-line answers (fn-wire-close ... :body-overlimit) -- so
        # the served step consumes a PREFIX of the socket read and leaves the
        # rest.  The host used to fault on that suffix and stop the process,
        # taking the listener with it.  The answer is the model's and was read
        # out of the certified books/served-tls-prefix on 2026-09-22: over one
        # chunk carrying POST and an article past the limit,
        # fn-served-step-counted consumes 61 of 130 octets and emits
        # (:reply :begin-article :reply :close) whose second reply is the line
        # below (books/nntp-post.lisp fn-nntp-post-step, on the :reject event
        # fn-wire-close raised).  That run is in
        # planning/evidence/owner-defects-2026-09-22.md.
        process, port = self.node.start_store_owner(once=False)
        oversize = self.article(b"<native-owner-oversize@example.invalid>",
                                b"z" * 70 + b"\r\n")
        oversize += b"y" * 70 + b"\r\n"
        while len(oversize) < 40960:
            oversize += b"y" * 70 + b"\r\n"
        self.assertGreater(len(oversize), 32768)
        client = self.connect_owner(port)
        self.assertTrue(client.command(b"POST").startswith(b"340 "))
        try:
            client.send(dot_stuff(oversize) + b".\r\n")
        except OSError:
            # The node refused and closed while the body was still going
            # out.  That is the refusal arriving early, not a failure.
            pass
        try:
            answer = client.line()
        except (OSError, EOFError):
            answer = b""
        self.assertEqual(
            answer,
            b"441 posting failed; the article exceeds the configured size\r\n",
            "an oversize article got {!r}".format(answer))
        client.close(quit=False)

        # The listener is still there and still serves, which is the whole
        # point: one long article is not a reason to stop the node.
        with Client(port, timeout=30, greeting=(b"200",)) as later:
            self.assertTrue(later.command(b"QUIT").startswith(b"205 "))
        self.assertIsNone(process.poll(), "an oversize article stopped the owner")

        # Nothing durable came of a refused article.
        self.assertNotEqual(self.inspect("<native-owner-oversize@example.invalid>").returncode,
                            EXIT.OK)

    def date_reading(self, port):
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            line = client.command(b"DATE")
        self.assertTrue(line.startswith(b"111 "), line)
        return line.split()[1]

    def post_article(self, port, message_id, dated=True):
        # An article that supplies Date and Message-ID gets no Injection-Date
        # (RFC 5537 section 3.5 item 11), so a test of the injection clock
        # posts without a Date.
        article = self.article(message_id)
        if not dated:
            article = article.replace(b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n", b"")
        with Client(port, timeout=30, greeting=(b"200",)) as client:
            first, final = client.post(article)
            self.assertTrue(first.startswith(b"340 "))
            self.assertTrue(final.startswith(b"240 "))

    def injection_date(self, message_id):
        inspected = self.inspect(message_id.decode("ascii"))
        self.assertEqual(inspected.returncode, EXIT.OK, inspected.stderr.decode())
        found = re.search(br"^Injection-Date: (.*)\r$", inspected.stdout,
                          re.MULTILINE)
        self.assertIsNotNone(found, inspected.stdout[:400])
        return found.group(1)

    def test_each_submission_and_each_connection_take_a_fresh_reading(self):
        # The 915 node's second defect.  Every article of a run carried one
        # Date and one Injection-Date and DATE answered one value for the life
        # of the process, because the native host took a clock reading at
        # startup and never again.  books/owner.lisp fn-own-open pins a
        # reading as the connection's READER environment and fn-own-read takes
        # the owner's CURRENT reading per read, so each submission is injected
        # at its own time (RFC 5537 section 3.4): supplying them is the host's
        # job, and tools/run_owner.py already did it at both points.
        process, port = self.node.start_store_owner(once=False)
        first = self.date_reading(port)
        self.post_article(port, b"<native-owner-clock-one@example.invalid>", dated=False)
        # Past the one-second resolution of the rendered value, so a fresh
        # reading cannot be mistaken for the pinned one.
        time.sleep(1.2)
        second = self.date_reading(port)
        self.post_article(port, b"<native-owner-clock-two@example.invalid>", dated=False)
        self.assertLess(first, second, "DATE answered {!r} twice".format(first))
        self.assertIsNone(process.poll(), "the owner stopped mid-run")
        self.node.stop(expect=None, process=process)

        one = self.injection_date(b"<native-owner-clock-one@example.invalid>")
        two = self.injection_date(b"<native-owner-clock-two@example.invalid>")
        self.assertNotEqual(one, two,
                            "both articles were injected at {!r}".format(one))


if __name__ == "__main__":
    unittest.main()
