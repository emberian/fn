"""Socket transcripts for the experimental loopback-only ACL2 reader."""
import os
import select
import socket
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GREETING = b"201 fn-nntp experimental reader ready\r\n"


class ReaderProcess:
    def __init__(self, store=None):
        self.store = store
        self.closed = False

    def command(self):
        command = [sys.executable, "tools/run_reader.py", "--port", "0"]
        if self.store is not None:
            command.extend(["--store", str(self.store)])
        return command

    def __enter__(self):
        self.proc = subprocess.Popen(
            self.command(),
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            ready, _, _ = select.select([self.proc.stdout], [], [], 0.2)
            if ready:
                line = self.proc.stdout.readline()
                if line.startswith(b"LISTENING "):
                    fields = line.split()
                    self.port = int(fields[1])
                    # The configuration generation the reader pinned at open.
                    self.generation = (int(fields[2].split(b"=")[1])
                                       if len(fields) > 2 else None)
                    return self
            if self.proc.poll() is not None:
                break
        if self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=8)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait(timeout=3)
        stderr = self.proc.stderr.read().decode("utf-8", "replace")
        self.proc.stdout.close()
        self.proc.stderr.close()
        raise RuntimeError("reader did not listen: " + stderr)

    def __exit__(self, *unused):
        if self.closed:
            return
        self.closed = True
        if self.proc.poll() is None:
            self.proc.terminate()
        try:
            self.proc.wait(timeout=8)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=3)
        self.proc.stdout.close()
        self.proc.stderr.close()

    def connect(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=5)
        sock.settimeout(2)
        self.assert_bytes(sock, GREETING)
        return sock

    @staticmethod
    def assert_bytes(sock, expected):
        received = b""
        while len(received) < len(expected):
            chunk = sock.recv(len(expected) - len(received))
            if not chunk:
                break
            received += chunk
        if received != expected:
            raise AssertionError("expected {!r}, received {!r}".format(expected, received))

    @staticmethod
    def read_reply(sock, count):
        received = b""
        while len(received) < count:
            chunk = sock.recv(count - len(received))
            if not chunk:
                break
            received += chunk
        return received

    @staticmethod
    def assert_closed(sock):
        try:
            received = sock.recv(1)
        except ConnectionResetError:
            # The ACL2 bridge closes after a framing rejection.  TCP may expose
            # that close as EOF or a reset depending on buffered peer input.
            received = b""
        if received != b"":
            raise AssertionError("expected closed socket, received {!r}".format(received))


class ReaderSocketTests(unittest.TestCase):
    def setUp(self):
        self.reader = ReaderProcess().__enter__()

    def tearDown(self):
        self.reader.__exit__()

    def test_fragmented_and_coalesced_commands_follow_core_transcript(self):
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"GRO")
        sock.sendall(b"UP fn.letters\r\nSTAT\r\nCAPABILITIES\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters\r\n")
        self.reader.assert_bytes(sock, b"223 1 <reader@example.invalid> retrieved\r\n")
        self.reader.assert_bytes(
            sock,
            b"101 capability list follows\r\nVERSION 2\r\nREADER\r\n"
            b"OVER MSGID\r\nHDR\r\n"
            b"LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT\r\n"
            b"IMPLEMENTATION fn-nntp-lab\r\n.\r\n")

    def test_reader_profile_transcript_over_a_real_socket(self):
        """DATE, NEWGROUPS, MODE READER, OVER and LIST OVERVIEW.FMT.

        Raw octets over the real socket adapter; expected replies are written
        from RFC 3977 sections 5.3, 7.1, 7.3, 8.3 and 8.4, not recorded from a
        previous run.  The seed article carries no Subject, From, Date or
        References, so those four overview fields are empty; :bytes is the 47
        retained octets and :lines the one retained body line.
        """
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"MODE READER\r\nLIST OVERVIEW.FMT\r\n")
        self.reader.assert_bytes(sock, b"201 posting prohibited\r\n")
        self.reader.assert_bytes(
            sock,
            b"215 order of fields in overview database\r\n"
            b"Subject:\r\nFrom:\r\nDate:\r\nMessage-ID:\r\nReferences:\r\n"
            b":bytes\r\n:lines\r\n.\r\n")

        sock.sendall(b"GROUP fn.letters\r\nOVER\r\nOVER 1-\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters\r\n")
        overview = (b"224 overview information follows\r\n"
                    b"1\t\t\t\t<reader@example.invalid>\t\t47\t1\r\n.\r\n")
        self.reader.assert_bytes(sock, overview)
        self.reader.assert_bytes(sock, overview)

        # The message-id form reports article number zero (section 8.3.2).
        sock.sendall(b"OVER <reader@example.invalid>\r\nOVER 5-2\r\n")
        self.reader.assert_bytes(
            sock,
            b"224 overview information follows\r\n"
            b"0\t\t\t\t<reader@example.invalid>\t\t47\t1\r\n.\r\n")
        self.reader.assert_bytes(sock, b"423 no articles in that range\r\n")

        sock.sendall(b"NEWGROUPS 19700101 000000 GMT\r\n"
                     b"NEWGROUPS 20990101 000000 GMT\r\n"
                     b"NEWGROUPS 20990101 000000 UTC\r\n")
        self.reader.assert_bytes(
            sock,
            b"231 list of new newsgroups follows\r\n.\r\n")
        self.reader.assert_bytes(
            sock, b"231 list of new newsgroups follows\r\n.\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")

        # DATE reports the host clock, so only its shape is fixed here.
        sock.sendall(b"DATE\r\n")
        reply = self.reader.read_reply(sock, 20)
        self.assertTrue(reply.startswith(b"111 "), reply)
        self.assertTrue(reply.endswith(b"\r\n"), reply)
        self.assertEqual(len(reply), 20, reply)
        self.assertTrue(reply[4:18].isdigit(), reply)
        self.assertEqual(reply[4:8], time.strftime("%Y", time.gmtime()).encode())

    def test_legacy_commands_transcript_over_a_real_socket(self):
        """XOVER, XHDR, HDR, LIST HEADERS and LIST ACTIVE.TIMES.

        Raw octets over the real socket adapter; expected replies are written
        from RFC 2980 sections 2.6 and 2.8 and RFC 3977 sections 8.5 and 8.6,
        not recorded from a previous run.  The seed article is
        `Message-ID: <reader@example.invalid>' with the one body line
        `Hello': 47 retained octets, one body line, and no Subject, so the
        Subject field of both OVER and HDR is empty.
        """
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"GROUP fn.letters\r\nXOVER\r\nXOVER 1-\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters\r\n")
        overview = (b"224 overview information follows\r\n"
                    b"1\t\t\t\t<reader@example.invalid>\t\t47\t1\r\n.\r\n")
        self.reader.assert_bytes(sock, overview)
        self.reader.assert_bytes(sock, overview)

        # RFC 2980 section 2.8.1 lists 420, not RFC 3977's 423, for an empty
        # range, and defines no message-id form at all.
        sock.sendall(b"XOVER 5-2\r\nXOVER <reader@example.invalid>\r\n")
        self.reader.assert_bytes(sock, b"420 no article(s) selected\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")

        # RFC 3977 section 8.5.2: number, space, the header content with the
        # name, colon and first space removed; an absent header renders empty.
        sock.sendall(b"HDR message-id 1\r\nHDR subject 1\r\n"
                     b"HDR :bytes 1\r\nHDR :lines 1\r\n")
        self.reader.assert_bytes(
            sock,
            b"225 headers follow\r\n1 <reader@example.invalid>\r\n.\r\n")
        self.reader.assert_bytes(sock, b"225 headers follow\r\n1 \r\n.\r\n")
        self.reader.assert_bytes(sock, b"225 headers follow\r\n1 47\r\n.\r\n")
        self.reader.assert_bytes(sock, b"225 headers follow\r\n1 1\r\n.\r\n")

        # Section 8.5.2: the message-id form labels its line with zero.
        # RFC 2980 section 2.6 labels it with the message-id, and 221 is its
        # initial line.
        sock.sendall(b"HDR message-id <reader@example.invalid>\r\n"
                     b"XHDR message-id <reader@example.invalid>\r\n"
                     b"XHDR message-id 1\r\n")
        self.reader.assert_bytes(
            sock,
            b"225 headers follow\r\n0 <reader@example.invalid>\r\n.\r\n")
        self.reader.assert_bytes(
            sock,
            b"221 header follows\r\n"
            b"<reader@example.invalid> <reader@example.invalid>\r\n.\r\n")
        self.reader.assert_bytes(
            sock,
            b"221 header follows\r\n1 <reader@example.invalid>\r\n.\r\n")

        # Section 8.5.2 assigns 423 to an empty range; RFC 2980 section 2.6.1
        # assigns 420.  430 for an absent message-id is common to both.
        sock.sendall(b"HDR subject 5-2\r\nXHDR subject 5-2\r\n"
                     b"HDR subject <absent@example.invalid>\r\nHDR\r\n")
        self.reader.assert_bytes(sock, b"423 no articles in that range\r\n")
        self.reader.assert_bytes(sock, b"420 no article(s) selected\r\n")
        self.reader.assert_bytes(
            sock, b"430 no article with that message-id\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")

    def test_xpat_transcript_over_a_real_socket(self):
        """RFC 2980 section 2.9.  XPAT is XHDR with a wildmat on the value.

        The seed article is `Message-ID: <reader@example.invalid>' with no
        Subject, so `XPAT subject' matches only the empty value and
        `XPAT message-id' matches the identifier.  Expected replies are
        written from section 2.9.1's response list, not recorded; that list
        is 221/430/502 and has no 501 in it.  No header value of this fixture
        contains an SP, so the matching multi-token case lives in
        tests/acl2/nntp-legacy-tests.lisp, which carries an article whose
        Subject is a phrase.
        """
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"GROUP fn.letters\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters\r\n")

        # A matching pattern: 221 and the XHDR line.
        sock.sendall(b"XPAT message-id 1-1 *example.invalid*\r\n")
        self.reader.assert_bytes(
            sock,
            b"221 header follows\r\n1 <reader@example.invalid>\r\n.\r\n")
        # Section 2.9: "This includes an empty list."  A non-matching
        # pattern is still 221, not 420 and not 423.
        sock.sendall(b"XPAT message-id 1-1 *nothing*\r\n")
        self.reader.assert_bytes(sock, b"221 header follows\r\n.\r\n")
        # A pattern that selects everything is XHDR's own block.
        sock.sendall(b"XPAT message-id 1-1 *\r\nXHDR message-id 1-1\r\n")
        expected = (b"221 header follows\r\n1 <reader@example.invalid>\r\n"
                    b".\r\n")
        self.reader.assert_bytes(sock, expected)
        self.reader.assert_bytes(sock, expected)
        # The message-id form labels with the message-id (section 2.9 as
        # section 2.6 does), and 430 when no such article exists.
        sock.sendall(b"XPAT message-id <reader@example.invalid> *\r\n"
                     b"XPAT message-id <absent@example.invalid> *\r\n")
        self.reader.assert_bytes(
            sock,
            b"221 header follows\r\n"
            b"<reader@example.invalid> <reader@example.invalid>\r\n.\r\n")
        self.reader.assert_bytes(
            sock, b"430 no article with that message-id\r\n")
        # Section 2.9 requires at least one pattern, and joins the trailing
        # arguments with a single space into one pattern.  The first two
        # commands are the arity refusals.  The third is the one OB-XPAT-SPACE
        # was about: the joined pattern `*reader* *invalid*' carries an SP,
        # which RFC 3977 section 4.1's <wildmat-exact> excludes and the
        # header-value profile of decision D19 admits, so it PARSES.  This
        # message-id contains no SP, so the pattern does not match and the
        # reply is section 2.9's 221 with an empty list -- which is what INN
        # 2.7.4 answers for the same command
        # (planning/evidence/inn-xpat-2026-09-20.md).  Before D19 it was 501.
        # The fourth command is the single-token control, unchanged.
        sock.sendall(b"XPAT message-id 1-1\r\nXPAT\r\n"
                     b"XPAT message-id 1-1 *reader* *invalid*\r\n"
                     b"XPAT message-id 1-1 *reader*\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")
        self.reader.assert_bytes(sock, b"221 header follows\r\n.\r\n")
        self.reader.assert_bytes(
            sock,
            b"221 header follows\r\n1 <reader@example.invalid>\r\n.\r\n")
        # A pattern whose SP falls where the value has one does match: the
        # message-id has no SP anywhere, so `*@example* *invalid*' is still
        # the empty list, while a genuinely malformed pattern is still 501.
        # A bare `!' is the post-comma negation marker in both profiles and an
        # item in neither.
        sock.sendall(b"XPAT message-id 1-1 *@example* *invalid*\r\n"
                     b"XPAT message-id 1-1 !reader\r\n")
        self.reader.assert_bytes(sock, b"221 header follows\r\n.\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")

    def test_list_variants_transcript_over_a_real_socket(self):
        """LIST HEADERS, LIST NEWSGROUPS, LIST ACTIVE wildmat, ACTIVE.TIMES.

        Expected replies from RFC 3977 sections 7.6.3, 7.6.4, 7.6.6 and 8.6
        and RFC 2980 sections 2.1.2, 2.1.3 and 2.1.6.
        """
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        # Section 8.6.2: any header may be retrieved, so the list is the
        # single colon plus the metadata items and no header names.
        sock.sendall(b"LIST HEADERS\r\nLIST HEADERS MSGID\r\n")
        headers = b"215 field list follows\r\n:\r\n:bytes\r\n:lines\r\n.\r\n"
        self.reader.assert_bytes(sock, headers)
        self.reader.assert_bytes(sock, headers)

        # Section 7.6.6: name, TAB, description.  fn's group table carries no
        # description, so every group gets the same fixed marker rather than
        # an invented sentence; an EMPTY field would make nntplib drop the
        # group from descriptions() entirely (measured 2026-09-20).
        sock.sendall(b"LIST NEWSGROUPS\r\nLIST NEWSGROUPS fn.*\r\n"
                     b"LIST NEWSGROUPS other.*\r\n")
        newsgroups = (b"215 list of newsgroups follows\r\n"
                      b"fn.letters\t(no description)\r\n.\r\n")
        self.reader.assert_bytes(sock, newsgroups)
        self.reader.assert_bytes(sock, newsgroups)
        self.reader.assert_bytes(sock, b"215 list of newsgroups follows\r\n.\r\n")

        # Sections 7.6.3 / RFC 2980 section 2.1.2: LIST ACTIVE takes a wildmat.
        sock.sendall(b"LIST ACTIVE\r\nLIST ACTIVE fn.l*\r\nLIST ACTIVE zz*\r\n")
        active = (b"215 list of active newsgroups follows\r\n"
                  b"fn.letters 1 1 y\r\n.\r\n")
        self.reader.assert_bytes(sock, active)
        self.reader.assert_bytes(sock, active)
        self.reader.assert_bytes(
            sock, b"215 list of active newsgroups follows\r\n.\r\n")

        # Section 7.6.4 permits omitting a group whose creation information is
        # unavailable.  The served connection carries no persisted creation
        # facts yet, so the block is empty rather than a date fn invented.
        sock.sendall(b"LIST ACTIVE.TIMES\r\nLIST ACTIVE.TIMES fn.*\r\n"
                     b"LIST DISTRIBUTIONS\r\nLIST SUBSCRIPTIONS\r\n"
                     b"LIST NOSUCHVARIANT\r\n")
        self.reader.assert_bytes(sock, b"215 information follows\r\n.\r\n")
        self.reader.assert_bytes(sock, b"215 information follows\r\n.\r\n")
        self.reader.assert_bytes(sock, b"503 data item not stored\r\n")
        # RFC 2980 section 2.1.8's own response list is 215 or 503; slrn 1.0.3
        # sends LIST SUBSCRIPTIONS on every connection.
        self.reader.assert_bytes(sock, b"503 data item not stored\r\n")
        self.reader.assert_bytes(sock, b"501 unsupported LIST variant\r\n")

    def test_help_lists_every_dispatched_command(self):
        """RFC 3977 section 7.2.  The list is the dispatcher's, not a subset."""
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"HELP\r\n")
        self.reader.assert_bytes(
            sock,
            b"100 help text follows\r\n"
            b"CAPABILITIES HELP QUIT MODE DATE POST\r\n"
            b"GROUP LISTGROUP LIST NEXT LAST NEWGROUPS\r\n"
            b"ARTICLE HEAD BODY STAT\r\n"
            b"OVER XOVER HDR XHDR XPAT\r\n.\r\n")

    def test_quit_replies_then_closes(self):
        sock = self.reader.connect()
        sock.sendall(b"QUIT\r\n")
        self.reader.assert_bytes(sock, b"205 closing connection\r\n")
        self.assertEqual(sock.recv(1), b"")
        sock.close()

    def test_listgroup_filtered_empty_response_still_selects_first_article(self):
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"LISTGROUP fn.letters 2-\r\nSTAT\r\nLISTGROUP\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters list follows\r\n.\r\n")
        self.reader.assert_bytes(sock, b"223 1 <reader@example.invalid> retrieved\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters list follows\r\n1\r\n.\r\n")

    def test_malformed_and_overlimit_input_close(self):
        for payload in (b"STAT\n", b"A" * 511 + b"\r\n"):
            with self.subTest(payload=payload[:8]):
                sock = self.reader.connect()
                sock.sendall(payload)
                self.reader.assert_bytes(sock, b"501 syntax error\r\n")
                self.reader.assert_closed(sock)
                sock.close()

    def test_list_wildmat_filters_in_acl2_and_preserves_session_on_syntax_error(self):
        sock = self.reader.connect()
        self.addCleanup(sock.close)
        sock.sendall(b"GROUP fn.letters\r\nLIST ACTIVE fn.letters\r\n"
                     b"LIST NEWSGROUPS no.*\r\nLIST ACTIVE [\r\nSTAT\r\n")
        self.reader.assert_bytes(sock, b"211 1 1 1 fn.letters\r\n")
        self.reader.assert_bytes(
            sock, b"215 list of active newsgroups follows\r\n"
            b"fn.letters 1 1 y\r\n.\r\n")
        self.reader.assert_bytes(sock, b"215 list of newsgroups follows\r\n.\r\n")
        self.reader.assert_bytes(sock, b"501 syntax error\r\n")
        self.reader.assert_bytes(sock, b"223 1 <reader@example.invalid> retrieved\r\n")

    def test_exact_510_octet_command_is_framed_but_511_octets_closes(self):
        accepted = self.reader.connect()
        accepted.sendall(b"X" * 510 + b"\r\nSTAT\r\n")
        self.reader.assert_bytes(accepted, b"500 command not recognized\r\n")
        self.reader.assert_bytes(accepted, b"412 no newsgroup selected\r\n")
        accepted.close()

        rejected = self.reader.connect()
        rejected.sendall(b"X" * 511 + b"\r\n")
        self.reader.assert_bytes(rejected, b"501 syntax error\r\n")
        self.reader.assert_closed(rejected)
        rejected.close()

    def test_sessions_do_not_leak_selected_group(self):
        first = self.reader.connect()
        first.sendall(b"GROUP fn.letters\r\n")
        self.reader.assert_bytes(first, b"211 1 1 1 fn.letters\r\n")
        first.close()

        second = self.reader.connect()
        self.addCleanup(second.close)
        second.sendall(b"STAT\r\n")
        self.reader.assert_bytes(second, b"412 no newsgroup selected\r\n")

    def test_reset_client_does_not_end_listener(self):
        dropped = socket.create_connection(("127.0.0.1", self.reader.port), timeout=5)
        dropped.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER,
                           struct.pack("ii", 1, 0))
        dropped.close()
        time.sleep(0.1)

        healthy = self.reader.connect()
        self.addCleanup(healthy.close)
        healthy.sendall(b"STAT\r\n")
        self.reader.assert_bytes(healthy, b"412 no newsgroup selected\r\n")


class StoreReaderSocketTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-reader-store-")
        self.store = Path(self.temp.name) / "store"
        self.payload = Path(self.temp.name) / "article"
        self.store_command("init")

    def tearDown(self):
        self.temp.cleanup()

    def store_command(self, command, *args, expected=0):
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(self.store), command,
             *map(str, args)], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode != expected:
            self.fail("store {} returned {}\nstdout={}\nstderr={}".format(
                command, result.returncode, result.stdout, result.stderr))
        return result

    def post(self, msgid, payload, groups):
        self.payload.write_bytes(payload)
        args = ["--message-id", msgid, "--payload", self.payload]
        for group in groups:
            args.extend(["--group", group])
        self.store_command("post", *args)

    def test_store_snapshot_returns_exact_durable_article_and_holds_lock(self):
        payload = (b"Message-ID: <durable@example.invalid>\r\nSubject: durable\r\n"
                   b"\r\nDurable body\r\n")
        self.post("<durable@example.invalid>", payload, ("fn.letters", "fn.test"))
        reader = ReaderProcess(self.store).__enter__()
        try:
            first = reader.connect()
            first.sendall(b"GROUP fn.test\r\nARTICLE\r\n")
            reader.assert_bytes(first, b"211 1 1 1 fn.test\r\n")
            reader.assert_bytes(
                first, b"220 1 <durable@example.invalid> article follows\r\n" +
                payload + b".\r\n")
            first.close()

            second = reader.connect()
            second.sendall(b"STAT\r\nSTAT <reader@example.invalid>\r\n")
            reader.assert_bytes(second, b"412 no newsgroup selected\r\n")
            reader.assert_bytes(second, b"430 no article with that message-id\r\n")
            second.close()

            self.payload.write_bytes(b"Message-ID: <blocked@example.invalid>\r\n\r\nblocked\r\n")
            blocked = self.store_command(
                "post", "--message-id", "<blocked@example.invalid>", "--payload", self.payload,
                "--group", "fn.letters", expected=1)
            self.assertIn(b"already locked", blocked.stderr)
        finally:
            reader.__exit__()

        self.post("<after-reader@example.invalid>",
                  b"Message-ID: <after-reader@example.invalid>\r\n\r\nafter\r\n",
                  ("fn.letters",))

    def test_store_with_non_news_payload_degrades_only_that_article(self):
        # Defect D3 in planning/review-2026-09-18-independent.md: this store
        # used to refuse to open at all, and before that every command in the
        # session answered 503.  A committed article whose stored bytes are not
        # CRLF-framed now degrades only itself.
        self.post("<opaque@example.invalid>", b"opaque durable bytes", ("fn.letters",))
        self.post("<news@example.invalid>",
                  b"Message-ID: <news@example.invalid>\r\n\r\nreadable\r\n",
                  ("fn.letters",))
        with ReaderProcess(self.store) as reader:
            client = reader.connect()
            client.sendall(b"CAPABILITIES\r\n")
            reader.assert_bytes(
                client,
                b"101 capability list follows\r\nVERSION 2\r\nREADER\r\n"
                b"OVER MSGID\r\nHDR\r\n"
                b"LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT\r\n"
                b"IMPLEMENTATION fn-nntp-lab\r\n.\r\n")
            client.sendall(b"GROUP fn.letters\r\n")
            reader.assert_bytes(client, b"211 2 1 2 fn.letters\r\n")
            client.sendall(b"STAT 1\r\n")
            reader.assert_bytes(
                client, b"223 1 <opaque@example.invalid> retrieved\r\n")
            client.sendall(b"ARTICLE 1\r\n")
            reader.assert_bytes(
                client, b"503 stored article framing unavailable\r\n")
            client.sendall(b"ARTICLE 2\r\n")
            reader.assert_bytes(
                client,
                b"220 2 <news@example.invalid> article follows\r\n"
                b"Message-ID: <news@example.invalid>\r\n\r\nreadable\r\n.\r\n")
            client.sendall(b"QUIT\r\n")
            reader.assert_bytes(client, b"205 closing connection\r\n")
            client.close()


if __name__ == "__main__":
    unittest.main()
