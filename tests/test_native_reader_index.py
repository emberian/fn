"""Saved-image witnesses for pinned NNTP Message-ID and LISTGROUP retrieval.

The Python test drives only public operator and NNTP interfaces.  The index,
archive and their correspondence are ACL2 decisions in the called owner path.
Run only against an image built from the integrated T10/T17 source:
FN_RUN_NATIVE_READER_INDEX=1 FN_NATIVE_HOST=... python3 -m unittest
tests.test_native_reader_index -v
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement, stop_and_diagnostics


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(os.environ.get("FN_RUN_NATIVE_READER_INDEX") == "1",
                     "set FN_RUN_NATIVE_READER_INDEX=1 for the integrated saved-image gate")
@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "an executable FN_NATIVE_HOST is required")
class NativeReaderIndexTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fn-reader-index-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.run_native("operator", self.config, "init", "fn.test")

    def run_native(self, *words):
        result = subprocess.run([str(IMAGE), "--fn", *map(str, words)], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=180, check=False)
        self.assertEqual(result.returncode, 0,
                         result.stderr.decode("utf-8", "replace"))
        return result

    def start_owner(self):
        proc = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(self.reap, proc)
        wait_for_announcement(proc, b"LISTENING ")
        return proc

    @staticmethod
    def reap(proc):
        if proc.poll() is None:
            proc.kill()
            proc.wait(timeout=10)
        for stream in (proc.stdout, proc.stderr):
            if stream and not stream.closed:
                stream.close()

    def stop_owner(self, proc):
        diagnostic = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostic)

    def reader(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=15)
        sock.settimeout(15)
        self.addCleanup(sock.close)
        stream = sock.makefile("rb", buffering=0)
        self.addCleanup(stream.close)
        greeting = stream.readline(4096)
        self.assertTrue(greeting.startswith(b"200 "), greeting)
        return sock, stream

    def command(self, reader, line, multiline=False):
        sock, stream = reader
        sock.sendall(line.encode("ascii") + b"\r\n")
        status = stream.readline(4096)
        self.assertTrue(status, "missing NNTP reply to " + line)
        rows = []
        if multiline and status[:1] in (b"1", b"2"):
            while True:
                row = stream.readline(32769)
                self.assertTrue(row, "unterminated reply to " + line)
                if row == b".\r\n":
                    break
                rows.append(row)
                self.assertLessEqual(len(rows), 256)
        return status, rows

    def post(self, msgid, ordinal, group="fn.test"):
        groups = (group,) if isinstance(group, str) else tuple(group)
        source = (
            b"From: reader@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: " + ",".join(groups).encode("ascii") + b"\r\n"
            b"Subject: pinned reader " + str(ordinal).encode("ascii") + b"\r\n"
            b"Message-ID: " + msgid.encode("ascii") +
            b"\r\n\r\nexact reader source\r\n")
        path = self.root / ("post-{}.eml".format(ordinal))
        path.write_bytes(source)
        words = ["operator", self.config, "post", "--message-id", msgid,
                 "--payload", path]
        for name in groups:
            words.extend(("--group", name))
        self.run_native(*words)
        return source

    def overview(self, reader, spelling, number_range):
        self.assertIn(spelling, ("OVER", "XOVER"))
        return self.command(reader, spelling + " " + number_range, True)

    def test_over_xover_crosspost_sparse_range_historical_pin_and_restart(self):
        self.run_native("operator", self.config, "group", "create", "fn.alt")
        owner = self.start_owner()
        old = self.reader()
        self.assertTrue(self.command(old, "GROUP fn.test")[0].startswith(b"211 "))
        self.assertEqual(self.overview(old, "OVER", "1-100"),
                         (b"423 no articles in that range\r\n", []))
        self.assertEqual(self.overview(old, "XOVER", "1-100"),
                         (b"420 no article(s) selected\r\n", []))

        cross = "<reader-over-cross@example.invalid>"
        alt = "<reader-over-alt@example.invalid>"
        second = "<reader-over-second@example.invalid>"
        self.post(cross, 301, ("fn.test", "fn.alt"))
        self.post(alt, 302, "fn.alt")
        middle = self.reader()
        self.assertTrue(self.command(middle, "GROUP fn.test")[0].startswith(b"211 "))
        self.assertEqual(self.overview(old, "OVER", "1-100")[1], [])
        first_status, first_rows = self.overview(middle, "OVER", "1-100")
        self.assertEqual(first_status, b"224 overview information follows\r\n")
        self.assertEqual(len(first_rows), 1)
        self.assertTrue(first_rows[0].startswith(b"1\t"), first_rows)
        self.assertIn(cross.encode(), first_rows[0])
        self.assertEqual(self.overview(middle, "XOVER", "1-100")[1], first_rows)

        self.post(second, 303, "fn.test")
        fresh = self.reader()
        self.assertTrue(self.command(fresh, "GROUP fn.test")[0].startswith(b"211 "))
        status, rows = self.overview(fresh, "OVER", "1-100")
        self.assertEqual(status, b"224 overview information follows\r\n")
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[0], first_rows[0])
        self.assertTrue(rows[1].startswith(b"2\t"), rows)
        self.assertIn(second.encode(), rows[1])
        self.assertEqual(self.overview(fresh, "XOVER", "2-2")[1], [rows[1]])
        self.assertEqual(self.overview(middle, "OVER", "2-2"),
                         (b"423 no articles in that range\r\n", []))
        self.assertEqual(self.overview(fresh, "OVER", "3-100"),
                         (b"423 no articles in that range\r\n", []))
        # Public posting allocates contiguous local numbers.  A genuinely
        # internal hole is covered by the ACL2 sparse-index witness; this
        # socket case checks a sparse bounded selection beyond the watermark.
        self.assertTrue(self.command(fresh, "GROUP fn.alt")[0].startswith(b"211 "))
        alt_status, alt_rows = self.overview(fresh, "OVER", "1-2")
        self.assertEqual(alt_status, b"224 overview information follows\r\n")
        self.assertEqual(len(alt_rows), 2)
        self.assertIn(cross.encode(), alt_rows[0])
        self.assertIn(alt.encode(), alt_rows[1])

        def read_pair(_):
            reader = self.reader()
            try:
                self.assertTrue(self.command(reader, "GROUP fn.test")[0]
                                .startswith(b"211 "))
                return self.overview(reader, "OVER", "1-100"), self.overview(
                    reader, "XOVER", "2-2")
            finally:
                reader[1].close()
                reader[0].close()

        with ThreadPoolExecutor(max_workers=4) as pool:
            for pair in pool.map(read_pair, range(4)):
                self.assertEqual(pair[0], (status, rows))
                self.assertEqual(pair[1][1], [rows[1]])
        for reader in (old, middle, fresh):
            reader[1].close()
            reader[0].close()
        self.stop_owner(owner)
        restarted = self.start_owner()
        recovered = self.reader()
        self.assertTrue(self.command(recovered, "GROUP fn.test")[0]
                        .startswith(b"211 "))
        self.assertEqual(self.overview(recovered, "OVER", "1-100"),
                         (status, rows))
        recovered[1].close()
        recovered[0].close()
        self.stop_owner(restarted)

    def listgroup(self, reader, group, number_range=None):
        command = "LISTGROUP " + group
        if number_range is not None:
            command += " " + number_range
        return self.command(reader, command, True)

    def test_listgroup_historical_pin_live_group_and_restart(self):
        owner = self.start_owner()
        old = self.reader()
        status, rows = self.listgroup(old, "fn.test")
        self.assertTrue(status.startswith(b"211 0 "), status)
        self.assertEqual(rows, [])
        self.assertEqual(self.command(old, "GROUP fn.live")[0],
                         b"411 no such newsgroup\r\n")

        # Config publication updates the served owner without repinning old.
        self.run_native("operator", self.config, "group", "create", "fn.live")
        configured = self.reader()
        self.assertEqual(self.command(old, "GROUP fn.live")[0],
                         b"411 no such newsgroup\r\n")
        self.assertTrue(self.command(configured, "GROUP fn.live")[0]
                        .startswith(b"211 "))
        status, rows = self.listgroup(configured, "fn.live")
        self.assertTrue(status.startswith(b"211 0 "), status)
        self.assertEqual(rows, [])

        self.post("<reader-group-one@example.invalid>", 101)
        middle = self.reader()
        self.assertEqual(self.listgroup(old, "fn.test")[1], [])
        self.assertEqual(self.listgroup(configured, "fn.test")[1], [])
        self.assertEqual(self.listgroup(middle, "fn.test")[1], [b"1\r\n"])

        self.post("<reader-group-two@example.invalid>", 102)
        self.post("<reader-live-one@example.invalid>", 103, "fn.live")
        fresh = self.reader()
        self.assertEqual(self.listgroup(old, "fn.test")[1], [])
        self.assertEqual(self.listgroup(middle, "fn.test")[1], [b"1\r\n"])
        self.assertEqual(self.listgroup(fresh, "fn.test")[1],
                         [b"1\r\n", b"2\r\n"])
        self.assertEqual(self.listgroup(middle, "fn.test", "2-2")[1], [])
        self.assertEqual(self.listgroup(fresh, "fn.test", "2-2")[1],
                         [b"2\r\n"])
        # An empty range above the high watermark remains empty.  The public
        # operator API does not yet make an internal allocation hole.
        self.assertEqual(self.listgroup(fresh, "fn.test", "3-5")[1], [])
        self.assertEqual(self.listgroup(old, "fn.live"),
                         (b"411 no such newsgroup\r\n", []))
        self.assertEqual(self.listgroup(configured, "fn.live")[1], [])
        self.assertEqual(self.listgroup(middle, "fn.live")[1], [])
        self.assertEqual(self.listgroup(fresh, "fn.live")[1], [b"1\r\n"])

        for reader in (old, configured, middle, fresh):
            reader[1].close()
            reader[0].close()
        self.stop_owner(owner)
        restarted = self.start_owner()
        recovered = self.reader()
        self.assertEqual(self.listgroup(recovered, "fn.test", "1-9")[1],
                         [b"1\r\n", b"2\r\n"])
        self.assertEqual(self.listgroup(recovered, "fn.live", "1-9")[1],
                         [b"1\r\n"])
        recovered[1].close()
        recovered[0].close()
        self.stop_owner(restarted)

    def test_list_counts_and_numbered_msgid_lookup(self):
        # RFC 6048 section 2.2 LIST COUNTS from the pinned buckets, and RFC
        # 3977 section 6.2.1.2's number for a Message-ID retrieval: the
        # article's number in the selected group, 0 without one or when the
        # article is not in it (books/nntp-list-counts.lisp).
        self.run_native("operator", self.config, "group", "create", "fn.live")
        owner = self.start_owner()
        one, two = "<counts-one@example.invalid>", "<counts-two@example.invalid>"
        self.post(one, 201)
        self.post(two, 202, ("fn.test", "fn.live"))
        reader = self.reader()
        status, caps = self.command(reader, "CAPABILITIES", True)
        self.assertTrue(status.startswith(b"101"), status)
        self.assertIn(b"LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS NEWSGROUPS OVERVIEW.FMT\r\n",
                      caps)
        status, rows = self.command(reader, "LIST COUNTS", True)
        self.assertEqual(status, b"215 list of newsgroups follows\r\n")
        self.assertEqual(sorted(rows), [b"fn.live 1 1 1 y\r\n", b"fn.test 2 1 2 y\r\n"])
        status, rows = self.command(reader, "list counts fn.l*", True)
        self.assertEqual(rows, [b"fn.live 1 1 1 y\r\n"])
        self.assertEqual(self.command(reader, "LIST COUNTS a b")[0],
                         b"501 syntax error\r\n")

        self.assertEqual(self.command(reader, "STAT " + two)[0],
                         ("223 0 %s retrieved\r\n" % two).encode("ascii"))
        self.assertTrue(self.command(reader, "GROUP fn.live")[0].startswith(b"211 1 1 1 "))
        self.assertEqual(self.command(reader, "STAT " + two)[0],
                         ("223 1 %s retrieved\r\n" % two).encode("ascii"))
        self.assertEqual(self.command(reader, "STAT " + one)[0],
                         ("223 0 %s retrieved\r\n" % one).encode("ascii"))
        self.assertTrue(self.command(reader, "GROUP fn.test")[0].startswith(b"211 2 1 2 "))
        status, _ = self.command(reader, "ARTICLE " + two, True)
        self.assertEqual(status, ("220 2 %s article follows\r\n" % two).encode("ascii"))
        # The number names the same article in a second command (section
        # 6.2.1.2), and the Message-ID form did not move the cursor.
        self.assertEqual(self.command(reader, "STAT")[0],
                         ("223 1 %s retrieved\r\n" % one).encode("ascii"))
        self.assertEqual(self.command(reader, "STAT 2")[0],
                         ("223 2 %s retrieved\r\n" % two).encode("ascii"))
        reader[1].close()
        reader[0].close()
        self.stop_owner(owner)

        restarted = self.start_owner()
        recovered = self.reader()
        self.assertEqual(sorted(self.command(recovered, "LIST COUNTS", True)[1]),
                         [b"fn.live 1 1 1 y\r\n", b"fn.test 2 1 2 y\r\n"])
        recovered[1].close()
        recovered[0].close()
        self.stop_owner(restarted)

    def test_listgroup_many_unrelated_groups_measured_socket_workload(self):
        groups = ["fn.work.{:02d}".format(i) for i in range(24)]
        for group in groups:
            self.run_native("operator", self.config, "group", "create", group)
        owner = self.start_owner()
        for ordinal, group in enumerate(groups):
            self.post("<reader-work-{}@example.invalid>".format(ordinal),
                      200 + ordinal, group)
        reader = self.reader()

        # 24 unrelated one-member groups, then 96 bounded socket reads on
        # one pinned view.  The measured interval excludes group creation,
        # Store publication, and process startup.  It is observational only.
        for group in (groups[0], groups[-1]):
            status, rows = self.listgroup(reader, group, "1-1")
            self.assertTrue(status.startswith(b"211 1 "), status)
            self.assertEqual(rows, [b"1\r\n"])
        started = time.monotonic()
        for _ in range(48):
            for group in (groups[0], groups[-1]):
                status, rows = self.listgroup(reader, group, "1-1")
                self.assertTrue(status.startswith(b"211 1 "), status)
                self.assertEqual(rows, [b"1\r\n"])
        elapsed = time.monotonic() - started
        print("native LISTGROUP workload: groups=24 articles=24 commands=96 "
              "range=1-1 elapsed={:.3f}s".format(elapsed))
        reader[1].close()
        reader[0].close()
        self.stop_owner(owner)

    def test_pinned_archive_and_index_through_public_reader(self):
        first = "<reader-index-first@example.invalid>"
        second = "<reader-index-second@example.invalid>"
        absent = "<reader-index-missing@example.invalid>"
        owner = self.start_owner()
        old = self.reader()
        self.assertEqual(self.command(old, "STAT " + first)[0],
                         b"430 no article with that message-id\r\n")
        first_source = self.post(first, 1)
        middle = self.reader()
        self.assertEqual(self.command(old, "STAT " + first)[0],
                         b"430 no article with that message-id\r\n")
        status = self.command(middle, "STAT " + first)[0]
        self.assertTrue(status.startswith(b"223 "), status)
        self.assertIn(first.encode(), status)
        self.assertEqual(self.command(middle, "STAT " + second)[0],
                         b"430 no article with that message-id\r\n")
        second_source = self.post(second, 2)
        fresh = self.reader()
        self.assertEqual(self.command(old, "STAT " + second)[0],
                         b"430 no article with that message-id\r\n")
        self.assertEqual(self.command(middle, "STAT " + second)[0],
                         b"430 no article with that message-id\r\n")
        status = self.command(fresh, "STAT " + second)[0]
        self.assertTrue(status.startswith(b"223 "), status)
        self.assertIn(second.encode(), status)
        self.assertEqual(self.command(fresh, "STAT " + absent)[0],
                         b"430 no article with that message-id\r\n")

        for msgid, source in ((first, first_source), (second, second_source)):
            status, rows = self.command(fresh, "ARTICLE " + msgid, True)
            self.assertTrue(status.startswith(b"220 "), status)
            self.assertTrue(b"".join(rows).endswith(source))
            status, rows = self.command(fresh, "HEAD " + msgid, True)
            self.assertTrue(status.startswith(b"221 "), status)
            self.assertIn(b"Message-ID: " + msgid.encode() + b"\r\n", rows)
            status, rows = self.command(fresh, "BODY " + msgid, True)
            self.assertTrue(status.startswith(b"222 "), status)
            self.assertEqual(rows, [b"exact reader source\r\n"])
            status, rows = self.command(fresh, "HDR :fn-verified " + msgid, True)
            self.assertEqual(status, b"225 headers follow\r\n")
            self.assertEqual(rows, [b"0 absent no-field\r\n"])

        # Independent clients exercise the same called path under bounded
        # overlap.  This records responsiveness, not an asymptotic claim.
        def batch(_):
            reader = self.reader()
            try:
                observations = []
                for _ in range(12):
                    observations.append(self.command(reader, "STAT " + first)[0])
                    observations.append(self.command(reader, "STAT " + absent)[0])
                return observations
            finally:
                reader[1].close()
                reader[0].close()

        started = time.monotonic()
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures = [pool.submit(batch, i) for i in range(4)]
            for future in as_completed(futures, timeout=90):
                observations = future.result()
                self.assertEqual(len(observations), 24)
                for index, status in enumerate(observations):
                    if index % 2 == 0:
                        self.assertTrue(status.startswith(b"223 "), status)
                        self.assertIn(first.encode(), status)
                    else:
                        self.assertEqual(status,
                                         b"430 no article with that message-id\r\n")
        print("native reader indexed 96 concurrent STAT reads: {:.3f}s".format(
            time.monotonic() - started))
        for reader in (old, middle, fresh):
            reader[1].close()
            reader[0].close()
        self.stop_owner(owner)
        reopened = self.start_owner()
        recovered = self.reader()
        for msgid in (first, second):
            status = self.command(recovered, "STAT " + msgid)[0]
            self.assertTrue(status.startswith(b"223 "), status)
            self.assertIn(msgid.encode(), status)
        self.assertEqual(self.command(recovered, "STAT " + absent)[0],
                         b"430 no article with that message-id\r\n")
        recovered[1].close()
        recovered[0].close()
        self.stop_owner(reopened)


if __name__ == "__main__":
    unittest.main()
