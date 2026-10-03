"""A served line that reads more payloads than the realizer keeps is answered
within ACL2's line deadline, never re-run forever (lane served-live,
2026-10-03; ledger cg-newnews-hang, sl-cold-line-quanta).

A served line runs with the extent realizer in its no-I/O mode: a payload
miss discards the line, the one missing entry is read off the owner mutex
and the line runs again (host/native/owner.lisp fnn-owner-cold-line).  The
realizer keeps fn-arx-read-cache-entries (8) entries, so a line that reads
more payloads than that evicts its own entries on every run.  On image set
45e05c7fd `HDR Newsgroups 1-100` over 40 articles never answered (the owner
re-ran it at full CPU); so did HDR Xref, and NEWNEWS before its catalog arm.
The bridge: one deadline per LINE from its first miss
(books/owner-time-bars.lisp fn-otb-line-dependency-step), past which ACL2's
unavailable line (403) answers it.  The real fix (each such command in
quanta that fit the cache) is the ledger's sl-cold-line-quanta.

For each command below over N articles (FN_COLD_LINE_N, default 40) in one
group the case asserts: a status within LINE_SECONDS, either the complete
reply (every article's row) or a 403; the connection still answers a
command after it; and a second reader is served meanwhile.

    FN_NATIVE_DEVELOPER_HOST=... python3 -m unittest tests.test_native_cold_line_deadline
"""
import os
import threading
import time
import unittest

from tests.native_harness import Client, Node, executable, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
N = int(os.environ.get("FN_COLD_LINE_N", "40"))
# read-dependency-ms (5,000 ms by default) plus the re-runs' own time.
LINE_SECONDS = 30
OTHER_SECONDS = 10
COMMANDS = ["HDR Newsgroups 1-{n}", "XHDR Newsgroups 1-{n}", "XPAT Newsgroups 1-{n} *",
            "HDR Xref 1-{n}", "HDR Path 1-{n}", "NEWNEWS fn.cold {since}"]


def article(i):
    head = ("From: cold@line.invalid\r\nNewsgroups: fn.cold\r\nSubject: cold line %d\r\n"
            "Date: Thu, 01 Oct 2026 12:00:00 +0000\r\nMessage-ID: <cold-%05d@line.invalid>\r\n\r\n"
            % (i, i))
    return (head + "a body line of a cold line article.\r\n" * 20).encode("ascii")


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeColdLineDeadline(unittest.TestCase):
    def test_lines_past_the_cache_are_answered_in_bounded_time(self):
        node = Node(self, IMAGE)
        node.operator("init", "--profile", "scale", "--max-article-octets", "4096", "fn.cold", "fn.other")
        owner = node.start()
        since = time.strftime("%Y%m%d %H%M%S", time.gmtime(time.time() - 86400))
        with Client(node.port, timeout=120) as poster:
            for i in range(N):
                first, final = poster.post(article(i))
                self.assertTrue(final is not None and final.startswith(b"240"), (i, first, final))

        waits, stop = [], threading.Event()

        def other_reader():
            with Client(node.port, timeout=OTHER_SECONDS * 3) as other:
                while not stop.is_set():
                    asked = time.monotonic()
                    status = other.command("GROUP fn.other")
                    waits.append(time.monotonic() - asked)
                    if not status.startswith(b"211"):
                        waits.append(("status", status))
                        return
                    time.sleep(0.05)

        reader = threading.Thread(target=other_reader)
        reader.start()
        outcomes = []
        try:
            for template in COMMANDS:
                command = template.format(n=N, since=since + " GMT")
                with Client(node.port, timeout=LINE_SECONDS) as client:
                    self.assertTrue(client.command("GROUP fn.cold").startswith(b"211"))
                    asked = time.monotonic()
                    status = client.command(command)
                    rows = 0
                    if status[:1] == b"2":
                        while client.line() != b".\r\n":
                            rows += 1
                    seconds = time.monotonic() - asked
                    outcomes.append((command, status[:3], rows, round(seconds, 3)))
                    print("COLD-LINE {!r} status={} rows={} seconds={:.3f}".format(
                        command, status[:3].decode(), rows, seconds), flush=True)
                    self.assertLess(seconds, LINE_SECONDS, command)
                    self.assertIn(status[:3], (b"221", b"225", b"230", b"403"), (command, status))
                    if status[:3] != b"403":
                        self.assertEqual(rows, N, command)
                    self.assertTrue(client.command("DATE").startswith(b"111"), command)
        finally:
            stop.set()
            reader.join(OTHER_SECONDS * 4)
        self.assertFalse(reader.is_alive(), "the other reader was not served")
        self.assertTrue(waits and all(isinstance(w, float) and w < OTHER_SECONDS for w in waits),
                        waits[-5:])
        print("COLD-LINE other-replies={} other-max={:.3f}s".format(len(waits), max(waits)), flush=True)
        node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
