"""A served line that needs more payloads than the realizer keeps answers
COMPLETELY, in bounded time, while another reader is served (lane
cold-line, 2026-10-04; ledger sl-cold-line-quanta).

The realizer keeps fn-arx-read-cache-entries (8) verified entries.  A served
line runs with the realizer in its no-I/O mode: a miss discards the run, the
one missing entry is read off the owner mutex and the run repeats.  A line
that reads more than 8 payloads evicted its own entries on every run and
never finished (image set 45e05c7fd, 40 articles: HDR/XHDR/XPAT on
Newsgroups/Xref/Path/Organization, NEWNEWS).  The bridge
(test_native_cold_line_deadline) answers such a line 403 after
read-dependency-ms; this case refuses the 403: HDR/XHDR/XPAT ranges run as
header cursors whose quantum reads at most fn-hrc-payload-quantum (< 8)
payloads (books/hdr-range-cursor.lisp), and NEWNEWS reads the catalog's
tombstone column.

For each command over N articles (FN_COLD_LINE_N, default 40) in one group
it asserts: the multi-line status (225/221/230, never 403), exactly one row
per article, within LINE_SECONDS; the connection still answers DATE; and a
second reader is served meanwhile with no reply slower than OTHER_SECONDS.

    FN_NATIVE_DEVELOPER_HOST=... python3 -m unittest tests.test_native_cold_line_quanta
"""
import os
import threading
import time
import unittest

from tests.native_harness import Client, Node, executable, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
N = int(os.environ.get("FN_COLD_LINE_N", "40"))
LINE_SECONDS = float(os.environ.get("FN_COLD_LINE_SECONDS", "20"))
OTHER_SECONDS = 10
COMMANDS = [("HDR Newsgroups 1-{n}", b"225"), ("XHDR Newsgroups 1-{n}", b"221"),
            ("XPAT Newsgroups 1-{n} *", b"221"), ("HDR Xref 1-{n}", b"225"),
            ("XHDR Xref 1-{n}", b"221"), ("HDR Path 1-{n}", b"225"),
            ("XPAT Path 1-{n} *", b"221"), ("HDR Organization 1-{n}", b"225"),
            ("NEWNEWS fn.* {since}", b"230"), ("NEWNEWS fn.cold {since}", b"230")]


def article(i):
    head = ("From: cold@line.invalid\r\nNewsgroups: fn.cold\r\nSubject: cold line %d\r\n"
            "Organization: cold line\r\n"
            "Date: Thu, 01 Oct 2026 12:00:00 +0000\r\nMessage-ID: <cold-%05d@line.invalid>\r\n\r\n"
            % (i, i))
    return (head + "a body line of a cold line article.\r\n" * 20).encode("ascii")


@unittest.skipUnless(executable(IMAGE), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeColdLineQuanta(unittest.TestCase):
    def test_lines_past_the_cache_answer_completely(self):
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
        failures = []
        try:
            for template, expected in COMMANDS:
                command = template.format(n=N, since=since + " GMT")
                try:
                    with Client(node.port, timeout=LINE_SECONDS) as client:
                        self.assertTrue(client.command("GROUP fn.cold").startswith(b"211"))
                        asked = time.monotonic()
                        status = client.command(command)
                        rows = 0
                        if status[:1] == b"2":
                            while client.line() != b".\r\n":
                                rows += 1
                        seconds = time.monotonic() - asked
                        print("COLD-QUANTA {!r} status={} rows={} seconds={:.3f}".format(
                            command, status[:3].decode(), rows, seconds), flush=True)
                        if not (status[:3] == expected and rows == N and seconds < LINE_SECONDS
                                and client.command("DATE").startswith(b"111")):
                            failures.append((command, status[:3], rows, round(seconds, 3)))
                except OSError as error:  # socket timeout: the line never answered
                    print("COLD-QUANTA {!r} NO ANSWER ({})".format(command, error), flush=True)
                    failures.append((command, "no answer", type(error).__name__))
        finally:
            stop.set()
            reader.join(OTHER_SECONDS * 4)
        self.assertEqual(failures, [])
        self.assertFalse(reader.is_alive(), "the other reader was not served")
        self.assertTrue(waits and all(isinstance(w, float) and w < OTHER_SECONDS for w in waits),
                        waits[-5:])
        print("COLD-QUANTA other-replies={} other-max={:.3f}s".format(len(waits), max(waits)), flush=True)
        node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
