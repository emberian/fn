"""The bounds join on a native image: large articles and the deployed store's step.

D27 packets P1 (the operator's profile), P2 (codec ceilings) and P4 (carrier
v2) meet here.  Two things neither lane could run alone:

* an operator profile whose article field is 4 MiB admits POSTs of 33 KiB,
  200 KiB and 3 MiB, each re-read identical, and refuses one octet past the
  bound with the 441 that names the size;
* one served step whose reply is several MiB (PKT-481): the ARTICLE of 1, 2
  and 3 MiB articles and an OVER of about 4 MB, the owner still serving.

Run on hbox with FN_NATIVE_HOST naming the image under test.
"""
import hashlib
import os
from pathlib import Path
import time
import unittest

from tests.native_harness import (
    EXIT_OK, EXIT_UNCERTAIN, Client, Node, article as make_article, dot_stuff,
    executable)
from tests.native_profile_fixture import ProfileFixture as ProfileUpgradeFixture

MIB4 = 4 * 1024 * 1024
# The store these cases need, named: a capacity-free init sizes to the
# process budget (PKT-582, image-floor), whose 8 MiB of history the 6 MiB of
# large articles and the long-References POSTs exceed (the 805th POST was
# refused `no capacity' on batch AR's image). 256 MiB of history, 16,384
# transactions, the 4 MiB article and its record at 16 groups per article:
# the launcher's figure for it is 18,311 MB, which --mem 40G holds.
INIT_PROFILE = ("--profile", "development", "--max-transactions", "16384",
                "--max-history-octets", str(256 << 20),
                "--max-record-octets", "4199563",
                "--max-article-octets", str(MIB4),
                "--max-groups-per-article", "16")
OVERSIZE = "441 posting failed; the article exceeds the configured size"


def article(message_id, total):
    """An authored article of exactly TOTAL octets, body in 78-octet lines."""
    head = ("From: join@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: bounds join\r\nMessage-ID: {}\r\n\r\n").format(message_id).encode("ascii")
    room = total - len(head)
    lines, line = [], b"j" * 78 + b"\r\n"
    while room >= len(line):
        lines.append(line)
        room -= len(line)
    if room == 1:
        lines[0] = b"j" * 79 + b"\r\n"
    elif room:
        lines.append(b"k" * (room - 2) + b"\r\n")
    data = head + b"".join(lines)
    assert len(data) == total, (len(data), total)
    return data


def post(client, data):
    """POST DATA; the final reply line, decoded (the node may close while an
    oversize article is still being sent: the reply line is the answer)."""
    first, final = client.post(data, tolerate_send_error=True)
    assert first.startswith(b"340"), first
    return final.rstrip(b"\r\n").decode("ascii", "replace")


def read_article(client, message_id):
    """(status line, the served octets or None when not 220)."""
    status, body = client.multiline(b"ARTICLE " + message_id.encode("ascii"))
    return status, (body if status.startswith(b"220") else None)


class JoinFixture(ProfileUpgradeFixture):
    def post_and_reread(self, sizes):
        """POST each size to a running owner; the reply and whether ARTICLE
        returns the posted octets as the suffix of the stored article (the
        owner prepends Path and injection fields)."""
        rows = {}
        client = Client(self.port, timeout=300)
        try:
            for n in sizes:
                msgid = "<join-{}@example.invalid>".format(n)
                data = article(msgid, n)
                reply = post(client, data)
                if reply.startswith("240"):
                    status, stored = read_article(client, msgid)
                    body = data.split(b"\r\n\r\n", 1)[1]
                    rows[n] = (reply, stored is not None and stored.endswith(body))
                else:
                    rows[n] = (reply, None)
                    if reply.startswith("441") and n > MIB4:
                        break  # the wire closes after an oversize article
                print("POST", n, rows[n], flush=True)
        finally:
            client.close()
        return rows

    def reread(self, message_id, total):
        with Client(self.port, timeout=300) as client:
            status, stored = read_article(client, message_id)
        body = article(message_id, total).split(b"\r\n\r\n", 1)[1]
        return stored is not None and stored.endswith(body)


class LargeArticleTests(JoinFixture):
    def test_a_4_mib_profile_admits_33k_200k_3m_and_names_the_size_past_it(self):
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start(image=self.image)
        rows = self.post_and_reread([33792, 204800, 3145728, MIB4 + 1])
        self.node.stop()
        for n in (33792, 204800, 3145728):
            self.assertTrue(rows[n][0].startswith("240"), rows)
            self.assertTrue(rows[n][1], "{} did not reread identical".format(n))
        self.assertEqual(rows[MIB4 + 1][0], OVERSIZE)
        self.assertEqual(self.headroom()["transactions-used"], 3)


class LargeReplyTests(JoinFixture):
    """Standing cases for PKT-481: one served step whose REPLY is several MiB.

    Until exposure-reply-size the exposure's observation after every step
    (host/owner-host.lisp fn-owner-exposure-observe) counted 481 replies with
    one control-stack frame per reply octet, so the ARTICLE of a 2 MiB article
    and an OVER of about 4 MB each stopped the owner (exit 4, "Control stack
    exhausted" in fn-owner-chunk) while every POST before them was accepted.
    They live here, beside the 3 MiB POST, because this module is the one that
    runs an operator profile large enough to hold them and asserts identity and
    a clean owner exit; tools/throughput_gate.py measures time on small
    articles and would neither hold a 3 MiB article nor say why a step died.
    """

    OVER_ARTICLES = 2000
    OVER_REFERENCES = 2000  # octets of folded References per article

    def references(self, i):
        ids, total, j = [], 0, 0
        while total < self.OVER_REFERENCES:
            mid = "<r{}-{}@example.invalid>".format(i, j)
            ids.append(mid)
            total += len(mid) + 3
            j += 1
        return "References: " + "\r\n ".join(ids)

    def test_article_of_1_2_3_mib_and_a_4_mb_over_leave_the_owner_serving(self):
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image)
        rows = self.post_and_reread([1048576, 2097152, 3145728])
        for n in (1048576, 2097152, 3145728):
            self.assertTrue(rows[n][0].startswith("240"), rows)
            self.assertTrue(rows[n][1], "the ARTICLE of {} octets was not served identical".format(n))
        self.assertIsNone(owner.poll(), "the owner stopped serving the large ARTICLEs")
        with Client(self.port, timeout=300) as client:
            for i in range(self.OVER_ARTICLES):
                first, reply = client.post(make_article(
                    "<over-{}@example.invalid>".format(i), sender="over@example.invalid",
                    subject="large over", date=None, headers=(self.references(i),)))
                self.assertTrue(first.startswith(b"340"), first)
                self.assertTrue(reply.startswith(b"240"), (i, reply))
            words = client.command(b"GROUP fn.test").split()
            self.assertEqual(words[0], b"211", words)
            status, overview = client.multiline(b"OVER " + words[2] + b"-" + words[3])
            self.assertTrue(status.startswith(b"224"), status)
            lines, octets = overview.count(b"\r\n"), len(overview)
        self.assertEqual(lines, 3 + self.OVER_ARTICLES)
        self.assertGreater(octets, 3 * 1024 * 1024)
        self.assertIsNone(owner.poll(), "the owner stopped serving the large OVER")
        with Client(self.port, timeout=300) as client:
            self.assertTrue(client.command(b"STAT <over-0@example.invalid>").startswith(b"223"))
        self.node.stop()


MIB10 = 10 * 1024 * 1024
# PKT-693 (lane thread-stacks): a 16 MiB article field, few transactions so
# the launcher's figure stays inside the module's --mem.  Since heap-pool
# (B9, 2026-09-28) the history gate charges an article its record figure
# plus its header charge at its worst, every payload octet a header octet at
# *fn-sbud-header-weight* 8 (books/store-budget-article.lisp
# fn-sbud-article-gate-figure): about 9 x 10 MiB for the 10 MiB article, so
# H = 64 MiB refused both POSTs `unaffordable'.  The committed row carries
# its own (small) header charge, so 128 MiB admits the second article too.
INIT_PROFILE_16M = ("--profile", "development", "--max-transactions", "64",
                    "--max-history-octets", str(128 << 20),
                    "--max-record-octets", str((16 << 20) + 65536),
                    "--max-article-octets", str(16 << 20),
                    "--max-groups-per-article", "16")


class TenMibArticleTests(JoinFixture):
    """PKT-693: a 10 MiB article through a node thread's 1,024 KB control stack.

    books/records-shape.lisp's two octet conversions recursed once per octet
    in execution and exhausted a node thread's stack at about 80,000 octets.
    Here a 10 MiB article is POSTed over NNTP (a connection thread) and
    submitted by `operator post' (the control thread), each re-read over
    NNTP identical, and the owner is still serving after both, at the
    image launcher's stack, the deployed figure (PKT-876).
    """

    def test_ten_mib_article_posts_and_rereads_over_nntp_and_operator_post(self):
        created = self.op("init", *INIT_PROFILE_16M, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image)
        try:
            rows = self.post_and_reread([MIB10])
            msgid = "<ten-mib-op@example.invalid>"
            path = self.root / "ten-mib-op"
            path.write_bytes(article(msgid, MIB10))
            posted = self.op("post", "--message-id", msgid, "--payload", str(path),
                             "--group", "fn.test")
            print("operator post", posted.returncode, posted.stdout.decode().strip(),
                  posted.stderr.decode().strip(), flush=True)
            # The control client's reply deadline is a fixed 10 s
            # (host/native/control.lisp +fnn-control-io-seconds+, PKT-871):
            # a 10 MiB submission outlasts it, so the client reports
            # UNCERTAIN (exit 3) while the owner completes the commit.  The
            # article is then read back from the store, the durable fact.
            reread = False
            for _ in range(60):
                if owner.poll() is not None:
                    break
                reread = self.reread(msgid, MIB10)
                if reread:
                    break
                time.sleep(2)
            alive = owner.poll() is None
        finally:
            self.node.stop()
        self.assertTrue(rows[MIB10][0].startswith("240"), rows)
        self.assertTrue(rows[MIB10][1], "the 10 MiB NNTP POST did not reread identical")
        self.assertIn(posted.returncode, (EXIT_OK, EXIT_UNCERTAIN), posted.stderr.decode())
        self.assertTrue(reread, "the 10 MiB operator post did not reread identical")
        self.assertTrue(alive, "the owner stopped serving after the 10 MiB articles")


class PostHeapUnderMutexTests(JoinFixture):
    """Sweep S002 (D27): a served POST at a large article's size does not
    build the article as a cons list (16 octets of heap per octet) under the
    owner mutex.

    The owner runs with FN_OWNER_MEASURE=1 (host/native/owner.lisp
    fnn-owner-measured): at stop it prints, per gate class, the holds, the
    time held and the octets SBCL allocated, in all and in the largest single
    hold.  One 3 MiB POST on the 4 MiB profile (the size LargeArticleTests
    admits); the largest hold of any class must allocate less than one list
    of the article would (16 x 3 MiB).  Before S002 the
    served attempt built two (the login gate's and the transit attempt's).
    An image whose report predates the max-bytes column is judged by its
    `bytes' total, which bounds every single hold from above.
    """

    def test_large_post_allocates_less_than_one_article_list_under_the_mutex(self):
        size = 3 * 1024 * 1024
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start(image=self.image, env={"FN_OWNER_MEASURE": "1"})
        try:
            rows = self.post_and_reread([size])
        finally:
            self.node.stop()
        report = owner.stderr.since(0).decode("utf-8", "replace")
        table = {}
        for line in report.splitlines():
            if line.startswith("fn-owner-measure "):
                words = line.split()
                table[words[1]] = {k: int(v) for k, v in
                                   (w.split("=", 1) for w in words[2:])}
                print(line, flush=True)
        self.assertTrue(rows[size][0].startswith("240"), rows)
        self.assertTrue(rows[size][1], "the 3 MiB POST did not reread identical")
        self.assertTrue(table, "no fn-owner-measure report on stderr")
        largest = max(row.get("max-bytes", row["bytes"]) for row in table.values())
        print("largest hold allocated", largest, "octets;",
              round(largest / size, 2), "x the article", flush=True)
        self.assertLess(largest, 16 * size, table)


class SpanReferenceTests(JoinFixture):
    """SCN-110: the span read serves what the per-read-list read served.

    The image under test (FN_NATIVE_HOST) consumes each socket read in place
    from the octet buffer (host/native/owner.lisp fnn-owner-handle-chunk ->
    fn-owner-chunk-span); the reference image (FN_SPAN_REFERENCE_HOST, a
    build of the base whose owner coerced every read to a list and called
    fn-owner-chunk) is driven with the same POSTs on a fresh store.  Every
    reply line and every ARTICLE's octets must agree, the values of the
    injected Date and Injection-Date fields (the wall clock) aside.  The articles are
    33 KiB, 200 KiB and 3 MiB of 78-octet lines (so body lines straddle the
    512-octet reads) and one article of dot-led lines written in 7-octet
    pieces (a dot-stuffed line split across reads).
    """

    SIZES = (33792, 204800, 3145728)

    def dotted(self, message_id):
        head = ("From: join@example.invalid\r\nNewsgroups: fn.test\r\n"
                "Subject: span split\r\nMessage-ID: {}\r\n\r\n").format(message_id)
        body = "".join(".{} dot-led line {}\r\n".format("." * (i % 3), i) for i in range(200))
        return (head + body).encode("ascii")

    def masked(self, stored):
        if stored is None:
            return None
        head, sep, body = stored.partition(b"\r\n\r\n")
        lines = [ln.split(b":", 1)[0] + b": *"
                 if ln.lower().startswith((b"date:", b"injection-date:")) else ln
                 for ln in head.split(b"\r\n")]
        return b"\r\n".join(lines) + sep + body

    def served(self, image, tag):
        self.image = image
        self.node = Node(self, image, root=self.root / tag)
        self.store, self.config = self.node.store_path, self.node.config
        self.control, self.port = self.node.control, self.node.port
        created = self.op("init", *INIT_PROFILE, "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start(image=image)
        rows = []
        client = Client(self.port, timeout=300)
        try:
            for n in self.SIZES:
                msgid = "<span-{}@example.invalid>".format(n)
                data = article(msgid, n)
                reply = post(client, data)
                status, stored = read_article(client, msgid)
                rows.append((n, reply, status, self.masked(stored),
                             stored is not None and stored.endswith(data.split(b"\r\n\r\n", 1)[1])))
            msgid = "<span-dotted@example.invalid>"
            data = dot_stuff(self.dotted(msgid)) + b".\r\n"
            self.assertTrue(client.command(b"POST").startswith(b"340"))
            for i in range(0, len(data), 7):
                client.send(data[i:i + 7])
            reply = client.line().rstrip(b"\r\n").decode("ascii", "replace")
            status, stored = read_article(client, msgid)
            rows.append(("dotted", reply, status, self.masked(stored),
                         stored is not None and stored.endswith(self.dotted(msgid).split(b"\r\n\r\n", 1)[1])))
        finally:
            client.close()
        self.node.stop()
        return rows

    def test_span_read_serves_the_reference_images_bytes_at_33k_200k_3m_and_split_dot_lines(self):
        reference = os.environ.get("FN_SPAN_REFERENCE_HOST")
        if not reference or not executable(Path(reference)):
            self.skipTest("FN_SPAN_REFERENCE_HOST (the base image) is required")
        under_test = self.image
        after = self.served(under_test, "after")
        before = self.served(Path(reference), "before")
        for a, b in zip(after, before):
            print("SPAN", a[0], a[1], a[2].rstrip(), len(a[3] or b""),
                  hashlib.sha256(a[3] or b"").hexdigest()[:16],
                  hashlib.sha256(b[3] or b"").hexdigest()[:16], flush=True)
            self.assertTrue(a[1].startswith("240"), a[:3])
            self.assertTrue(a[4], "{} did not reread identical".format(a[0]))
            self.assertEqual(a[1:3], b[1:3], a[0])
            self.assertEqual(a[3], b[3], "{}: served octets differ from the reference".format(a[0]))
        self.assertEqual(len(after), len(before))


if __name__ == "__main__":
    unittest.main()
