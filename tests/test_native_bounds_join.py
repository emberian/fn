"""The bounds join on a native image: large articles and the deployed store's step.

D27 packets P1 (the operator's profile), P2 (codec ceilings) and P4 (carrier
v2) meet here.  Two things neither lane could run alone:

* an operator profile whose article field is 4 MiB admits POSTs of 33 KiB,
  200 KiB and 3 MiB, each re-read identical, and refuses one octet past the
  bound with the 441 that names the size;
* the deployed store's offline step, rehearsed on a format-7 scale store
  written by a pre-D27 image (FN_FORMAT7_IMAGE): open under the new image,
  upgrade with a 4 MiB article field, roll back by restoring the kept
  config.json and reopen under the old image, upgrade again, POST 3 MiB,
  re-read, restart, still open (planning/evidence/bounds-join-2026-09-25.md).

* one served step whose reply is several MiB (PKT-481): the ARTICLE of 1, 2
  and 3 MiB articles and an OVER of about 4 MB, the owner still serving.

Run on hbox with FN_NATIVE_HOST naming the image under test.
"""
import shutil
import signal
import socket
import unittest

from tests import test_native_operator_verbs as verbs
from tests.test_native_profile_upgrade import (FORMAT7_IMAGE, FORMAT7_SCALE_FRAME,
                                               ProfileUpgradeFixture)

EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED
MIB4 = 4 * 1024 * 1024
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


def dot_stuff(data):
    return b"".join((b"." + ln if ln.startswith(b".") else ln)
                    for ln in data.splitlines(keepends=True))


class NntpClient:
    def __init__(self, port):
        self.conn = socket.create_connection(("127.0.0.1", port), timeout=300)
        self.stream = self.conn.makefile("rwb")
        assert self.stream.readline().startswith(b"200")

    def post(self, data):
        self.stream.write(b"POST\r\n")
        self.stream.flush()
        assert self.stream.readline().startswith(b"340")
        try:
            self.stream.write(dot_stuff(data) + b".\r\n")
            self.stream.flush()
        except OSError:
            pass
        return self.stream.readline().rstrip(b"\r\n").decode("ascii", "replace")

    def article(self, message_id):
        self.stream.write(b"ARTICLE " + message_id.encode("ascii") + b"\r\n")
        self.stream.flush()
        status = self.stream.readline()
        if not status.startswith(b"220"):
            return status, None
        lines = []
        while True:
            ln = self.stream.readline()
            if ln == b".\r\n":
                break
            lines.append(ln[1:] if ln.startswith(b"..") else ln)
        return status, b"".join(lines)

    def close(self):
        try:
            self.stream.write(b"QUIT\r\n")
            self.stream.flush()
        except OSError:
            pass
        self.conn.close()


class JoinFixture(ProfileUpgradeFixture):
    def post_and_reread(self, sizes):
        """POST each size to a running owner; the reply and whether ARTICLE
        returns the posted octets as the suffix of the stored article (the
        owner prepends Path and injection fields)."""
        rows = {}
        client = NntpClient(self.port)
        try:
            for n in sizes:
                msgid = "<join-{}@example.invalid>".format(n)
                data = article(msgid, n)
                reply = client.post(data)
                if reply.startswith("240"):
                    status, stored = client.article(msgid)
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
        client = NntpClient(self.port)
        try:
            status, stored = client.article(message_id)
        finally:
            client.close()
        body = article(message_id, total).split(b"\r\n\r\n", 1)[1]
        return stored is not None and stored.endswith(body)


class LargeArticleTests(JoinFixture):
    def test_a_4_mib_profile_admits_33k_200k_3m_and_names_the_size_past_it(self):
        created = self.op("init", "--max-article-octets", str(MIB4), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.start_owner(self.image)
        rows = self.post_and_reread([33792, 204800, 3145728, MIB4 + 1])
        self.stop(owner)
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

    def stop_serving(self, owner):
        owner.send_signal(signal.SIGTERM)
        code = owner.wait(timeout=60)
        self.assertEqual(code, EXIT_OK, b"".join(owner.stderr.readlines()[-20:])
                         .decode("utf-8", "replace"))

    def references(self, i):
        ids, total, j = [], 0, 0
        while total < self.OVER_REFERENCES:
            mid = "<r{}-{}@example.invalid>".format(i, j)
            ids.append(mid)
            total += len(mid) + 3
            j += 1
        return b"References: " + "\r\n ".join(ids).encode("ascii") + b"\r\n"

    def test_article_of_1_2_3_mib_and_a_4_mb_over_leave_the_owner_serving(self):
        created = self.op("init", "--max-article-octets", str(MIB4), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.start_owner(self.image)
        rows = self.post_and_reread([1048576, 2097152, 3145728])
        for n in (1048576, 2097152, 3145728):
            self.assertTrue(rows[n][0].startswith("240"), rows)
            self.assertTrue(rows[n][1], "the ARTICLE of {} octets was not served identical".format(n))
        self.assertIsNone(owner.poll(), "the owner stopped serving the large ARTICLEs")
        with socket.create_connection(("127.0.0.1", self.port), timeout=300) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            for i in range(self.OVER_ARTICLES):
                stream.write(b"POST\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"340"))
                stream.write(b"From: over@example.invalid\r\nNewsgroups: fn.test\r\n"
                             b"Subject: large over\r\nMessage-ID: <over-" +
                             str(i).encode("ascii") + b"@example.invalid>\r\n" +
                             self.references(i) + b"\r\nbody\r\n.\r\n")
                stream.flush()
                reply = stream.readline()
                self.assertTrue(reply.startswith(b"240"), (i, reply))
            stream.write(b"GROUP fn.test\r\n")
            stream.flush()
            words = stream.readline().split()
            self.assertEqual(words[0], b"211", words)
            stream.write(b"OVER " + words[2] + b"-" + words[3] + b"\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"224"))
            lines, octets = 0, 0
            while True:
                line = stream.readline()
                self.assertTrue(line, "the OVER reply ended without its terminator")
                if line == b".\r\n":
                    break
                lines += 1
                octets += len(line)
        self.assertEqual(lines, 3 + self.OVER_ARTICLES)
        self.assertGreater(octets, 3 * 1024 * 1024)
        self.assertIsNone(owner.poll(), "the owner stopped serving the large OVER")
        client = NntpClient(self.port)
        try:
            client.stream.write(b"STAT <over-0@example.invalid>\r\n")
            client.stream.flush()
            self.assertTrue(client.stream.readline().startswith(b"223"))
        finally:
            client.close()
        self.stop_serving(owner)


@unittest.skipUnless(FORMAT7_IMAGE, "FN_FORMAT7_IMAGE names a pre-D27 image")
class DeployRehearsalTests(JoinFixture):
    """The offline 7-to-8 step for the deployed node, on a scratch store."""

    def old(self, *words):
        return self.operator(*words, image=FORMAT7_IMAGE)

    def test_step_rollback_step_post_3_mib_restart(self):
        created = self.old("init", "--profile", "scale", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertEqual(self.frame(), FORMAT7_SCALE_FRAME)
        owner = self.start_owner(FORMAT7_IMAGE)
        self.assertEqual(self.post_many(["<seed@example.invalid>"]), ["240 article received OK"])
        self.stop(owner)
        # Step 2: keep config.json (the rollback) with the unit stopped.
        kept = self.root / "config.json.format-7"
        shutil.copyfile(self.store / "config.json", kept)
        # Step 3: the new image opens the format-7 store under its translation.
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        self.assertIn(b"profile format=7", status.stdout)
        print(status.stdout.decode(), flush=True)
        # Step 4 with the article field alone is refused by the relation: the
        # translated R (17,138,486) does not hold a 4 MiB article's record.
        alone = self.op("store", "upgrade-profile", "--max-article-octets", str(MIB4))
        self.assertEqual(alone.returncode, EXIT_REFUSED, alone.stderr.decode())
        self.assertIn(b"max-record-octets-below-the-article-record", alone.stderr)
        self.assertEqual(self.frame(), FORMAT7_SCALE_FRAME)
        step = ("store", "upgrade-profile", "--max-article-octets", str(MIB4),
                "--max-record-octets", "33554432")
        upgraded = self.op(*step)
        self.assertEqual(upgraded.returncode, EXIT_OK, upgraded.stderr.decode())
        print(upgraded.stdout.decode(), flush=True)
        self.assertIn(b"transactions-used=1 transactions-budget=4096 previous-budget=4096",
                      upgraded.stdout)
        line = self.profile_line()
        self.assertEqual((line["format"], line["max-article-octets"],
                          line["max-record-octets"]), (8, MIB4, 33554432))
        # Rollback: the old image refuses format 8; the kept frame restores it.
        refused = self.old("status")
        self.assertNotEqual(refused.returncode, EXIT_OK)
        shutil.copyfile(kept, self.store / "config.json")
        self.assertEqual(self.frame(), FORMAT7_SCALE_FRAME)
        reopened = self.old("status")
        self.assertEqual(reopened.returncode, EXIT_OK, reopened.stderr.decode())
        # Step 4 again, then serve.
        self.assertEqual(self.op(*step).returncode, EXIT_OK)
        owner = self.start_owner(self.image)
        rows = self.post_and_reread([3145728])
        self.stop(owner)
        self.assertTrue(rows[3145728][0].startswith("240"), rows)
        self.assertTrue(rows[3145728][1])
        # Restart: still open, the 3 MiB article rereads, the next POST lands.
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        owner = self.start_owner(self.image)
        self.assertTrue(self.reread("<join-3145728@example.invalid>", 3145728))
        self.assertEqual(self.post_many(["<after@example.invalid>"]), ["240 article received OK"])
        self.stop(owner)
        self.assertEqual(self.headroom()["transactions-used"], 3)

    profile_line = __import__("tests.test_native_profile_upgrade",
                              fromlist=["OperatorFieldsTests"]).OperatorFieldsTests.profile_line


if __name__ == "__main__":
    unittest.main()
