"""`operator post' carries an article up to the profile's A (D27, PKT-008/009).

Before the per-schema frame blob width, the FNCT request's article field was a
`:blob' of 131 072 octets, so `fn operator CONFIG post' could not submit an
article above it whatever the profile allowed, and with hybrid control built
in the owner read a control frame of at most 65 578 octets.  Under a profile
whose article field A is 300 000 (above the 262 708-octet command frame, so
the owner's read bound is the profile's), this test submits over the control
socket:

* 131 073 and 290 000 octets: accepted (exit 0), each re-read over NNTP with
  the posted body as the stored article's suffix (290 000 is above the
  command frame, so only a read bound taken from A admits it);
* 300 001 octets: refused by name, ARTICLE-EXCEEDS-PROFILE-BOUND (exit 1);
* PKT-182: 64 MiB past A (far past the owner's read bound, so the owner
  answers refused and stops reading while the client is still writing):
  refused (exit 1), never uncertain (exit 3), and nothing stored.

A bounds the injected article: the owner adds Path, Injection-Date and
Injection-Info, so a submission of exactly A octets is refused by name too.

Run on hbox with FN_NATIVE_HOST naming the image under test
(planning/evidence/bounds-blob-2026-09-25.md).
"""
import unittest

from tests.native_harness import EXIT_OK, EXIT_REFUSED
from tests.test_native_bounds_join import JoinFixture, article

A = 300000
BELOW_A = 290000


class OperatorPostAboveTheOldBlobTests(JoinFixture):
    def test_operator_post_carries_up_to_a_and_names_one_octet_past(self):
        created = self.op("init", "--max-article-octets", str(A), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start(image=self.image)
        served = {}
        try:
            for n in (131073, BELOW_A, A + 1):
                msgid = "<blob-{}@example.invalid>".format(n)
                path = self.root / "blob-{}".format(n)
                path.write_bytes(article(msgid, n))
                served[n] = self.op("post", "--message-id", msgid, "--payload",
                                    str(path), "--group", "fn.test")
                print("operator post", n, served[n].returncode,
                      served[n].stdout.decode().strip(),
                      served[n].stderr.decode().strip(), flush=True)
            reread = {n: self.reread("<blob-{}@example.invalid>".format(n), n)
                      for n in (131073, BELOW_A)}
            print("reread", reread, flush=True)
        finally:
            self.node.stop()
        for n in (131073, BELOW_A):
            self.assertEqual(served[n].returncode, EXIT_OK, served[n].stderr.decode())
            self.assertTrue(reread[n], "{} did not reread identical".format(n))
        self.assertEqual(served[A + 1].returncode, EXIT_REFUSED,
                         served[A + 1].stderr.decode())
        self.assertIn(b"ARTICLE-EXCEEDS-PROFILE-BOUND", served[A + 1].stderr)
        self.assertEqual(self.headroom()["transactions-used"], 2)

    def test_a_frame_far_past_the_read_bound_is_refused_not_uncertain(self):
        created = self.op("init", "--max-article-octets", str(A), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start(image=self.image)
        n = A + 64 * 1024 * 1024
        msgid = "<overbound-{}@example.invalid>".format(n)
        path = self.root / "overbound"
        try:
            path.write_bytes(article(msgid, n))
            posted = self.op("post", "--message-id", msgid, "--payload",
                             str(path), "--group", "fn.test")
            print("operator post", n, posted.returncode,
                  posted.stdout.decode().strip(), posted.stderr.decode().strip(),
                  flush=True)
        finally:
            path.unlink()
            self.node.stop()
        self.assertEqual(posted.returncode, EXIT_REFUSED, posted.stderr.decode())
        self.assertEqual(self.headroom()["transactions-used"], 0)


    unittest.main()
