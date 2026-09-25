"""`operator post' carries an article up to the profile's A (D27, PKT-008/009).

Before the per-schema frame blob width, the FNCT request's article field was a
`:blob' of 131 072 octets, so `fn operator CONFIG post' could not submit an
article above it whatever the profile allowed, and with hybrid control built
in the owner read a control frame of at most 65 578 octets.  Under a profile
whose article field A is 300 000 (above the 262 708-octet command frame, so
the owner's read bound is the profile's), this test submits over the control
socket:

* 131 073 and 300 000 octets: accepted (exit 0), each re-read over NNTP with
  the posted body as the stored article's suffix;
* 300 001 octets: refused by name, ARTICLE-EXCEEDS-PROFILE-BOUND (exit 1).

Run on hbox with FN_NATIVE_HOST naming the image under test
(planning/evidence/bounds-blob-2026-09-25.md).
"""
import unittest

from tests import test_native_operator_verbs as verbs
from tests.test_native_bounds_join import JoinFixture, article

EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED
A = 300000


class OperatorPostAboveTheOldBlobTests(JoinFixture):
    def test_operator_post_carries_up_to_a_and_names_one_octet_past(self):
        created = self.op("init", "--max-article-octets", str(A), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.start_owner(self.image)
        served = {}
        try:
            for n in (131073, A, A + 1):
                msgid = "<blob-{}@example.invalid>".format(n)
                path = self.root / "blob-{}".format(n)
                path.write_bytes(article(msgid, n))
                served[n] = self.op("post", "--message-id", msgid, "--payload",
                                    str(path), "--group", "fn.test")
                print("operator post", n, served[n].returncode,
                      served[n].stdout.decode().strip(),
                      served[n].stderr.decode().strip(), flush=True)
            reread = {n: self.reread("<blob-{}@example.invalid>".format(n), n)
                      for n in (131073, A)}
            print("reread", reread, flush=True)
        finally:
            self.stop(owner)
        for n in (131073, A):
            self.assertEqual(served[n].returncode, EXIT_OK, served[n].stderr.decode())
            self.assertTrue(reread[n], "{} did not reread identical".format(n))
        self.assertEqual(served[A + 1].returncode, EXIT_REFUSED,
                         served[A + 1].stderr.decode())
        self.assertIn(b"ARTICLE-EXCEEDS-PROFILE-BOUND", served[A + 1].stderr)
        self.assertEqual(self.headroom()["transactions-used"], 2)


if __name__ == "__main__":
    unittest.main()
