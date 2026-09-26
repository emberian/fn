"""Control replies that cannot carry their value refuse by name (control-reply-fit).

PKT-467 (the coordinator's ruling: D27's "profile validation, representation
and format evolution must agree"): a store profile whose record bound R the
consumer poll reply cannot carry is refused by name, at `init` and at
`store upgrade-profile`, rather than admitted and discovered at the first
oversized article.  The ceiling is `*fn-stxa-max-octets*` (4,294,966,940:
the Store frame's u32 less the kind-6 reply's 9 header and 346 cursor
octets); the arm is books/byte-store-frame.lisp `fn-bs-profile-invalid-reason`
`:max-record-octets-above-the-poll-reply`, the keystone
`fn-bs-profile-valid-record-fits-a-poll-reply`.

The witnesses, on the developer image:

* `init` one octet past the ceiling (H raised with it) is refused by that
  name, exit 1, and writes no config.json; at the ceiling it is written and
  the store serves: the owner starts and takes a POST;
* `store upgrade-profile` of a default store one octet past the ceiling is
  refused by that name, exit 1, the frame unchanged; to the ceiling it is an
  upgrade; the owner serves after both.

The live-status (FNLS) row's named refusal
(`fn-nls-page-refuses-exactly-past-the-total-width`) needs a report of 2^32
octets and is not driven natively; its host carriage is checked statically.
Run on hbox with FN_NATIVE_HOST naming the image under test.
"""
import hashlib
import unittest

from tests import test_native_operator_verbs as verbs
from tests.test_native_profile_upgrade import ProfileUpgradeFixture

ROOT = verbs.ROOT
EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED
CEILING = 4294966940          # *fn-stxa-max-octets*
PAST = CEILING + 1
NAME = b"max-record-octets-above-the-poll-reply"


class ControlReplyFitSourceTests(unittest.TestCase):
    def test_the_arm_and_the_named_live_status_refusal_are_carried(self):
        frame = (ROOT / "books" / "byte-store-frame.lisp").read_text(encoding="ascii")
        self.assertIn("((< *fn-stxa-max-octets* r)\n           :max-record-octets-above-the-poll-reply)",
                      frame)
        control = (ROOT / "host" / "native" / "control.lisp").read_text(encoding="ascii")
        self.assertIn("(:refused (return (if (rest step) step :refused)))", control)
        operator = (ROOT / "host" / "native" / "operator.lisp").read_text(encoding="ascii")
        self.assertEqual(operator.count('(fnn-refuse "live status refused: ~(~a~)" (second answer))'), 2)


class ControlReplyFitTests(ProfileUpgradeFixture):
    def profile_line(self):
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        for line in status.stdout.decode("ascii").splitlines():
            if line.startswith("profile "):
                return {k: int(v) if v.isdigit() else v
                        for k, v in (w.split("=", 1) for w in line.split()[1:])}
        self.fail(status.stdout.decode())

    def config_frame(self):
        path = self.store / "config.json"
        return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None

    def serves(self, tag):
        owner = self.start_owner(self.image)
        try:
            self.assertEqual(self.post_many(["<fit-{}@example.invalid>".format(tag)]),
                             ["240 article received OK"])
        finally:
            self.stop(owner)

    def test_init_refuses_r_past_the_poll_reply_by_name_and_admits_the_ceiling(self):
        refused = self.op("init", "--max-record-octets", str(PAST),
                          "--max-history-octets", str(PAST), "fn.test")
        print(refused.stderr.decode(errors="replace"), flush=True)
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        # The operator's result line prints the reason word upper-cased.
        self.assertIn(NAME, refused.stderr.lower())
        self.assertIsNone(self.config_frame())
        created = self.op("init", "--max-record-octets", str(CEILING),
                          "--max-history-octets", str(CEILING), "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertEqual(self.profile_line()["max-record-octets"], CEILING)
        self.serves("init")

    def test_upgrade_refuses_r_past_the_poll_reply_by_name_then_raises_to_it(self):
        created = self.op("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        before = self.config_frame()
        refused = self.op("store", "upgrade-profile", "--max-record-octets", str(PAST))
        print(refused.stderr.decode(errors="replace"), flush=True)
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        self.assertIn(b"store profile upgrade refused: " + NAME, refused.stderr)
        self.assertEqual(self.config_frame(), before)
        self.serves("refused")
        raised = self.op("store", "upgrade-profile", "--max-record-octets", str(CEILING))
        self.assertEqual(raised.returncode, EXIT_OK, raised.stderr.decode())
        self.assertEqual(self.profile_line()["max-record-octets"], CEILING)
        self.serves("raised")


if __name__ == "__main__":
    unittest.main()
