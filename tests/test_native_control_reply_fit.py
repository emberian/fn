"""Control replies that cannot carry their value refuse by name (control-reply-fit).

PKT-467 (the coordinator's ruling: D27's "profile validation, representation
and format evolution must agree"): a store profile whose record bound R the
consumer poll reply cannot carry is refused by name at `init` (and at
`store import`, which resolves the same relation), rather than admitted and discovered at the first
oversized article.  The ceiling is `*fn-stxa-max-octets*` (4,294,966,940:
the Store frame's u32 less the kind-6 reply's 9 header and 346 cursor
octets); the arm is books/byte-store-frame.lisp `fn-bs-profile-invalid-reason`
`:max-record-octets-above-the-poll-reply`, the keystone
`fn-bs-profile-valid-record-fits-a-poll-reply`.

The witnesses, on the developer image:

* `init` one octet past the ceiling (H raised with it) is refused by that
  name, exit 1, and writes no config.json; at the ceiling it is written and
  the store serves: the owner starts and takes a POST.

The live-status (FNLS) row's named refusal
(`fn-nls-page-refuses-exactly-past-the-total-width`) needs a report of 2^32
octets and is not driven natively; its host carriage is checked statically.
Run on hbox with FN_NATIVE_HOST naming the image under test.
"""
import hashlib
import unittest

from tests import test_native_operator_verbs as verbs
# The harness stores' init budget (tools/native_env.py): init refuses a
# store without FN_INIT_BUDGET_MB on a large machine (batch AZ, 2026-09-28).
from tools.native_env import harness_store_env  # noqa: E402
from tests.native_profile_fixture import ProfileFixture as ProfileUpgradeFixture

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


class ControlReplyFitFixture(ProfileUpgradeFixture):
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


class ControlReplyFitTests(ControlReplyFitFixture):
    def test_init_refuses_r_past_the_poll_reply_by_name_and_admits_the_ceiling(self):
        # The reply-fit refusal is a property of the profile, not of this
        # machine: the init budget (books/heap-reservation.lisp) is set far
        # above the ceiling profile's reservation (about 110 TB) so that the
        # budget check, which init runs first, admits both and the named
        # refusal is the one under test (batch AZ, 2026-09-28).
        budget = harness_store_env(dict(verbs.environment(), FN_INIT_BUDGET_MB="200000000"))
        refused = self.op("init", "--max-record-octets", str(PAST),
                          "--max-history-octets", str(PAST), "fn.test", env=budget)
        print(refused.stderr.decode(errors="replace"), flush=True)
        self.assertEqual(refused.returncode, EXIT_REFUSED, refused.stderr.decode())
        # The operator's result line prints the reason word upper-cased.
        self.assertIn(NAME, refused.stderr.lower())
        self.assertIsNone(self.config_frame())
        created = self.op("init", "--max-record-octets", str(CEILING),
                          "--max-history-octets", str(CEILING), "fn.test", env=budget)
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertEqual(self.profile_line()["max-record-octets"], CEILING)
        self.serves("init")


if __name__ == "__main__":
    unittest.main()
