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


# PKT-471 (the coordinator's decision of 2026-09-26): a store SAVED before
# PKT-467 with R in the window above CEILING is refused by name at every open
# (books/store-profile-open.lisp fn-spo-config-open, the open
# host/native/io.lisp fnn-metadata-config-decode calls; keystone
# fn-spo-open-of-a-saved-format-8-profile-opens-or-refuses-by-name), and
# `store upgrade-profile --max-record-octets CEILING` is its one repair
# (fn-spo-repair-verdict; fn-spo-repair-admits-exactly-the-lowering-to-the-width).
#
# The witness config.json is written BY HAND, never taken from a real store:
# the octets the format-8 encoder wrote under the relation before PKT-467 for
# the scale preset's fields with R = H = 4,294,967,295 (the codec's u32), the
# same constant tests/acl2/store-profile-open-tests.lisp checks is
# (fn-spo-saved-frame *spot-window*).  Its last 32 octets are the SHA-256 of
# the rest (the FNSM trailer).
WINDOW_FRAME = bytes.fromhex(
    "464e534d010100000094000a666e2d73746f72652d38001e666e2d73746f7265"
    "2d616c6c6f636174696f6e2d66726f6e746965722d3200000000000010000000"
    "0000ffffffff00000000ffffffff0000000000008000000000000000ffff0000"
    "0000000001000000000000001000000000000010000000000000001000000000"
    "00000010000000000000001000000000000000100000000000000000000030f0"
    "f366d0c3978954589a8e03e2160450ce2cc20435273838484922cb8e9d12")
LINE = ("profile record bound exceeds the poll reply width: "
        "run store upgrade-profile --max-record-octets 4294966940")


class ProfileOpenRefusalSourceTests(unittest.TestCase):
    def test_the_witness_frame_is_a_sealed_format_8_frame(self):
        self.assertEqual(len(WINDOW_FRAME), 190)
        self.assertEqual(WINDOW_FRAME[:4], b"FNSM")
        self.assertEqual(hashlib.sha256(WINDOW_FRAME[:-32]).digest(), WINDOW_FRAME[-32:])
        book = (ROOT / "tests" / "acl2" / "store-profile-open-tests.lisp").read_text(encoding="ascii")
        octets = book.split("(defconst *spot-window-octets*", 1)[1].split("))", 1)[0]
        self.assertEqual(bytes(int(w) for w in octets.replace("'(", " ").split()), WINDOW_FRAME)


class ProfileOpenRefusalTests(ControlReplyFitTests):
    def files(self):
        return {str(p.relative_to(self.store)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(self.store.rglob("*"))
                if p.is_file() and p.name != "writer.lock"}

    def run_owner(self):
        import subprocess
        return subprocess.run([str(self.image), "--fn", "operator", str(self.config), "run"],
                              cwd=ROOT, env=verbs.environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=180, check=False)

    def assert_named(self, result, what):
        out = (result.stdout + result.stderr).decode("utf-8", "replace")
        print("$", what, "->", result.returncode, "\n" + out.strip(), flush=True)
        self.assertEqual(result.returncode, EXIT_REFUSED, out)
        self.assertIn(LINE, out)
        self.assertNotIn("ACL2 rejected durable configuration frame", out)

    def test_a_store_saved_in_the_window_is_refused_by_name_at_every_open_then_repaired(self):
        created = self.op("init", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.serves("window")
        (self.store / "config.json").write_bytes(WINDOW_FRAME)
        before = self.files()

        self.assert_named(self.op("status"), "operator status")
        self.assert_named(self.op("store", "recover"), "operator store recover")
        self.assert_named(self.op("store", "checkpoint"), "operator store checkpoint")
        self.assert_named(self.op("health"), "operator health")
        self.assert_named(self.run_owner(), "operator run")
        self.assert_named(self.store_cli("recover"), "store recover")
        self.assert_named(self.store_cli("inspect", "<fit-window@example.invalid>"),
                          "store inspect")
        self.assert_named(self.store_cli("checkpoint"), "store checkpoint")
        # Refused, never mutated.
        self.assertEqual(self.files(), before)

        # Any other target is refused by name and writes nothing.
        other = self.op("store", "upgrade-profile", "--max-record-octets", str(CEILING - 1))
        print(other.stderr.decode(errors="replace"), flush=True)
        self.assertEqual(other.returncode, EXIT_REFUSED, other.stderr.decode())
        self.assertIn(b"store profile upgrade refused: "
                      b"repair-lowers-max-record-octets-to-the-poll-reply-only", other.stderr)
        self.assertEqual(self.files(), before)

        repaired = self.op("store", "upgrade-profile", "--max-record-octets", str(CEILING))
        print(repaired.stdout.decode(errors="replace"), repaired.stderr.decode(errors="replace"),
              flush=True)
        self.assertEqual(repaired.returncode, EXIT_OK, repaired.stderr.decode())
        self.assertIn(b"repaired profile=max-record-octets transactions-used=1", repaired.stdout)
        profile = self.profile_line()
        self.assertEqual(profile["max-record-octets"], CEILING)
        self.assertEqual(profile["max-history-octets"], 4294967295)
        self.assertEqual(profile["max-transactions"], 4096)
        for name, digest in before.items():
            if name != "config.json" and name.startswith("transactions"):
                self.assertEqual(self.files()[name], digest)
        self.serves("repaired")


if __name__ == "__main__":
    unittest.main()
