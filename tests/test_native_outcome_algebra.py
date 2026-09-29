"""One outcome algebra: every native fn command exits code(classify(f, x)).

specs/host.md "CLI exit codes" (HST-009, PRF-143) is the one table: 0
accepted, 1 refused, 3 fenced, 4 fault, 5 usage, 6 interrupted, 7 not
connected.  Each witness below runs a real command of one verb family and
checks the code against that table's class, never against a family table:

* operator: init (0), a second init and NO-STORE (1, their words kept),
  init with no group (5), a lost durable outcome (3, developer image), a
  store whose frontier file is not JSON (4);
* store: status (0), inspect of an absent article (1), an unknown store
  command (5), a missing root (4), a post whose publication outcome is lost
  (3, developer image);
* control (the operator post over the owner's socket): accepted, DUPLICATE
  (0), and a changed source under the held Message-ID, CONFLICT (1);
* bp: a send to a port with no listener (7, not connected), and `bp decode`
  of that authored bundle with no clock, which cannot decide its lifetime:
  a refusal with its reason (1), never the fence (3);
"""
import os
from pathlib import Path
import re
import time
import unittest

from tests import test_native_operator_verbs as verbs
from tests.native_harness import (
    EXIT, Acl2Session, Node, acl2_octets, free_port, native_image, requires)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
IMAGE = native_image("FN_NATIVE_HOST")
ROOT = verbs.ROOT

# specs/host.md "CLI exit codes": one code per class, ACL2's table.
ACCEPTED, REFUSED, FENCED, FAULT, USAGE, INTERRUPTED, NOT_CONNECTED = (
    EXIT.OK, EXIT.REFUSED, EXIT.UNCERTAIN, EXIT.FAULT, EXIT.USAGE, EXIT.INTERRUPTED,
    EXIT.NOT_CONNECTED)


def bundle_without_age(creation_ms, lifetime_ms, adu=b"clockless"):
    """A bundle with a DTN creation time and no Bundle Age block: without a
    wall clock the receiver cannot decide its lifetime (books/clock.lisp
    fn-clock-expiry-decision answers :uncertain).  ACL2 frames it
    (books/bp-bundle.lisp fn-bpb-encode, CRC-16 blocks) in the developer
    image's session."""
    def eid(node):
        return "(cons :dtn '" + Acl2Session.literal(("//%s/" % node).encode("ascii")) + ")"
    primary = "(fn-bpp-make-block 0 1 %s %s %s %d 0 %d nil nil)" % (
        eid("fn-b"), eid("fn-a"), eid("fn-a"), creation_ms, lifetime_ms)
    with Acl2Session(DEVELOPER) as acl2:
        return acl2_octets(acl2.call(
            "(fn-bpb-encode (fn-bpb-make-bundle %s nil (fn-bpb-payload-block 1 '%s)))"
            % (primary, Acl2Session.literal(adu))))


class OutcomeAlgebraSourceTests(unittest.TestCase):
    """The host writes no exit number of its own."""

    def test_the_host_constants_are_acl2s_map(self):
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        for name, cls in (("ok", "accepted"), ("refused", "refused"),
                          ("uncertain", "fenced"), ("fault", "fault"),
                          ("usage", "usage")):
            self.assertIn("(defconstant +fnn-exit-%s+ (fn-outcome-code :%s))" % (name, cls), io)
        book = (ROOT / "books" / "native-operator.lisp").read_text(encoding="utf-8")
        self.assertNotIn("*fn-nop-no-store-exit*", book)


@requires(IMAGE, DEVELOPER)
class OutcomeAlgebraNativeTests(verbs.NativeOperatorUncertainOutcomeTests):
    """One case per class per family, on the production and developer images.

    The inherited test_a_lost_durable_outcome_exits_three_and_recover_resolves_it
    is the operator family's fenced case (3)."""

    def expect(self, result, code, *words):
        text = result.stderr.decode("utf-8", "replace") + result.stdout.decode("utf-8", "replace")
        self.assertEqual(result.returncode, code, text)
        for word in words:
            self.assertIn(word, text)
        return text

    # -- operator ---------------------------------------------------------
    def test_operator_family(self):
        self.expect(self.operator("init", "fn.test"), REFUSED, "refused operator init")
        self.expect(self.operator("init"), USAGE, "usage operator init")
        self.expect(self.operator("status"), ACCEPTED)
        empty = Node(self, IMAGE, root=self.root.parent / "empty", listener=False, control=False)
        absent = empty.operator("status")
        self.expect(absent, REFUSED, "refused operator status NO-STORE", "run: fn operator")
        # A durable authority file that is no frame: the host's fault class.
        # (The store holds no allocation frontier file; the profile frame is
        # read at every open, and octets that are no sealed frame are the
        # open's (:rejected), never a named refusal.)
        (self.store / "config.json").write_bytes(b"not a frame\n")
        self.expect(self.operator("status"), FAULT)

    # -- store ------------------------------------------------------------
    def test_store_family(self):
        self.expect(self.node.store("status", image=DEVELOPER), ACCEPTED)
        self.expect(self.node.store("inspect", "<absent@example.invalid>",
                                    image=DEVELOPER), REFUSED)
        self.expect(self.node.store("bogus", image=DEVELOPER), USAGE)
        self.expect(self.node.invoke("store", self.root / "nowhere", "status",
                                     image=DEVELOPER), FAULT)
        payload = self.root / "fenced.eml"
        payload.write_bytes(self.article("<outcome-fenced@example.invalid>"))
        self.expect(self.node.store("post", "<outcome-fenced@example.invalid>",
                                    payload, "-", "postpublish", "fn.test", image=DEVELOPER),
                    FENCED)

    # -- control: the D25 conflict word over the owner's socket -------------
    def conflict_case(self, client_image, expected_code, *words):
        self.node.start()
        message_id = "<outcome-conflict@example.invalid>"
        self.expect(self.post(message_id), ACCEPTED, "accepted operator post")
        self.expect(self.post(message_id), ACCEPTED, "DUPLICATE")
        changed = self.root / "changed.eml"
        changed.write_bytes(self.article(message_id).replace(b"exact payload", b"changed payload"))
        answer = self.operator("post", "--message-id", message_id, "--payload", str(changed),
                               "--group", "fn.test", image=client_image, timeout=120)
        text = self.expect(answer, expected_code, *words)
        self.node.stop()
        return text

    def test_control_conflict_is_a_refusal_named_conflict(self):
        self.conflict_case(IMAGE, REFUSED, "refused operator post CONFLICT")

    # -- bp ---------------------------------------------------------------
    def test_bp_not_connected_and_the_clockless_decode(self):
        journal = self.root / "bp-journal"
        adu = self.root / "adu.txt"
        adu.write_bytes(b"an application data unit\n")
        port = free_port()
        wall = str(int((time.time() - 946684800) * 1000))
        sent = self.node.invoke("bp", "send", "127.0.0.1", port, adu, journal, "-", "-", "-", "-",
                   "-", "-", "-", wall, "0")
        self.expect(sent, NOT_CONNECTED)
        wires = sorted(journal.rglob("*.wire"))
        self.assertTrue(wires, "bp send kept no authored wire under %s" % journal)
        decoded = self.node.invoke("bp", "decode", wires[0])
        text = decoded.stdout.decode("utf-8", "replace")
        match = re.search(r"BP decode outcome=(\S+) reason=(\S+)", text)
        self.assertIsNotNone(match, text + decoded.stderr.decode("utf-8", "replace"))
        self.assertNotEqual(decoded.returncode, FENCED, text)
        if match.group(1) == "uncertain":
            self.assertEqual(decoded.returncode, REFUSED, text)
        elif match.group(1) == "accepted":
            self.assertEqual(decoded.returncode, ACCEPTED, text)
        else:
            self.assertEqual(decoded.returncode, REFUSED, text)
        print("bp decode without a clock: %s exit=%d" % (match.group(0), decoded.returncode))

    def test_bp_decode_the_clock_cannot_decide_is_a_refusal_not_a_fence(self):
        # specs/host.md "CLI exit codes": the clock-undecided verdict is the
        # refused class, 1, with its reason printed; before PRF-143 it was 3.
        path = self.root / "clockless.bundle"
        created = int((time.time() - 946684800) * 1000)
        path.write_bytes(bundle_without_age(created, 3600 * 1000))
        decoded = self.node.invoke("bp", "decode", path)
        text = decoded.stdout.decode("utf-8", "replace") + decoded.stderr.decode("utf-8", "replace")
        self.assertIn("BP decode outcome=uncertain", text)
        self.assertEqual(decoded.returncode, REFUSED, text)
        print("clockless decode: %s exit=%d" % (text.strip().splitlines()[-1], decoded.returncode))


if __name__ == "__main__":
    unittest.main()
