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
* the old-client case: an image from before :conflict (FN_OLD_NATIVE_HOST)
  posting the conflicting source reads the new word as undecodable after
  submission, so it answers uncertain (3) -- the documented reason clients
  are upgraded with the node (docs/agents.md).
"""
import os
from pathlib import Path
import re
import signal
import socket
import subprocess
import time
import unittest

try:
    from tests import test_native_operator_verbs as verbs
except ImportError:
    import test_native_operator_verbs as verbs

DEVELOPER, IMAGE, ROOT = verbs.DEVELOPER, verbs.IMAGE, verbs.ROOT
environment, executable, free_port = verbs.environment, verbs.executable, verbs.free_port

# specs/host.md "CLI exit codes": one code per class.
ACCEPTED, REFUSED, FENCED, FAULT, USAGE, INTERRUPTED, NOT_CONNECTED = 0, 1, 3, 4, 5, 6, 7
OLD = Path(os.environ["FN_OLD_NATIVE_HOST"]) if os.environ.get("FN_OLD_NATIVE_HOST") else None


def run(*argv, image=None, timeout=180):
    return subprocess.run([str(image or IMAGE), "--fn", *map(str, argv)],
                          cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=False)


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


@unittest.skipUnless(executable(IMAGE) and executable(DEVELOPER),
                     "build/fn-host and build/fn-host-developer are required")
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
        empty = self.root / "empty.toml"
        empty.write_text('[store]\npath = "{}"\n'.format(self.root / "never"), encoding="ascii")
        absent = subprocess.run([str(IMAGE), "--fn", "operator", str(empty), "status"],
                                cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=180, check=False)
        self.expect(absent, REFUSED, "refused operator status NO-STORE", "run: fn operator")
        (self.store / "allocation-frontier.json").write_bytes(b"not json\n")
        self.expect(self.operator("status"), FAULT)

    # -- store ------------------------------------------------------------
    def test_store_family(self):
        self.expect(run("store", self.store, "status", image=DEVELOPER), ACCEPTED)
        self.expect(run("store", self.store, "inspect", "<absent@example.invalid>",
                        image=DEVELOPER), REFUSED)
        self.expect(run("store", self.store, "bogus", image=DEVELOPER), USAGE)
        self.expect(run("store", self.root / "nowhere", "status", image=DEVELOPER), FAULT)
        payload = self.root / "fenced.eml"
        payload.write_bytes(self.article("<outcome-fenced@example.invalid>"))
        self.expect(run("store", self.store, "post", "<outcome-fenced@example.invalid>",
                        payload, "-", "postpublish", "fn.test", image=DEVELOPER), FENCED)

    # -- control: the D25 conflict word over the owner's socket -------------
    def conflict_case(self, client_image, expected_code, *words):
        owner = self.start_owner(IMAGE)
        message_id = "<outcome-conflict@example.invalid>"
        self.expect(self.post(message_id), ACCEPTED, "accepted operator post")
        self.expect(self.post(message_id), ACCEPTED, "DUPLICATE")
        changed = self.root / "changed.eml"
        changed.write_bytes(self.article(message_id).replace(b"exact payload", b"changed payload"))
        answer = self.operator("post", "--message-id", message_id, "--payload", str(changed),
                               "--group", "fn.test", image=client_image, timeout=120)
        text = self.expect(answer, expected_code, *words)
        owner.send_signal(signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=60), ACCEPTED,
                         owner.stderr.read().decode("utf-8", "replace"))
        return text

    def test_control_conflict_is_a_refusal_named_conflict(self):
        self.conflict_case(IMAGE, REFUSED, "refused operator post CONFLICT")

    @unittest.skipUnless(OLD and executable(OLD), "FN_OLD_NATIVE_HOST names an image before :conflict")
    def test_an_old_client_reads_conflict_as_uncertain(self):
        self.conflict_case(OLD, FENCED, "uncertain operator post")

    # -- bp ---------------------------------------------------------------
    def test_bp_not_connected_and_the_clockless_decode(self):
        journal = self.root / "bp-journal"
        adu = self.root / "adu.txt"
        adu.write_bytes(b"an application data unit\n")
        port = free_port()
        wall = str(int((time.time() - 946684800) * 1000))
        sent = run("bp", "send", "127.0.0.1", port, adu, journal, "-", "-", "-", "-",
                   "-", "-", "-", wall, "0")
        self.expect(sent, NOT_CONNECTED)
        wires = sorted(journal.rglob("*.wire"))
        self.assertTrue(wires, "bp send kept no authored wire under %s" % journal)
        decoded = run("bp", "decode", wires[0])
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


if __name__ == "__main__":
    unittest.main()
