"""A known abort of a staged identity, consumer or topic record, natively.

Lane host-decisions (PRF-299) made the Store's known abort resolve every
staged deferred record (fn-sn-known-abort; fn-owner-known-abort answers
:aborted, lane host-decisions-2's fn-pout-known-abort), where before a staged
identity, consumer or topic record answered :fault and the owner fenced for
recovery although nothing had been written.  This module injects the known
refusal on the served owner's publication of each kind
(FN_NATIVE_POST_FAULT=record-prepublish:refuse, host/native/io.lisp
fnn-publish: a refusal before the record's first write, developer image
only) and checks, per kind:

* the verb is REFUSED (exit 1), never uncertain (3) or a fault (4);
* the owner is not fenced: it keeps serving (a second refused verb is again
  a refusal, not "fenced pending recovery") and stops cleanly (exit 0);
* nothing was committed: the record log's committed history is unchanged;
* after a restart without the fault, the same verb commits (exit 0) and the
  history grows by exactly that record.
"""
import unittest

from tests.native_harness import (
    EXIT_OK, EXIT_REFUSED, ROOT, Node, environment, native_image, requires)
from tests import native_log_observation

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
FIXTURES = ROOT / "tests" / "fixtures" / "topic-history"
FAULT = "record-prepublish:refuse"


@requires(IMAGE)
class NativeKnownAbortTest(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.root, self.store, self.control = self.node.root, self.node.store_path, self.node.control
        init = self.node.store("init", "fn.test")
        self.assertEqual(init.returncode, 0, self.text(init))
        self.principal = self.root / "principal.bin"
        self.ed_public = self.root / "ed-public.bin"
        self.principal.write_bytes(bytes([85]) * 32)
        self.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ml_public = FIXTURES / "ml-dsa-65-test-public.pem"

    @staticmethod
    def text(result):
        return (result.stdout + result.stderr).decode("utf-8", "replace")

    def invoke(self, *words):
        return self.node.invoke(*words, timeout=120)

    def start_owner(self, fault=None):
        return self.node.start(env={"FN_NATIVE_POST_FAULT": fault} if fault else None,
                               timeout=120)

    def stop_owner(self, proc):
        self.node.stop(process=proc)
        return proc.stderr.since(0).decode("utf-8", "replace")

    def history(self):
        return native_log_observation.committed_history(IMAGE, self.store,
                                                        env=environment(), cwd=ROOT)

    def verb(self, kind):
        if kind == "topic":
            return ("topic", "install", self.control)
        if kind == "consumer":
            return ("consumer", "bootstrap", self.control)
        return ("hybrid-enroll", self.control, "1", self.principal,
                self.ed_public, self.ml_public)

    def check_known_abort(self, kind):
        before = self.history()
        owner = self.start_owner(FAULT)
        refused = self.invoke(*self.verb(kind))
        self.assertEqual(refused.returncode, EXIT_REFUSED, self.text(refused))
        self.assertIsNone(owner.poll(), "the owner stopped after a known abort")
        # Not fenced: the next publication is refused the same way, by the
        # injected refusal, not by a fence pending recovery.
        again = self.invoke(*self.verb(kind))
        self.assertEqual(again.returncode, EXIT_REFUSED, self.text(again))
        self.assertNotIn("fenced", self.text(again))
        diagnostic = self.stop_owner(owner)
        self.assertNotIn("indeterminate", diagnostic)
        self.assertEqual(self.history(), before, "a known abort committed a record")
        # Without the fault the same verb commits exactly one record.
        owner = self.start_owner()
        committed = self.invoke(*self.verb(kind))
        self.assertEqual(committed.returncode, EXIT_OK, self.text(committed))
        self.stop_owner(owner)
        after = self.history()
        self.assertEqual(len(after), len(before) + 1)

    def test_topic_known_abort(self):
        self.check_known_abort("topic")

    def test_consumer_known_abort(self):
        self.check_known_abort("consumer")

    def test_identity_known_abort(self):
        self.check_known_abort("identity")


if __name__ == "__main__":
    unittest.main()
