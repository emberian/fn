"""Row S10 (lane operability-2): the operator's refusals name their reason.

* An operator `post' the injection admits and the Store refuses (here: a
  full development store) answered `refused operator post REFUSED' and
  logged `refused post path=control message-id=...' with no reason word.
  Now the reply carries the Store's word and the line ` reason=WORD'
  (books/owner-control-post-reason.lisp, KEYSTONE
  fn-ocpr-line-names-the-reason-exactly-when-refused).
* `policy set bogus-key 1' and `policy set exposure-connections abc'
  answered the usage line; now they are refused by name
  (unknown-policy-key, policy-value-not-a-number) with what it would take
  (books/native-admin.lisp fn-native-admin-counted-policy-keyp).

Run with a native image (tests.native_harness): FN_NATIVE_IMAGE=... python3
-m unittest tests.test_native_operator_refusals
"""

import re
import unittest

from tests import test_native_checkpoint_auto as auto
from tests.native_harness import EXIT_OK, article

CONTROL_REFUSED = re.compile(rb"refused post path=control message-id=(<[^>]+>) .*reason=([a-z0-9-]+)")


class OperatorRefusalTests(auto.AutoCheckpointFixture):

    def test_a_post_the_store_refuses_names_its_reason_and_policy_set_refuses_by_name(self):
        created = self.op("init", "--profile", "development", "--max-transactions", "4", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        owner = self.node.start()
        self.ids = self.post_batch(0, 2)
        refused = None
        for n in range(6):
            control_id = "<op-refusal-{}@example.invalid>".format(n)
            source = self.root / "control-article-{}".format(n)
            source.write_bytes(article(control_id, subject="operator refusal"))
            result = self.op("post", "--message-id", control_id, "--payload", str(source),
                             "--group", "fn.test")
            if result.returncode != 0:
                refused = (control_id, result)
                break
        self.assertIsNotNone(refused, "the development store of 4 never filled")
        control_id, result = refused
        out = (result.stdout + result.stderr).decode("utf-8", "replace")
        # The reply names the Store's word, not the bare status.
        self.assertIn("refused operator post ", out)
        # `STATUS WORD': the bare `REFUSED' no longer stands alone.
        self.assertNotRegex(out, r"refused operator post REFUSED\s*$")
        self.assertRegex(out, r"refused operator post REFUSED [a-z0-9-]+")
        # The line names the same reason.
        line = self.owner_line(owner, CONTROL_REFUSED, deadline=60.0)
        self.assertIsNotNone(line, "no refused control post line with a reason")
        self.assertEqual(line.group(1).decode("ascii"), control_id)
        self.assertIn(line.group(2).decode("ascii"), out)
        # `policy set' refused by name, with what it would take.
        bogus = self.op("policy", "set", "bogus-key", "1")
        self.assertEqual(bogus.returncode, 1, bogus.stderr.decode())
        bogus_out = (bogus.stdout + bogus.stderr).decode("utf-8", "replace")
        self.assertIn("unknown-policy-key", bogus_out.lower())
        self.assertIn("no key by that name", bogus_out)
        self.assertNotIn("usage:", bogus_out)
        letters = self.op("policy", "set", "exposure-connections", "abc")
        self.assertEqual(letters.returncode, 1, letters.stderr.decode())
        letters_out = (letters.stdout + letters.stderr).decode("utf-8", "replace")
        self.assertIn("policy-value-not-a-number", letters_out.lower())
        self.assertIn("decimal count", letters_out)
        self.assertNotIn("usage:", letters_out)
        self.node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
