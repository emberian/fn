#!/usr/bin/env python3
"""Mini M4: `fn identity CONTROL' asks the running owner who this store is.

The owner answers FNCT kind 25 (books/store-identity.lisp over the exported
wire grammar), and the client prints ACL2's line: the format word, the
genesis node identity, schema and profile digests, the consumer arm, both
image revisions and the digest of specs/wire-grammar.json.  Before a
consumer bootstrap the arm is `unbootstrapped' (never an empty field);
after `consumer bootstrap' it carries the history id and incarnation.  The
grammar digest is BLAKE3 of the committed file, so Mini pins the file it
decodes with by this one command.  Refuted: an unknown verb, an empty
history or incarnation, a grammar digest that is not the file's, a reply
without the genesis fields, a usage error that exits 0, or an answer with
no owner running.
"""

from __future__ import annotations

import re
import sys
import unittest

from tests.native_harness import EXIT, ROOT, Node, native_image, requires

sys.path.insert(0, str(ROOT / "tools"))
import blake3_ref  # noqa: E402

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
LINE = re.compile(
    r"^fn-store-identity-v1 format=(\S+) node=([0-9a-f]{64}) schema=([0-9a-f]{64})"
    r" profile=([0-9a-f]{64}) consumer=(unbootstrapped|bootstrapped"
    r" history=[0-9a-f]{2,128} incarnation=[0-9a-f]{2,128})"
    r" created-revision=(\S+) running-revision=(\S+) grammar=([0-9a-f]{64})$")


@requires(IMAGE)
class StoreIdentity(unittest.TestCase):
    def setUp(self) -> None:
        self.node = Node(self, IMAGE)
        self.node.store("init", "fn.test", expect=EXIT.OK)

    def identity(self, *words: str, expect: int) -> str:
        result = self.node.invoke("identity", *words, expect=expect)
        return result.stdout.decode("utf-8", "replace").strip()

    def test_identity_before_and_after_bootstrap(self) -> None:
        self.node.start()
        control = str(self.node.control)
        before = LINE.match(self.identity(control, expect=EXIT.OK))
        self.assertIsNotNone(before)
        self.assertEqual(before.group(5), "unbootstrapped")
        grammar = blake3_ref.blake3((ROOT / "specs" / "wire-grammar.json").read_bytes()).hex()
        self.assertEqual(before.group(8), grammar)
        self.assertNotEqual(before.group(2), "00" * 32)

        result = self.node.invoke("consumer", "bootstrap", control, expect=EXIT.OK)
        self.assertIn(b"consumer accepted", result.stdout)
        after = LINE.match(self.identity(control, expect=EXIT.OK))
        self.assertIsNotNone(after)
        self.assertTrue(after.group(5).startswith("bootstrapped history="))
        # The genesis fields and the running image are the same store's.
        for field in (1, 2, 3, 4, 6, 7, 8):
            self.assertEqual(before.group(field), after.group(field))
        self.node.stop()

        # No owner: no identity line, and not an acceptance.
        offline = self.node.invoke("identity", control)
        self.assertNotEqual(offline.returncode, EXIT.OK)
        self.assertNotIn(b"fn-store-identity-v1 ", offline.stdout)

    def test_usage(self) -> None:
        self.identity("relative/control", expect=EXIT.USAGE)
        self.identity("/a", "/b", expect=EXIT.USAGE)
        self.assertIn("usage: fn identity CONTROL", self.identity("help", expect=EXIT.OK))


if __name__ == "__main__":
    unittest.main()
