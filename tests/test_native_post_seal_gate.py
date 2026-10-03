"""A POST the catalog would refuse after the seal seals nothing (lane
arena-forget; books/catalog-may-seal.lisp).

MUTATION witness (labelled): FN_NATIVE_TEST_CAT_SEAL_REFUSE makes the
catalog gate answer no, as a held index-writer ticket or a pending catalog
commit does.  Two refused POSTs report the same arena count (before the
gate each left one unnamed sealed payload); the node still serves the
articles it held.
"""
import re
import unittest

from tests.native_harness import Client, native_image, requires
from tests import test_native_expiry as expiry

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(IMAGE)
class NativePostSealGate(unittest.TestCase):
    image = IMAGE
    setUp = expiry.ExpiryMixin.setUp
    node = expiry.ExpiryMixin.node
    post_all = expiry.ExpiryMixin.post_all
    owner_lines = expiry.ExpiryMixin.owner_lines

    def test_refused_gate_seals_nothing(self):
        node = self.node("gate")
        self.post_all(node, [("n0", expiry.GROUP, None, 0)])
        owner = node.start(timeout=600, env={"FN_NATIVE_TEST_CAT_SEAL_REFUSE": "1"})
        try:
            for tag in ("g1", "g2"):
                c = Client(node.port, timeout=300, greeting=None)
                try:
                    first, final = c.post(expiry.article(tag, expiry.GROUP, None))
                    self.assertFalse((final or first).startswith(b"240"), (first, final))
                except (ConnectionError, OSError):
                    pass
                finally:
                    c.close(False)
            pattern = re.compile(rb"POST seal-gate refused arena=(\d+)")
            lines = self.owner_lines(owner, pattern, 2)
            self.assertEqual(len(lines), 2, owner.stderr.since(0)[-3000:])
            counts = {int(pattern.search(l).group(1)) for l in lines}
            self.assertEqual(len(counts), 1, lines)
        finally:
            node.stop(expect=None, grace=300)
