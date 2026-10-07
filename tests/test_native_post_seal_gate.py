"""A POST the catalog would refuse after the seal seals nothing (lane
arena-forget; books/catalog-may-seal.lisp).

MUTATION witness (labelled): FN_NATIVE_TEST_CAT_SEAL_REFUSE makes the
catalog gate answer no, as a held index-writer ticket or a pending catalog
commit does.  Two refused POSTs are each answered 441 and report the same
arena count (before the gate each left one unnamed sealed payload); the
owner is still running after each (RS-01: the refusal used to fault).
"""
import re
import unittest

from tests.native_harness import Client, native_image, requires
from tests import test_native_expiry as expiry

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


class PostSealGateRefusalSource(unittest.TestCase):
    def test_refused_staged_prepare_is_a_known_abort_not_a_reservation_refusal(self):
        from pathlib import Path
        text = (Path(__file__).resolve().parent.parent / "host/native/owner.lisp").read_text()
        start = text.index("(defun fnn-owner-attempt ")
        body = text[start:text.index("\n(defun ", start + 1)]
        gate = body.index("POST seal-gate refused")
        arm = body[gate:body.index("fnn-owner-prepare-refusal-word", gate)]
        # an accepted prepare leaves the store :record-staged, where
        # fn-owner-refuse-reservation answers :fault (store phase :reserved only)
        self.assertIn("(fnn-owner-action 'fn-owner-known-abort)", arm,
                      "a seal-gate refusal after an accepted prepare must abort the staged record")


@requires(IMAGE)
class NativePostSealGate(unittest.TestCase):
    image = IMAGE
    setUp = expiry.ExpiryMixin.setUp
    node = expiry.ExpiryMixin.node
    reclaim_live = expiry.ExpiryMixin.reclaim_live  # D53: node() reads it
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
                    # RS-01: the refusal answers the poster (441) and the
                    # owner keeps serving; it used to fault and fence.
                    first, final = c.post(expiry.article(tag, expiry.GROUP, None))
                    self.assertTrue((final or b"").startswith(b"441"), (first, final))
                finally:
                    c.close(False)
                self.assertIsNone(owner.poll(), owner.stderr.since(0)[-3000:])
            pattern = re.compile(rb"POST seal-gate refused arena=(\d+)")
            lines = self.owner_lines(owner, pattern, 2)
            self.assertEqual(len(lines), 2, owner.stderr.since(0)[-3000:])
            counts = {int(pattern.search(l).group(1)) for l in lines}
            self.assertEqual(len(counts), 1, lines)
        finally:
            node.stop(expect=None, grace=300)
