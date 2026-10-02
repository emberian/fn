"""A reclaim requested while another pass is in flight is refused by name
(SWEEP-OPS S038: the capture checks admission before it reserves or writes
anything), and the running pass completes normally.

The first pass is held at its rebuilt cut (FN_NATIVE_TEST_RECLAIM_STALL_FILE);
a dry run and a recorded pass are requested meanwhile; both answer REFUSED
with DEFERRED-IN-FLIGHT (or -QUEUED) and never finish the held pass's slot;
releasing the stall, the held pass installs.
"""
import re
import threading
import unittest

from tests.native_harness import Client, EXIT, native_image, requires
from tests import test_native_expiry as expiry

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")


@requires(IMAGE)
class NativeReclaimInFlight(unittest.TestCase):
    image = IMAGE
    setUp = expiry.ExpiryMixin.setUp
    node = expiry.ExpiryMixin.node
    post_all = expiry.ExpiryMixin.post_all
    filled = expiry.ExpiryMixin.filled
    reclaim = expiry.ExpiryMixin.reclaim
    owner_lines = expiry.ExpiryMixin.owner_lines
    recorded_base = expiry.DeveloperExpiryTests.recorded_base
    copy_of = expiry.DeveloperExpiryTests.copy_of

    def test_second_pass_and_dry_run_refused_while_one_runs(self):
        node = self.copy_of(self.recorded_base(), "in-flight")
        stall = self.root / "reclaim-stall"
        stall.write_bytes(b"")
        owner = node.start(timeout=600, env={"FN_NATIVE_TEST_RECLAIM_STALL_FILE": str(stall)})
        try:
            result = {}
            worker = threading.Thread(
                target=lambda: result.setdefault("done", self.reclaim(node, "--recorded", expect=None)))
            worker.start()
            held = self.owner_lines(owner, re.compile(rb"RECLAIM stalled at=rebuilt"), 1, deadline=600)
            self.assertEqual(len(held), 1, owner.stderr.since(0)[-3000:])
            dry = self.reclaim(node, "--dry-run", expect=None)
            self.assertEqual(dry.returncode, EXIT.REFUSED, (dry.stdout, dry.stderr[-600:]))
            self.assertRegex(dry.stdout + dry.stderr, rb"(?i)deferred-(in-flight|queued)|in-flight|queued")
            second = self.reclaim(node, "--recorded", expect=None)
            self.assertEqual(second.returncode, EXIT.REFUSED, (second.stdout, second.stderr[-600:]))
            self.assertNotIn(b"installed", second.stdout)
            refused = self.owner_lines(owner, re.compile(rb"RECLAIM (dry-run refused: (in-flight|queued)|deferred reason=(in-flight|queued))"), 2)
            self.assertEqual(len(refused), 2, owner.stderr.since(0)[-3000:])
            stall.unlink()
            worker.join(timeout=1300)
            self.assertFalse(worker.is_alive())
            done = result["done"]
            self.assertEqual(done.returncode, EXIT.OK, (done.stdout, done.stderr[-600:]))
            self.assertIn(b"installed", done.stdout, done.stdout)
            with Client(node.port, timeout=300, greeting=None) as c:
                self.assertTrue(c.command("STAT %s" % expiry.msgid("p0")).startswith(b"430 article reclaimed"))
                self.assertTrue(c.command("STAT %s" % expiry.msgid("n0")).startswith(b"223"))
        finally:
            stall.unlink(missing_ok=True)
            node.stop(expect=None, grace=300)
