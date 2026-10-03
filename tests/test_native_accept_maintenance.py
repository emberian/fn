"""r71 F8: a SIGTERM is consumed while a barrier stalls (lane served-live,
2026-10-03; ledger r71-F8, acceptance lifecycle:reap-off-section).

The primary accept loop ran the owner's maintenance itself between accepts:
the cold reap (a :control section even with nothing to reap), the
checkpoint publication decision (:control), the log reopen and the retire
step.  Behind a batch whose barrier does not return, each waited at the
owner's scheduling gate, so the loop never came back to its SIGTERM check
and the stop's drain did not begin.  The maintenance now has its own worker
(host/native/owner.lisp fnn-owner-start-maintenance) and the accept loop
enters no gate.

The case stalls the device (FN_NATIVE_TEST_DISK_STALL_FILE), leaves a POST
waiting on its barrier, sends SIGTERM and asserts the owner announces its
drain within DRAIN_SECONDS while the device is still stalled; released, the
owner answers the POST and exits cleanly.
"""
import signal
import threading
import time
import unittest

from tests.native_harness import Client, Node, article, executable, native_image

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
DRAIN_SECONDS = 6
DRAIN_LINE = b"stopping: answering the posts in flight first"


@unittest.skipUnless(executable(DEVELOPER), "an executable FN_NATIVE_DEVELOPER_HOST is required")
class NativeAcceptMaintenanceTests(unittest.TestCase):
    def test_sigterm_is_consumed_behind_a_stalled_barrier(self):
        node = Node(self, DEVELOPER, name="accept-maintenance")
        node.init()
        stall = node.root / "stall"
        self.addCleanup(lambda: stall.unlink() if stall.exists() else None)
        owner = node.start(env={"FN_NATIVE_TEST_DISK_STALL_FILE": str(stall)})
        with node.log_on_failure(owner):
            with Client(node.port, timeout=60) as warm:
                _, final = warm.post(article(b"<maint-warm@example.invalid>"))
                self.assertTrue(final.startswith(b"240"), final)
            stall.write_bytes(b"")
            answer = {}
            client = Client(node.port, timeout=120)
            self.addCleanup(client.close, False)

            def post():
                try:
                    answer["reply"] = client.post(article(b"<maint-stalled@example.invalid>"))
                except Exception as error:
                    answer["error"] = error

            poster = threading.Thread(target=post)
            poster.start()
            time.sleep(2)
            self.assertTrue(poster.is_alive(), "the POST was answered through a stalled barrier")
            offset = len(owner.stderr.since(0))
            # Let the maintenance reach its gate behind the stalled batch.
            time.sleep(2)
            owner.signal(signal.SIGTERM)
            signalled = time.monotonic()
            deadline = signalled + DRAIN_SECONDS
            while time.monotonic() < deadline and DRAIN_LINE not in owner.stderr.since(offset):
                time.sleep(0.1)
            drained_after = time.monotonic() - signalled
            self.assertIn(DRAIN_LINE, owner.stderr.since(offset),
                          "the SIGTERM was not consumed within {} s behind a stalled barrier".format(
                              DRAIN_SECONDS))
            print("ACCEPT-MAINTENANCE drain-announced-after={:.3f}s".format(drained_after), flush=True)
            stall.unlink()
            poster.join(timeout=120)
            self.assertFalse(poster.is_alive())
            owner.wait(timeout=120)
            owner.finish()


if __name__ == "__main__":
    unittest.main()
