"""PKT-466(b): SCN-106's six cuts with actual process kills on production.

The consumer application SIGSTOPs at its declared boundary; this harness
SIGKILLs it. For the two owner cuts a Unix relay holds the answer; the
harness kills the owner, drops the answer and reopens. The original scenario
requires recovered ACK/Q state, separate uncertain outcomes, and one
application transition. No developer selector reaches the fn owner.
"""
import json
import os
import signal
import sys
import time
import unittest

from tests.native_harness import ROOT, native_image, requires, scratch, start
from tests.consumer_reply_hold import ConsumerReplyHold
from tests.test_native_consumer_exchange_two_nodes import (
    CONSUMER, TwoNodeConsumerExchangeScenario)

IMAGE = native_image("FN_NATIVE_HOST")
ENABLED = os.environ.get("FN_RUN_CONSUMER_EXCHANGE") == "1"


@unittest.skipUnless(ENABLED, "set FN_RUN_CONSUMER_EXCHANGE=1")
@requires(IMAGE)
class NativeProductionConsumerExchangeTests(TwoNodeConsumerExchangeScenario,
                                          unittest.TestCase):
    image = IMAGE

    def consumer(self, config, *words, cut=None, expected=0, background=False):
        if cut is None:
            return super().consumer(config, *words, expected=expected, background=background)
        self.assertFalse(background, "a cut process is owned by the external killer")
        env = dict(self.env, FN_CONSUMER_CUT=cut, FN_CONSUMER_CUT_ACTION="stop")
        proc = start([sys.executable, str(CONSUMER), str(config), *words], cwd=ROOT, env=env)
        self.addCleanup(proc.stop, 1)
        marker = ("CONSUMER-CUT " + cut).encode()
        deadline = time.monotonic() + 900
        while marker not in proc.stderr.since(0):
            if proc.poll() is not None or time.monotonic() >= deadline:
                self.fail("consumer never reached %s: %r" % (cut, proc.stderr.since(0)))
            time.sleep(0.02)
        proc.kill()
        stdout, stderr = proc.communicate(timeout=30)
        self.assertEqual(proc.returncode, -signal.SIGKILL, (stdout, stderr))
        self.log.append([config.parent.name, list(words), cut, proc.returncode,
                         "external SIGKILL after application cut announcement"])
        # All cut callers only inspect the durable database after reopening.
        return proc

    def cut_at_owner(self, node, config, *words):
        proxy_root = scratch(self, "fn-consumer-reply-hold-")
        proxy = ConsumerReplyHold(proxy_root / "control.sock", node.control)
        self.addCleanup(proxy.close)
        original = config.read_text(encoding="utf-8")
        routed = json.loads(original)
        routed["control"] = proxy.path
        config.write_text(json.dumps(routed), encoding="utf-8")
        try:
            proc = self.consumer(config, *words, background=True)
            self.assertTrue(proxy.reply_received.wait(300), proxy.error)
            # Receiving an octet is only the cut trigger, never acceptance
            # evidence: the scenario requires committed ACK/Q after reopen.
            self.kill(node)
            proxy.close()
            stdout, stderr = proc.communicate(timeout=300)
            self.assertEqual(proc.returncode, 3, (stdout + stderr).decode("utf-8", "replace"))
            self.log.append([config.parent.name, list(words), "owner-reply-held",
                             proc.returncode, "external owner SIGKILL; reply discarded"])
        finally:
            config.write_text(original, encoding="utf-8")
            proxy.close()
        self.start(node)
        return json.loads(stdout)


if __name__ == "__main__":
    unittest.main()
