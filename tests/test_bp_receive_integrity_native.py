"""Native BP receive evidence identity, fencing, and fault taxonomy."""

import time
import unittest

from tests.native_harness import (
    EXIT, environment, native_image, requires, run, scratch, start)

IMAGE = native_image("FN_NATIVE_BP_HOST")


def log(process):
    """Everything PROCESS wrote, stdout then stderr, as text (after `finish`
    for all of it)."""
    return (process.stdout.since(0) + process.stderr.since(0)).decode("utf-8", "replace")


@requires(IMAGE)
class NativeBpReceiveIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = scratch(self, "fn-bp-receive-integrity-")
        self.journal = self.tmp / "journal"

    def spawn_receive(self, name, *, once="1", env=None):
        process = start(
            [IMAGE, "--fn", "bp", "receive", "0", once, self.journal, "dtn://fn-b/", "-",
             "3600000", "2", "32", "1048576", "-", "-", "-", "0"],
            env=environment(env))
        self.addCleanup(process.stop, 10)
        line = process.announcement(b"BP LISTENING ", timeout=15)
        return process, int(line.rsplit(b" ", 1)[1])

    def send(self, port, payload, name, *, segment_mru=1024):
        source = self.tmp / f"{name}.bundle"
        source.write_bytes(payload)
        return run(
            [IMAGE, "--fn", "tcpcl", "send", "127.0.0.1", port, source,
             self.tmp / f"{name}-peer", "dtn://fn-a/", "-", "4", segment_mru, "1048576",
             "0", "-"], timeout=30)

    def wait_for_wire_count(self, count, timeout=15):
        evidence = self.journal / "receive-evidence"
        deadline = time.time() + timeout
        while time.time() < deadline:
            wires = sorted(evidence.glob("*.wire")) if evidence.exists() else []
            if len(wires) >= count:
                return wires
            time.sleep(0.02)
        self.fail(f"did not observe {count} durable wire records")

    def test_receive_core_fault_remains_exit_four(self):
        receiver, port = self.spawn_receive("fault", env={"FN_BP_TEST_DELIVER_FAULT": "1"})
        self.send(port, b"trigger receive callback", "fault-input")
        receiver.wait(timeout=20)
        receiver.finish()
        output = log(receiver)
        self.assertEqual(receiver.returncode, EXIT.FAULT, output)
        self.assertIn("injected receive core fault", output)
        self.assertNotIn("BP refused xfer=", output)

    def test_two_sessions_reusing_transfer_zero_keep_both_exact_wires(self):
        receiver, port = self.spawn_receive("two-sessions", once="0")
        first = b"first malformed BP transfer"
        second = b"second distinct malformed BP transfer"

        sent1 = self.send(port, first, "first")
        sent2 = self.send(port, second, "second")
        self.assertEqual(sent1.returncode, EXIT.REFUSED, sent1.stdout + sent1.stderr)
        self.assertEqual(sent2.returncode, EXIT.REFUSED, sent2.stdout + sent2.stderr)
        self.assertIn(b"outbound xfer=0", sent1.stdout)
        self.assertIn(b"outbound xfer=0", sent2.stdout)
        self.assertNotIn(b"accepted outbound xfer=0", sent1.stdout)
        self.assertNotIn(b"accepted outbound xfer=0", sent2.stdout)

        wires = self.wait_for_wire_count(2)
        self.assertEqual({path.read_bytes() for path in wires}, {first, second})
        self.assertEqual(
            [path.name for path in wires],
            ["00000000000000000000.wire", "00000000000000000001.wire"],
        )
        # The receiver still serves (once=0): wait for both refusals on its drain.
        receiver.output_until(b"BP refused xfer=0", timeout=15)
        receiver.output_until(b"BP refused xfer=0", timeout=15)
        output = log(receiver)
        self.assertEqual(output.count("BP refused xfer=0"), 2, output)

    def test_refusal_after_partial_segments_has_no_successful_end_ack(self):
        receiver, port = self.spawn_receive("partial-refusal")
        wire = b"malformed bundle across three or more segments"
        sent = self.send(port, wire, "partial", segment_mru=16)
        receiver.wait(timeout=20)
        receiver.finish()
        output = log(receiver)
        self.assertEqual(sent.returncode, EXIT.REFUSED, sent.stdout + sent.stderr)
        self.assertIn(b"refused outbound xfer=0", sent.stdout)
        self.assertNotIn(b"accepted outbound xfer=0", sent.stdout)
        self.assertIn("BP refused xfer=0", output)
        self.assertEqual(self.wait_for_wire_count(1)[0].read_bytes(), wire)

    def test_uncertain_publication_exits_and_prevents_next_session_mutation(self):
        receiver, port = self.spawn_receive(
            "uncertain", once="0", env={"FN_IMMUTABLE_PUBLISH_TEST_FAIL": "namespace"})
        first = b"visible wire with uncertain namespace barrier"
        self.send(port, first, "uncertain-first")

        receiver.wait(timeout=20)
        receiver.finish()
        output = log(receiver)
        self.assertEqual(receiver.returncode, EXIT.UNCERTAIN, output)
        self.assertIn("receive wire evidence publication uncertain", output)
        wires = self.wait_for_wire_count(1)
        self.assertEqual([path.read_bytes() for path in wires], [first])

        second = self.send(port, b"must not reach the fenced owner", "after-fence")
        self.assertNotEqual(second.returncode, EXIT.OK, second.stdout + second.stderr)
        time.sleep(0.1)
        self.assertEqual(
            len(list((self.journal / "receive-evidence").glob("*.wire"))), 1
        )

        # Reopen barriers and ACL2 recovery consume the visible wire-only
        # identity.  The next process must not reuse or replace it.
        restarted, restarted_port = self.spawn_receive("after-restart", once="1")
        after_restart = b"new transfer after authoritative recovery"
        sent = self.send(restarted_port, after_restart, "after-restart-input")
        restarted.wait(timeout=20)
        restarted.finish()
        self.assertEqual(sent.returncode, EXIT.REFUSED, sent.stdout + sent.stderr)
        self.assertIn(b"refused outbound xfer=0", sent.stdout)
        self.assertIn(restarted.returncode, (EXIT.OK, EXIT.REFUSED))
        wires = self.wait_for_wire_count(2)
        self.assertEqual(
            [path.name for path in wires],
            ["00000000000000000000.wire", "00000000000000000001.wire"],
        )
        self.assertEqual({path.read_bytes() for path in wires}, {first, after_restart})


if __name__ == "__main__":
    unittest.main()
