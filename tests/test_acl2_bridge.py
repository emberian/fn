"""Correlation, poisoning and bounded parsing at the ACL2 pipe boundary.

These tests drive the real bridge code against a scripted pipe instead of a
live ACL2 process, so a lost, late or duplicated reply is reproducible.  No
ACL2 semantics are modelled here; only the host's own transport discipline is.
"""
import os
from pathlib import Path
import socket
import sys
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_reader  # noqa: E402
import run_store  # noqa: E402
from run_store import PROMPT, StoreError  # noqa: E402


class _Stream:
    """A pipe end with the attributes the bridge reads."""
    def __init__(self, fd):
        self._fd = fd
        self.closed = False

    def fileno(self):
        return self._fd

    def close(self):
        self.closed = True


class ScriptedProcess:
    """Replay scripted ACL2 output for each written form.

    Each script entry is either literal bytes or a callable applied to the
    bytes just written, which is how a reply can echo the caller's own nonce.
    """
    def __init__(self, script):
        self._read_fd, self._write_fd = os.pipe()
        self.script = list(script)
        self.written = []
        self.stdout = _Stream(self._read_fd)
        self.stdin = self

    def write(self, data):
        self.written.append(data)
        reply = self.script.pop(0) if self.script else b""
        if callable(reply):
            reply = reply(data)
        if reply:
            os.write(self._write_fd, reply)

    def flush(self):
        return None

    def poll(self):
        return None

    def close(self):
        for fd in (self._read_fd, self._write_fd):
            try:
                os.close(fd)
            except OSError:
                pass


def echo_marker(suffix=b"\n NIL\n" + PROMPT):
    """Answer a marker write the way ACL2 answers `(cw "FN_CALL_...~%")`."""
    def reply(data):
        marker = data.split(b'"')[1].replace(b"~%", b"")
        return marker + suffix
    return reply


class BridgeCorrelationTests(unittest.TestCase):
    def bridge(self, script):
        process = ScriptedProcess(script)
        self.addCleanup(process.close)
        bridge = object.__new__(run_store.Acl2Store)
        bridge.proc = process
        bridge.poisoned = False
        return bridge, process

    def test_marked_reply_is_accepted_and_returns_only_the_result(self):
        bridge, process = self.bridge([echo_marker(), b"(1 2 3)" + PROMPT])
        self.assertEqual(run_store.acl2_octets(bridge.call("(f)")), b"\x01\x02\x03")
        self.assertFalse(bridge.poisoned)
        self.assertIn(b"FN_CALL_", process.written[0])
        self.assertEqual(process.written[1], b"(f)\n")

    def test_fresh_nonce_per_call(self):
        bridge, process = self.bridge(
            [echo_marker(), b"NIL" + PROMPT, echo_marker(), b"NIL" + PROMPT])
        bridge.call("(f)")
        bridge.call("(g)")
        self.assertNotEqual(process.written[0], process.written[2])

    def test_reply_without_this_calls_marker_poisons_the_bridge(self):
        """The previous call's result can never be returned as this one's."""
        bridge, process = self.bridge([b"(9 9 9)" + PROMPT])
        with self.assertRaisesRegex(StoreError, "marker"):
            bridge.call("(f)")
        self.assertTrue(bridge.poisoned)
        # The form was never written: nothing reached ACL2 after the loss.
        self.assertEqual(len(process.written), 1)
        with self.assertRaisesRegex(StoreError, "poisoned"):
            bridge.call("(g)")
        self.assertEqual(len(process.written), 1)

    def test_stale_reply_arriving_with_the_marker_is_a_correlation_failure(self):
        bridge, _ = self.bridge([echo_marker(suffix=b"\n NIL\n" + PROMPT),
                                 b"NIL" + PROMPT])
        stale = ScriptedProcess([lambda data: b"(7)" + PROMPT + echo_marker()(data)])
        self.addCleanup(stale.close)
        bridge.proc = stale
        with self.assertRaisesRegex(StoreError, "marker"):
            bridge.call("(f)")
        self.assertTrue(bridge.poisoned)

    def test_timeout_poisons_the_bridge_for_good(self):
        bridge, _ = self.bridge([b""])
        with mock.patch.object(run_store, "ACL2_CALL_BASE_SECONDS", 0.2):
            with self.assertRaisesRegex(StoreError, "timeout"):
                bridge.call("(f)")
        self.assertTrue(bridge.poisoned)
        with self.assertRaisesRegex(StoreError, "poisoned"):
            bridge.call("(f)")

    def test_output_bound_trip_poisons_the_bridge(self):
        bridge, _ = self.bridge([echo_marker(), b"x" * 4096])
        with mock.patch.object(run_store, "MAX_ACL2_OUTPUT", 64):
            with self.assertRaisesRegex(StoreError, "exceeds bound"):
                bridge.call("(f)")
        self.assertTrue(bridge.poisoned)

    def test_acl2_error_reply_is_answered_without_poisoning(self):
        """A correlated refusal leaves the pipe synchronized and reusable."""
        bridge, _ = self.bridge([echo_marker(), b"ACL2 Error: nope" + PROMPT,
                                 echo_marker(), b"NIL" + PROMPT])
        with self.assertRaises(StoreError):
            bridge.call("(f)")
        self.assertFalse(bridge.poisoned)
        self.assertEqual(run_store.acl2_octets(bridge.call("(g)")), b"")

    def test_call_timeout_grows_with_form_size_and_bounds_the_recorded_reopen(self):
        base = run_store.Acl2Store.form_timeout("(f)")
        larger = run_store.Acl2Store.form_timeout("(f " + "1 " * 40000 + ")")
        self.assertGreaterEqual(base, run_store.ACL2_CALL_BASE_SECONDS)
        self.assertGreater(larger, base)
        # The recorded maximum-profile reopen on this machine is 11.7 s for
        # MAX_TRANSACTION_COUNT records.  The bound stays an order of magnitude
        # above it, rather than the fixed 20 s D2 found too close to it.
        recovery = (run_store.ACL2_RECOVER_BASE_SECONDS
                    + run_store.ACL2_RECOVER_PER_RECORD_SECONDS
                    * run_store.MAX_TRANSACTION_COUNT)
        self.assertGreater(recovery, 10 * 11.7)


class BridgeParsingTests(unittest.TestCase):
    def test_octet_list_parse_is_linear_on_malformed_output(self):
        # A repeated-group regular expression backtracks exponentially here.
        hostile = b"(" + b"1" * 64 + b"!"
        started = time.monotonic()
        self.assertIsNone(run_store.decimal_list(hostile))
        with self.assertRaises(StoreError):
            run_store.acl2_octets(hostile + PROMPT)
        with self.assertRaises(RuntimeError):
            run_reader.acl2_octet_list(hostile + PROMPT)
        self.assertLess(time.monotonic() - started, 1.0)

    def test_octet_list_accepts_only_bounded_decimal_octets(self):
        self.assertEqual(run_store.acl2_octets(b"(0 255)" + PROMPT), b"\x00\xff")
        self.assertEqual(run_store.acl2_octets(b"NIL" + PROMPT), b"")
        self.assertEqual(run_reader.acl2_octet_list(b"(1 2)" + PROMPT), [1, 2])
        self.assertEqual(run_reader.acl2_octet_list(b"NIL" + PROMPT), [])
        for bad in (b"(256)", b"(1,2)", b"(-1)", b"(1", b"1)", b"(1 2) (3)"):
            with self.subTest(bad=bad):
                with self.assertRaises(StoreError):
                    run_store.acl2_octets(bad + PROMPT)


class ReaderFailClosedTests(unittest.TestCase):
    class _Reader:
        def __init__(self, poisoned):
            self.poisoned = poisoned

        def reset(self):
            return b"200 ready\r\n"

        def chunk(self, octets):
            raise RuntimeError("unexpected ACL2 octet-list result")

    def serve(self, poisoned):
        server, client = socket.socketpair()
        self.addCleanup(server.close)
        self.addCleanup(client.close)
        client.sendall(b"QUIT\r\n")
        return run_reader.serve_client(self._Reader(poisoned), server)

    def test_poisoned_bridge_stops_the_reader_instead_of_serving_on(self):
        with self.assertRaisesRegex(run_reader.ReaderBridgeFault, "poisoned"):
            self.serve(poisoned=True)

    def test_a_merely_invalid_result_still_only_ends_the_connection(self):
        self.assertIsNone(self.serve(poisoned=False))


if __name__ == "__main__":
    unittest.main()
