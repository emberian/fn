"""PRF-986 (PKT-639, row W2a): the TLS handshake is an admission ACL2 decides.

One owner on 127.0.0.1 with an implicit-TLS listener; strangers are other
loopback source addresses (127.0.0.0/8 routes to lo on Linux).

- A flood of handshakes from one source is refused by name past its budget
  (`policy set tls-handshakes-per-source-per-minute 3'): three complete, the
  rest are closed before any handshake work and the service log names
  `tls refused reason=handshake-budget source=127.0.0.2'; a second source is
  still served.
- Slow-loris handshakes (TCP connected, no ClientHello, ever) hold at most
  `tls-handshakes-in-flight' slots (2 here) for at most `tls-handshake-ms'
  (2,000 ms here): a legitimate client that arrives behind them waits its
  turn, unadmitted, and completes once the deadline frees a slot; the log
  names `reason=timeout'.
- A source listed in `policy set tls-handshake-source-overrides' (a carrier
  NAT's address) is admitted at its own rate while another source stays at
  the row's; a list that does not parse is refused; `none' clears it live.

Run on hbox: tools/hbox_native.sh . tests.test_native_tls_handshake_budget
"""
from __future__ import annotations

import os
from pathlib import Path
import socket
import ssl
import time
import unittest

from tests.native_harness import EXIT, Node, executable, native_image

IMAGE = (Path(os.environ["FN_NATIVE_HOST"]) if os.environ.get("FN_NATIVE_HOST")
         else native_image("FN_NATIVE_DEVELOPER_HOST"))
READY = executable(IMAGE)


def client_context() -> ssl.SSLContext:
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    return context


@unittest.skipUnless(READY, "no native image (FN_NATIVE_HOST or build/fn-host-developer)")
class NativeTlsHandshakeBudgetTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.addCleanup(self.stop)
        self.node.store("init", "fn.test", expect=EXIT.OK)
        self.node.use_tls()
        self.log = self.node.root / "fn.log"
        key = self.node.root / "key.pem"
        self.node.write_config(
            extra='tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[log]\npath = "{}"\n'.format(
                self.node.tls_port, self.node.cert, key, self.log),
            protected_only=True)

    def stop(self):
        if self.node.process is not None:
            self.node.stop(expect=None)

    def policy(self, slot, value):
        self.node.operator("policy", "set", slot, str(value), expect=EXIT.OK)

    def start(self):
        # Node.start waits for both listeners' announcements (use_tls sets
        # listening = 2), LISTENING-TLS among them.
        self.node.start()

    def handshake(self, source, timeout=10):
        """True when the TLS handshake from SOURCE completes and the node
        greets; False when the node closes it (a refusal)."""
        raw = socket.create_connection(("127.0.0.1", self.node.tls_port), timeout=timeout,
                                       source_address=(source, 0))
        try:
            sock = client_context().wrap_socket(raw, server_hostname="127.0.0.1")
        except (ssl.SSLError, ConnectionResetError, BrokenPipeError, OSError):
            raw.close()
            return False
        try:
            sock.settimeout(timeout)
            line = sock.recv(512)
            return line[:3] in (b"200", b"201", b"480")
        finally:
            sock.close()

    def log_text(self, needle, deadline=10):
        end = time.monotonic() + deadline
        while time.monotonic() < end:
            text = self.log.read_text(errors="replace") if self.log.exists() else ""
            if needle in text:
                return text
            time.sleep(0.2)
        self.fail("the service log never named {!r}".format(needle))

    def test_a_flood_from_one_source_is_refused_by_name_and_another_is_served(self):
        self.policy("tls-handshakes-per-source-per-minute", 3)
        self.start()
        outcomes = [self.handshake("127.0.0.2") for _ in range(8)]
        self.assertEqual(outcomes[:3], [True, True, True], outcomes)
        self.assertEqual(outcomes[3:], [False] * 5, outcomes)
        self.log_text("tls refused reason=handshake-budget source=127.0.0.2")
        self.assertTrue(self.handshake("127.0.0.3"), "a second source was not served")
        # Live: the operator raises the budget; the first source is served again
        # only as its bucket refills (not reset), so a new source proves the row.
        self.policy("tls-handshakes-per-source-per-minute", 60)
        self.assertTrue(self.handshake("127.0.0.4"))
        self.assertIsNone(self.node.process.poll(), "the owner exited")

    def test_a_listed_source_has_its_own_rate_and_the_others_keep_theirs(self):
        # A carrier NAT's address (here 127.0.0.5) is listed at 20 a minute;
        # the row's 3 still holds for every other source.
        self.policy("tls-handshakes-per-source-per-minute", 3)
        self.policy("tls-handshake-source-overrides", "127.0.0.5=20,127.0.0.8=20")
        # A list that does not parse is refused by the administrative plan and
        # changes nothing (the owner reads the list above).
        self.node.operator("policy", "set", "tls-handshake-source-overrides", "127.0.0.300=20",
                           expect=EXIT.USAGE)
        self.start()
        listed = [self.handshake("127.0.0.5") for _ in range(8)]
        self.assertEqual(listed, [True] * 8, listed)
        other = [self.handshake("127.0.0.6") for _ in range(5)]
        self.assertEqual(other, [True, True, True, False, False], other)
        self.log_text("tls refused reason=handshake-budget source=127.0.0.6")
        # Live: `none' clears the list; 127.0.0.8, listed until now and not
        # yet seen, is at the row's 3.
        self.policy("tls-handshake-source-overrides", "none")
        cleared = [self.handshake("127.0.0.8") for _ in range(5)]
        self.assertEqual(cleared, [True, True, True, False, False], cleared)
        self.assertIsNone(self.node.process.poll(), "the owner exited")

    def test_slow_handshakes_hold_at_most_the_in_flight_slots_for_the_deadline(self):
        self.policy("tls-handshakes-in-flight", 2)
        self.policy("tls-handshake-ms", 2000)
        self.start()
        loris = [socket.create_connection(("127.0.0.1", self.node.tls_port), timeout=10,
                                          source_address=("127.0.1.{}".format(i), 0))
                 for i in range(1, 5)]
        try:
            time.sleep(0.3)  # the node has decided all four: two in flight, two waiting
            began = time.monotonic()
            served = self.handshake("127.0.0.9", timeout=15)
            waited = time.monotonic() - began
            self.assertTrue(served, "the legitimate client was not served")
            # It waited behind the two slots the silent handshakes held, and no
            # longer than their deadline plus its own turn.
            self.assertGreater(waited, 1.2, waited)
            self.assertLess(waited, 10.0, waited)
            self.log_text("tls refused reason=timeout")
        finally:
            for sock in loris:
                sock.close()
        self.assertIsNone(self.node.process.poll(), "the owner exited")


if __name__ == "__main__":
    unittest.main()
