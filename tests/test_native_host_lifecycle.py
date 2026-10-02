"""Host lifecycle: a client's or peer's event ends that connection, never the
node (lane host-lifecycle, 2026-10-03; Astra r71, inspection sweep
2026-10-03).

Each case is a remote or lifecycle event the native host once turned into a
stopped owner, a wedged loop or an unjoined worker, driven on a scratch
developer node; the assertion is that the node keeps serving (or settles its
stop cleanly) and that the client gets the protocol's answer.

    FN_NATIVE_DEVELOPER_HOST=build/fn-host-developer \\
        python3 -m unittest tests.test_native_host_lifecycle
"""
import time
import unittest

from tests.native_harness import (EXIT, Client, Node, article, client_context, native_image,
                                  requires)

DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


def read_reply(client, status_prefix):
    """The status line, and the dot-terminated block when the status says one follows."""
    status = client.line()
    block = client.block() if status.startswith((b"220", b"221", b"222")) else None
    return status, block


@requires(DEVELOPER)
class TlsPipelineTests(unittest.TestCase):
    """r71 F3 / sweep S010 (host/native/mux.lisp fnn-mux-step): on a protected
    channel a step that consumed a prefix of the record without closing,
    submitting or redeeming was a fault of the whole service ("protected
    owner read left a TLS suffix").  A pipelined line whose payload is not in
    memory splits the read (row A4 (c), fnn-owner-chunk-span-no-io: the warm
    lines first, then the cold line alone), so any TLS client could stop the
    node with DATE, ARTICLE <cold>, DATE in one record.  The suffix is the
    next step's input, as on a plaintext connection."""

    MSGID = b"<tls-cold@example.invalid>"

    def setUp(self):
        self.node = Node(self, DEVELOPER).use_tls(protected_only=False)
        self.node.init()
        owner = self.node.start()
        with Client(self.node.port, timeout=60) as poster:
            first, final = poster.post(article(self.MSGID, body=b"cold body\r\n"))
            self.assertTrue(first.startswith(b"340"), first)
            self.assertTrue(final.startswith(b"240"), final)
        self.node.stop(process=owner)
        # Reopened: the payload is a cold extent (nothing read it yet).
        self.owner = self.node.start()

    def tls(self):
        return Client(self.node.tls_port, timeout=60, implicit_tls=client_context())

    def test_a_pipelined_cold_line_in_one_tls_record_is_served_in_order(self):
        with self.node.log_on_failure(self.owner):
            client = self.tls()
            try:
                # One write is one TLS record: the whole pipeline is one read.
                client.send(b"DATE\r\nARTICLE " + self.MSGID + b"\r\nDATE\r\n")
                self.assertTrue(client.line().startswith(b"111 "))
                status, block = read_reply(client, b"220")
                self.assertTrue(status.startswith(b"220 "), status)
                self.assertIn(b"cold body", block)
                self.assertTrue(client.line().startswith(b"111 "))
                self.assertTrue(client.command(b"DATE").startswith(b"111 "))
            finally:
                client.close()
            self.assertIsNone(self.owner.poll(), "a TLS client's pipeline stopped the owner")
            # The node still serves a new connection, plaintext and TLS.
            with Client(self.node.port, timeout=60) as plain:
                self.assertTrue(plain.command(b"DATE").startswith(b"111 "))
            with self.tls() as again:
                self.assertTrue(again.command(b"DATE").startswith(b"111 "))
            self.node.stop(process=self.owner, expect=EXIT.OK)

    def test_a_cold_first_line_then_a_pipelined_line_in_one_tls_record(self):
        with self.node.log_on_failure(self.owner):
            client = self.tls()
            try:
                client.send(b"ARTICLE " + self.MSGID + b"\r\nDATE\r\n")
                status, block = read_reply(client, b"220")
                self.assertTrue(status.startswith(b"220 "), status)
                self.assertIn(b"cold body", block)
                self.assertTrue(client.line().startswith(b"111 "))
            finally:
                client.close()
            self.assertIsNone(self.owner.poll(), "a TLS client's pipeline stopped the owner")
            self.node.stop(process=self.owner, expect=EXIT.OK)


if __name__ == "__main__":
    unittest.main()
