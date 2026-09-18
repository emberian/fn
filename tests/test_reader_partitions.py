"""Partition and connection-reset matrix for the experimental NNTP reader.

The tests use one real ACL2-backed ``Acl2Reader`` and the production
``serve_client`` socket adapter, serially.  Expected replies are written as
independent protocol transcripts rather than obtained from an unpartitioned
run.
"""
import socket
import struct
import sys
from pathlib import Path
import threading
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_reader  # noqa: E402


GREETING = b"201 fn-nntp experimental reader ready\r\n"
MULTI_COMMAND = b"GROUP fn.letters\r\nSTAT\r\nQUIT\r\n"
MULTI_REPLY = (
    GREETING
    + b"211 1 1 1 fn.letters\r\n"
    + b"223 1 <reader@example.invalid> retrieved\r\n"
    + b"205 closing connection\r\n"
)
UTF8_WILDMAT = b"LIST ACTIVE fn.\xc3\xb1*\r\nQUIT\r\n"
UTF8_WILDMAT_REPLY = (
    GREETING
    + b"215 list of active newsgroups follows\r\n.\r\n"
    + b"205 closing connection\r\n"
)
RESET_REPLY = GREETING + b"412 no newsgroup selected\r\n205 closing connection\r\n"
MALFORMED_REPLY = GREETING + b"501 syntax error\r\n"


class ReaderPartitionMatrixTests(unittest.TestCase):
    """Serialized connection cases against one persistent bridge process."""

    @classmethod
    def setUpClass(cls):
        cls.reader = run_reader.Acl2Reader()

    @classmethod
    def tearDownClass(cls):
        cls.reader.close()

    def _exchange(self, chunks, expected):
        """Serve one socketpair connection and return its independent bytes."""
        server, client = socket.socketpair()
        thread = threading.Thread(
            target=run_reader.serve_client, args=(self.reader, server), daemon=True)
        thread.start()
        try:
            for chunk in chunks:
                if chunk:
                    client.sendall(chunk)
            client.shutdown(socket.SHUT_WR)
            client.settimeout(5)
            received = []
            while True:
                piece = client.recv(4096)
                if not piece:
                    break
                received.append(piece)
            thread.join(5)
            self.assertFalse(thread.is_alive(), "serialized client did not close")
            actual = b"".join(received)
            self.assertEqual(actual, expected)
            return actual
        finally:
            client.close()

    def _direct_chunks(self, chunks, expected):
        """Feed exact bridge chunks, draining each returned suffix first."""
        replies = [self.reader.reset()]
        closing = False
        suffix = []
        for piece in chunks:
            pending = list(piece)
            # Empty chunks are sent through the real bridge too.
            if not pending:
                reply, empty_closing, suffix = self.reader.chunk([])
                replies.append(reply)
                self.assertEqual(suffix, [])
                closing = closing or empty_closing
                continue
            while pending:
                reply, closing, suffix = self.reader.chunk(pending)
                replies.append(reply)
                if closing:
                    self.assertEqual(suffix, [])
                    pending = []
                else:
                    pending = suffix
        self.assertTrue(closing)
        self.assertEqual(b"".join(replies), expected)

    def _direct_partition(self, payload, expected):
        for cut in range(len(payload) + 1):
            with self.subTest(cut=cut, payload=payload):
                self._direct_chunks((payload[:cut], payload[cut:]), expected)

    def test_every_two_piece_cut_preserves_multicommand_crlf_transcript(self):
        # This includes cuts immediately before and after every CRLF and
        # drains suffixes before feeding the next exact bridge chunk.
        self._direct_partition(MULTI_COMMAND, MULTI_REPLY)

    def test_every_two_piece_cut_preserves_split_utf8_wildmat_transcript(self):
        # The matrix includes both cuts inside the C3 B1 encoding of ñ as well
        # as command CRLF cuts.  The expected result is an empty listing.
        self._direct_partition(UTF8_WILDMAT, UTF8_WILDMAT_REPLY)

    def test_bytewise_coalesced_and_empty_chunks_have_same_expected_reply(self):
        self._direct_chunks(tuple(bytes((byte,)) for byte in MULTI_COMMAND), MULTI_REPLY)
        self._direct_chunks((MULTI_COMMAND,), MULTI_REPLY)

        # Empty chunks are a bridge-level no-op and must not perturb a fixed
        # protocol transcript.  Drain the bridge's explicit suffix result.
        self.assertEqual(self.reader.reset(), GREETING)
        self.assertEqual(self.reader.chunk([]), (b"", False, []))
        self.assertEqual(self.reader.chunk([]), (b"", False, []))
        reply, closing, suffix = self.reader.chunk(list(MULTI_COMMAND))
        replies = [reply]
        while suffix:
            self.assertEqual(self.reader.chunk([]), (b"", False, []))
            reply, closing, suffix = self.reader.chunk(suffix)
            replies.append(reply)
        self.assertEqual(b"".join(replies), MULTI_REPLY[len(GREETING):])
        self.assertTrue(closing)
        self.assertEqual(suffix, [])

    def test_malformed_and_oversize_commands_reject_and_close(self):
        self._exchange((b"STAT\n",), MALFORMED_REPLY)
        oversize = b"X" * 511 + b"\r\n"
        self._exchange((oversize[:257], oversize[257:]), MALFORMED_REPLY)

    def test_quit_ignores_suffix_and_closes_connection(self):
        self._exchange((b"QUIT\r\nSTAT\r\n",), GREETING + b"205 closing connection\r\n")

    def test_partial_disconnect_does_not_leak_session_to_next_connection(self):
        # A disconnected partial line produces only the greeting.  The next
        # connection is freshly reset and therefore has no selected group.
        self._exchange((b"GROUP fn.le",), GREETING)
        self.assertEqual(
            self._exchange((b"STAT\r\nQUIT\r\n",), RESET_REPLY), RESET_REPLY)

    def test_connection_reset_after_partial_input_leaves_next_connection_usable(self):
        # Use an actual loopback TCP reset so SO_LINGER has TCP semantics.
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        accepted = []

        def accept_and_serve():
            connection, unused_address = listener.accept()
            accepted.append(connection)
            run_reader.serve_client(self.reader, connection)

        thread = threading.Thread(target=accept_and_serve, daemon=True)
        thread.start()
        client = socket.create_connection(listener.getsockname(), timeout=5)
        try:
            client.sendall(b"GROUP fn.le")
            client.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER,
                              struct.pack("ii", 1, 0))
            client.close()
            thread.join(5)
            self.assertFalse(thread.is_alive(), "reset client did not release adapter")
        finally:
            try:
                client.close()
            except OSError:
                pass
            listener.close()
        self._exchange((b"STAT\r\nQUIT\r\n",), RESET_REPLY)


if __name__ == "__main__":
    unittest.main()
