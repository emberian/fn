"""Differential test: the socket and `fn-served-run' must agree byte for byte.

The served path is now one certified function.  `books/served.lisp' proves
what it does; this test checks that the thing on the socket is that function
and nothing else.  The same octets go two ways:

  model   evaluated inside ACL2 as fn-served-open followed by fn-served-run
          over the exact chunk list, projected with fn-served-reply-octets;
  socket  through tools/run_reader.py's production serve_client over a real
          socketpair, whose chunking is whatever the kernel chose.

They must produce identical bytes.  The two differ in how the input was cut,
which is the point: `fn-served-run-is-the-concatenated-step' says the cut is
invisible, and this test is the evidence that the host obeys it.
"""
import socket
import sys
import threading
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_reader  # noqa: E402


MULTI_COMMAND = b"GROUP fn.letters\r\nSTAT\r\nQUIT\r\n"
UTF8_WILDMAT = b"LIST ACTIVE fn.\xc3\xb1*\r\nQUIT\r\n"
QUIT_WITH_TRAILER = b"QUIT\r\nSTAT\r\n"
BARE_LF = b"STAT\n"


def octet_literal(chunk):
    return "'(" + " ".join(str(byte) for byte in chunk) + ")"


class ServedDifferentialTests(unittest.TestCase):
    """One persistent bridge process, serialized connections."""

    @classmethod
    def setUpClass(cls):
        cls.reader = run_reader.Acl2Reader()

    @classmethod
    def tearDownClass(cls):
        cls.reader.close()

    def model_bytes(self, chunks):
        """Evaluate the reply stream of fn-served-run inside ACL2.

        The expression is pure: it reads the pinned archive constant and
        touches none of the bridge's globals, so it may be evaluated in the
        same session that serves the socket.
        """
        # The posting configuration, the clock observation and the AUTHINFO
        # policy are pinned at open; a read-only transcript never consults
        # them.  This form is `fn-reader-reset' (host/reader-host.lisp:137)
        # spelled out: the same archive, the same limits, the same
        # `(fn-auth-open-config)' the served side opens with.  A trailing
        # argument added to `fn-served-open' has to be added here too, or the
        # differential errors instead of comparing -- which is what happened
        # for a day after `d484e9a' gave it a seventh formal, since a call
        # spelled as TEXT is invisible to both sides.  `tools/harness_check.py
        # --lint acl2-arity' reads ACL2 forms out of Python string literals
        # and checks their arity against the books, for exactly this shape.
        open_form = ("(fn-served-open *fn-reader-archive* 510 8192"
                     " (fn-reader-post-config *fn-reader-archive* nil)"
                     " nil nil (fn-auth-open-config))")
        chunk_list = "(list " + " ".join(octet_literal(c) for c in chunks) + ")"
        form = (
            "(fn-served-reply-octets"
            " (append (fn-served-result-effects " + open_form + ")"
            " (fn-served-result-effects"
            " (fn-served-run (fn-served-result-conn " + open_form + ") "
            + chunk_list + "))))")
        return bytes(run_reader.acl2_octet_list(self.reader.call(form)))

    def socket_bytes(self, chunks):
        """Serve one connection through the production adapter."""
        server, client = socket.socketpair()
        thread = threading.Thread(
            target=run_reader.serve_client, args=(self.reader, server), daemon=True)
        thread.start()
        try:
            for chunk in chunks:
                if chunk:
                    client.sendall(bytes(chunk))
            client.shutdown(socket.SHUT_WR)
            client.settimeout(5)
            received = []
            while True:
                piece = client.recv(4096)
                if not piece:
                    break
                received.append(piece)
            thread.join(5)
            self.assertFalse(thread.is_alive(), "adapter did not release the connection")
            return b"".join(received)
        finally:
            client.close()

    def assertAgree(self, chunks):
        model = self.model_bytes(chunks)
        served = self.socket_bytes(chunks)
        self.assertEqual(served, model)
        return served

    def test_whole_transcript_agrees(self):
        served = self.assertAgree([MULTI_COMMAND])
        self.assertIn(b"211 1 1 1 fn.letters\r\n", served)

    def test_cut_inside_a_command_agrees(self):
        # "GROUP fn.let" | "ters\r\nSTAT\r\nQUIT\r\n"
        self.assertAgree([MULTI_COMMAND[:12], MULTI_COMMAND[12:]])

    def test_cut_after_a_reply_agrees(self):
        # The first chunk already earns the 211 reply, so the cut falls inside
        # the reply stream as well as inside the next command.
        self.assertAgree([MULTI_COMMAND[:20], MULTI_COMMAND[20:]])

    def test_bytewise_partition_agrees(self):
        self.assertAgree([MULTI_COMMAND[i:i + 1] for i in range(len(MULTI_COMMAND))])

    def test_split_utf8_wildmat_agrees(self):
        # The cut falls inside the C3 B1 encoding of the group-name character.
        self.assertAgree([UTF8_WILDMAT[:16], UTF8_WILDMAT[16:]])

    def test_input_after_quit_is_ignored_identically(self):
        self.assertAgree([QUIT_WITH_TRAILER])

    def test_framing_rejection_agrees(self):
        self.assertAgree([BARE_LF])


if __name__ == "__main__":
    unittest.main()
