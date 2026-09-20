"""Differential test: the native host's socket and `fn-served-run' agree.

The mirror of tests/test_served_differential.py for the host that has no
Python in it.  The same octets go two ways through `build/fn-host`:

  model   `--fn model CHUNKS -`, which is one `fn-served-open' followed by
          one `fn-served-run' over the exact chunk list, projected with
          `fn-served-reply-octets' (host/native/reader-model-host.lisp);
  socket  `--fn reader 0 1 -`, the production listener, whose chunking is
          whatever the kernel chose.

They must produce identical bytes.  The two differ in how the input was cut,
which is the point: `fn-served-run-is-the-concatenated-step' says the cut is
invisible, and this test is the evidence that the native host obeys it -- one
`fn-served-step' per socket read, the reply octets from the book, no wire
loop in host/native/io.lisp.

The image is built by tools/build_native_host.sh; without it these tests are
skipped rather than silently passing.
"""
import os
from pathlib import Path
import select
import socket
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import fn_native  # noqa: E402


MULTI_COMMAND = b"GROUP fn.letters\r\nSTAT\r\nQUIT\r\n"
UTF8_WILDMAT = b"LIST ACTIVE fn.\xc3\xb1*\r\nQUIT\r\n"
QUIT_WITH_TRAILER = b"QUIT\r\nSTAT\r\n"
BARE_LF = b"STAT\n"


def image_environment():
    env = dict(os.environ)
    env.pop("FN_HOST", None)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    return env


class NativeServedDifferentialTests(unittest.TestCase):
    """One image invocation per side, both over the seeded archive."""

    @classmethod
    def setUpClass(cls):
        cls.image = fn_native.image_path()
        if not os.access(cls.image, os.X_OK):
            raise unittest.SkipTest(
                "native host image missing: {} (tools/build_native_host.sh)".format(cls.image))

    def model_bytes(self, chunks):
        """The reply stream of `fn-served-run', evaluated inside the image.

        The chunk file is length-prefixed so that a chunk may hold any octet,
        including LF and the split halves of a UTF-8 sequence.
        """
        with tempfile.NamedTemporaryFile(prefix="fn-chunks-", delete=False) as handle:
            for chunk in chunks:
                handle.write("{}\n".format(len(chunk)).encode("ascii"))
                handle.write(bytes(chunk))
            path = handle.name
        try:
            result = subprocess.run(
                [str(self.image), "--fn", "model", path, "-"], cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env=image_environment(), timeout=180, check=False)
            self.assertEqual(result.returncode, 0,
                             "model run failed: {}".format(result.stderr.decode("utf-8", "replace")))
            return result.stdout
        finally:
            os.unlink(path)

    def socket_bytes(self, chunks):
        """Serve one connection through the production native listener."""
        process = subprocess.Popen(
            [str(self.image), "--fn", "reader", "0", "1", "-"], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=image_environment())
        try:
            port = None
            while port is None:
                ready = select.select([process.stdout], [], [], 180)[0]
                self.assertTrue(ready, "native reader did not announce a port")
                line = process.stdout.readline()
                if not line:
                    self.fail("native reader exited: {}".format(
                        process.stderr.read().decode("utf-8", "replace")))
                if line.startswith(b"LISTENING "):
                    port = int(line.split()[1])
            received = []
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                for chunk in chunks:
                    if chunk:
                        client.sendall(bytes(chunk))
                client.shutdown(socket.SHUT_WR)
                client.settimeout(30)
                while True:
                    piece = client.recv(4096)
                    if not piece:
                        break
                    received.append(piece)
            self.assertEqual(process.wait(timeout=60), 0)
            return b"".join(received)
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
            process.stdout.close()
            process.stderr.close()

    def assertAgree(self, chunks):
        model = self.model_bytes(chunks)
        served = self.socket_bytes(chunks)
        self.assertEqual(served, model)
        return served

    def test_whole_transcript_agrees(self):
        served = self.assertAgree([MULTI_COMMAND])
        self.assertIn(b"211 1 1 1 fn.letters\r\n", served)

    def test_cut_inside_a_command_agrees(self):
        self.assertAgree([MULTI_COMMAND[:12], MULTI_COMMAND[12:]])

    def test_cut_after_a_reply_agrees(self):
        # The first chunk already earns the 211, so the cut falls inside the
        # reply stream as well as inside the next command.
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
