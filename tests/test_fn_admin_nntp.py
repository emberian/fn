#!/usr/bin/env python3
"""Socket-level NNTP POST outcome tests for the fn CLI."""
from __future__ import annotations

import json
from pathlib import Path
import socket
import subprocess
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]


class PostOutcome(unittest.TestCase):
    def post_with_reply(self, reply: bytes, opening: bytes = b"340 send article to be posted\r\n"):
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        port = listener.getsockname()[1]
        errors = []

        def serve() -> None:
            try:
                conn, _ = listener.accept()
                with conn:
                    conn.settimeout(5)
                    conn.sendall(b"200 fn ready\r\n")
                    data = b""
                    while b"POST\r\n" not in data:
                        chunk = conn.recv(4096)
                        self.assertTrue(chunk)
                        data += chunk
                    conn.sendall(opening)
                    if opening.startswith(b"340 "):
                        while b"\r\n.\r\n" not in data:
                            chunk = conn.recv(4096)
                            self.assertTrue(chunk)
                            data += chunk
                        conn.sendall(reply)
            except BaseException as exc:
                errors.append(exc)
            finally:
                listener.close()

        thread = threading.Thread(target=serve)
        thread.start()
        proc = subprocess.run(
            [str(ROOT / "fn"), "post", "local.test", "--body", "hello", "--port", str(port), "--json"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=10,
        )
        thread.join(6)
        self.assertFalse(thread.is_alive())
        if errors:
            raise errors[0]
        return proc

    def assert_outcome(self, reply: bytes, outcome: str, code: int) -> None:
        proc = self.post_with_reply(reply)
        self.assertEqual(proc.returncode, code, (proc.stdout, proc.stderr))
        decoded = json.loads(proc.stdout)
        self.assertEqual(decoded["outcome"], outcome)
        self.assertEqual(decoded["status"], reply.decode("latin-1").rstrip("\r\n"))

    def test_accepted_post(self) -> None:
        self.assert_outcome(b"240 article received OK\r\n", "accepted", 0)

    def test_ordinary_441_is_refused(self) -> None:
        self.assert_outcome(
            b"441 posting failed; this article is already stored here\r\n", "refused", 1
        )

    def test_uncertain_441_is_uncertain(self) -> None:
        self.assert_outcome(
            b"441 posting failed; the outcome is uncertain, do not repost\r\n", "uncertain", 3
        )

    def test_uncertain_403_after_body_is_uncertain(self) -> None:
        self.assert_outcome(
            b"403 internal fault; the posting session is malformed\r\n", "uncertain", 3
        )

    def test_uncertain_403_before_body_is_uncertain(self) -> None:
        proc = self.post_with_reply(
            b"", opening=b"403 internal fault; the posting session is malformed\r\n"
        )
        self.assertEqual(proc.returncode, 3, (proc.stdout, proc.stderr))
        self.assertEqual(json.loads(proc.stdout)["outcome"], "uncertain")


if __name__ == "__main__":
    unittest.main()
