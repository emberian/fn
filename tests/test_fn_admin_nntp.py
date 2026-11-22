#!/usr/bin/env python3
"""Socket-level NNTP response and outcome tests for the fn CLI."""
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
                    if not opening.endswith(b"\r\n"):
                        conn.shutdown(socket.SHUT_WR)
                        self.assertEqual(conn.recv(4096), b"")
                    elif opening.startswith(b"340 "):
                        while b"\r\n.\r\n" not in data:
                            chunk = conn.recv(4096)
                            self.assertTrue(chunk)
                            data += chunk
                        conn.sendall(reply)
                        if not reply.endswith(b"\r\n"):
                            conn.shutdown(socket.SHUT_WR)
                            self.assertEqual(conn.recv(4096), b"")
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

    def test_incomplete_invitation_is_an_error_before_sending_any_body(self) -> None:
        for opening in (b"", b"340 send article"):
            with self.subTest(opening=opening):
                proc = self.post_with_reply(b"", opening=opening)
                self.assertEqual(proc.returncode, 2, (proc.stdout, proc.stderr))
                self.assertEqual(json.loads(proc.stdout)["outcome"], "error")

    def test_incomplete_final_reply_cannot_settle_post(self) -> None:
        for reply in (b"", b"240 received", b"240 received\n", b"441 posting failed"):
            with self.subTest(reply=reply):
                proc = self.post_with_reply(reply)
                self.assertEqual(proc.returncode, 3, (proc.stdout, proc.stderr))
                self.assertEqual(json.loads(proc.stdout)["outcome"], "uncertain")

    def test_unexpected_complete_reply_cannot_settle_post(self) -> None:
        for reply in (b"340 send another article\r\n", b"205 closing connection\r\n"):
            with self.subTest(reply=reply):
                proc = self.post_with_reply(reply)
                self.assertEqual(proc.returncode, 3, (proc.stdout, proc.stderr))
                self.assertEqual(json.loads(proc.stdout)["outcome"], "uncertain")


class ReaderOutcome(unittest.TestCase):
    def test_complete_command_specific_replies(self) -> None:
        article = ("article", "<one@example.invalid>")
        head = (*article, "--head")
        for command, request, response, outcome, code in (
            (("groups",), b"LIST ACTIVE", b"", "error", 2),
            (("groups",), b"LIST ACTIVE", b"502 denied\r\n", "refused", 1),
            (("groups",), b"LIST ACTIVE", b"215 list\r\nlocal.test 1 1 y\r\n.\r\n", "accepted", 0),
            (("article", "local.test", "1"), b"GROUP local.test", b"411 no group", "error", 2),
            (article, b"ARTICLE <one@example.invalid>", b"221 1 <one@example.invalid>\r\n.\r\n", "error", 2),
            (head, b"HEAD <one@example.invalid>", b"220 1 <one@example.invalid>\r\n.\r\n", "error", 2),
            (head, b"HEAD <one@example.invalid>", b"221 1 <one@example.invalid>\r\n.\r\n", "accepted", 0),
            (article, b"ARTICLE <one@example.invalid>", b"220 0 <other@example.invalid>\r\nwrong\r\n.\r\n", "error", 2),
            (head, b"HEAD <one@example.invalid>", b"221 headers follow\r\n.\r\n", "error", 2),
            (article, b"ARTICLE <one@example.invalid>", b"220 0 <one@example.invalid> article follows\r\nbody\r\n.\r\n", "accepted", 0),
            (article, b"ARTICLE <one@example.invalid>", b"220 1 <one@example.invalid>\r\npartial\n.\r\n", "error", 2),
        ):
            with self.subTest(command=command, response=response), socket.create_server(("127.0.0.1", 0)) as listener:
                listener.settimeout(5)
                port = listener.getsockname()[1]
                with subprocess.Popen([str(ROOT / "fn"), *command, "--port", str(port), "--json"],
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE) as proc:
                    conn, _ = listener.accept()
                    with conn, conn.makefile("rb") as reader:
                        conn.settimeout(5)
                        conn.sendall(b"200 fn ready\r\n")
                        self.assertEqual(reader.readline(), request + b"\r\n")
                        conn.sendall(response)
                        conn.shutdown(socket.SHUT_WR)
                        stdout, stderr = proc.communicate(timeout=5)
                    self.assertEqual((proc.returncode, json.loads(stdout)["outcome"]), (code, outcome), stderr)

    def test_number_is_bound_to_the_selected_group(self):
        for selected, number, expected in (("other.group", 1, 2), ("local.test", 2, 2),
                                           ("local.test", 1, 0)):
            with self.subTest(selected=selected, number=number), socket.create_server(("127.0.0.1", 0)) as listener:
                listener.settimeout(5)
                with subprocess.Popen(
                    [str(ROOT / "fn"), "article", "local.test", "1", "--port",
                     str(listener.getsockname()[1]), "--json"], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                ) as proc:
                    conn, _ = listener.accept()
                    with conn, conn.makefile("rb") as reader:
                        conn.settimeout(5)
                        conn.sendall(b"200 fn ready\r\n")
                        self.assertEqual(reader.readline(), b"GROUP local.test\r\n")
                        conn.sendall(f"211 2 1 2 {selected}\r\n".encode())
                        if selected == "local.test":
                            self.assertEqual(reader.readline(), b"ARTICLE 1\r\n")
                            conn.sendall(f"220 {number} <returned@example.invalid>\r\nbody\r\n.\r\n".encode())
                        conn.shutdown(socket.SHUT_WR)
                        if selected != "local.test":
                            self.assertIn(reader.readline(), (b"QUIT\r\n", b""))
                        output, err = proc.communicate(timeout=5)
                    reply = json.loads(output)
                    self.assertEqual(proc.returncode, expected, (reply, err))
                    if expected:
                        self.assertNotIn("text", reply)



class EndpointValidation(unittest.TestCase):
    def test_out_of_range_port_is_local_error(self) -> None:
        for port in ("-1", "0", "65536"):
            with self.subTest(port=port):
                proc = subprocess.run(
                    [str(ROOT / "fn"), "groups", "--port", port, "--json"],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    timeout=10,
                )
                self.assertEqual(proc.returncode, 2, (proc.stdout, proc.stderr))
                self.assertEqual(proc.stderr, "")
                self.assertEqual(json.loads(proc.stdout)["outcome"], "error")


if __name__ == "__main__":
    unittest.main()
