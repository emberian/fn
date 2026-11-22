#!/usr/bin/env python3
"""Focused FNCT client transport/outcome tests (no node or ACL2 required)."""
from __future__ import annotations

from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
FN = str(ROOT / "fn")
sys.path.insert(0, str(ROOT / "tools"))
import fn_admin

CURSOR = (ROOT / "tests/fixtures/consumer-position/five-field-v1.fncu").read_bytes().hex()


class DisconnectAfterRequest(unittest.TestCase):
    def test_large_reply_is_read_in_bounded_blocks(self) -> None:
        payload = bytes(range(256)) * 769
        frame = fn_admin.fnct_seal(fn_admin.KIND_CNS_REPLY, payload)
        source = io.BytesIO(frame)
        with patch.object(fn_admin.socket, "socket") as sockets:
            recv = sockets.return_value.recv
            recv.side_effect = source.read
            with fn_admin.ControlSession("unused.sock") as session:
                self.assertEqual(session._recv_frame(), frame)
            self.assertGreater(len(recv.call_args_list), 3)
            self.assertLessEqual(max(call.args[0] for call in recv.call_args_list), 64 * 1024)

    def test_unsupported_frame_version_stops_at_header(self) -> None:
        with patch.object(fn_admin.socket, "socket") as sockets:
            recv = sockets.return_value.recv
            recv.return_value = b"FNCT\x02\x1c" + (1024).to_bytes(4, "big")
            with fn_admin.ControlSession("unused.sock") as session, self.assertRaises(fn_admin.WireError):
                session._recv_frame()
            recv.assert_called_once_with(10)

    def test_transport_failure_boundary(self) -> None:
        append = ["stream", "append", "--group", "local.test", "--body", "hello", "--op", "17"]
        cases = [
            (append, "sendall", BrokenPipeError(), 3),
            (append, "recv", OSError("connection lost"), 3),
            (["principal", "create", "alice"], "sendall", TimeoutError(), 3),
            (["stream", "status"], "sendall", BrokenPipeError(), 2),
            (append, "connect", ConnectionRefusedError(), 2),
        ]
        for args, method, failure, expected in cases:
            with self.subTest(args=args, method=method), patch.object(fn_admin.socket, "socket") as socket_cls:
                getattr(socket_cls.return_value, method).side_effect = failure
                output = io.StringIO()
                with redirect_stdout(output):
                    rc = fn_admin.main([*args, "--control-sock", "unused.sock", "--json"], root=ROOT)
                self.assertEqual(rc, expected)
                answer = json.loads(output.getvalue())
                self.assertEqual(answer["outcome"], "uncertain" if expected == 3 else "error")
                if args == append and expected == 3:
                    self.assertEqual(answer["op"], 17)

    def run_command(self, *args: str) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory) / "ctl.sock")
            ready = threading.Event()
            errors = []

            def serve() -> None:
                try:
                    listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                    listener.bind(path)
                    listener.listen(1)
                    ready.set()
                    conn, _ = listener.accept()
                    with conn:
                        conn.recv(65536)
                    listener.close()
                except BaseException as exc:  # surface thread failures in the test
                    errors.append(exc)
                    ready.set()

            thread = threading.Thread(target=serve)
            thread.start()
            self.assertTrue(ready.wait(5), "mock listener did not start")
            proc = subprocess.run(
                [FN, *args, "--control-sock", path, "--json"],
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                timeout=10,
            )
            thread.join(5)
            self.assertFalse(thread.is_alive(), "mock server did not exit")
            if errors:
                raise errors[0]
            return proc

    def assert_uncertain(self, proc: subprocess.CompletedProcess) -> None:
        self.assertEqual(proc.returncode, 3, (proc.stdout, proc.stderr))
        self.assertEqual(proc.stderr, "")
        self.assertEqual(json.loads(proc.stdout)["outcome"], "uncertain")

    def test_principal_create_disconnect_is_uncertain(self) -> None:
        self.assert_uncertain(self.run_command("principal", "create", "alice"))

    def test_stream_register_disconnect_is_uncertain(self) -> None:
        self.assert_uncertain(self.run_command("stream", "register"))

    def test_stream_ack_disconnect_is_uncertain(self) -> None:
        self.assert_uncertain(self.run_command("stream", "ack", "6", "--cursor", CURSOR))

    def test_grant_set_disconnect_remains_uncertain_with_op(self) -> None:
        proc = self.run_command("grant", "set", "1", "consume", "--op", "1")
        self.assert_uncertain(proc)
        self.assertEqual(json.loads(proc.stdout)["op"], 1)

    def test_stream_append_disconnect_remains_uncertain_with_op(self) -> None:
        proc = self.run_command(
            "stream", "append", "--group", "local.test", "--body", "hello", "--op", "1"
        )
        self.assert_uncertain(proc)
        self.assertEqual(json.loads(proc.stdout)["op"], 1)


if __name__ == "__main__":
    unittest.main()
