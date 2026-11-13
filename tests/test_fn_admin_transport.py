#!/usr/bin/env python3
"""Focused FNCT client transport/outcome tests (no node or ACL2 required)."""
from __future__ import annotations

import json
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
FN = str(ROOT / "fn")
CURSOR = (ROOT / "tests/fixtures/consumer-position/five-field-v1.fncu").read_bytes().hex()


class DisconnectAfterRequest(unittest.TestCase):
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
