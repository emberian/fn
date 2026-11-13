#!/usr/bin/env python3
"""Focused FNCT reply-codec tests against the declared result layouts."""
from __future__ import annotations

import json
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_admin  # noqa: E402

CURSOR = (ROOT / "tests/fixtures/consumer-position/five-field-v1.fncu").read_bytes()


def cns_reply(result: bytes) -> bytes:
    payload = b"\x00" + fn_admin.octets16(b"") + fn_admin.octets32(result)
    return fn_admin.fnct_seal(fn_admin.KIND_CNS_REPLY, payload)


def auth_reply(verb: str, result: bytes) -> bytes:
    payload = bytes([fn_admin.AUTH_OPCODES[verb], 0]) + fn_admin.octets16(b"") + result
    return fn_admin.fnct_seal(fn_admin.KIND_AUTH_REPLY, payload)


class ReplyDecoding(unittest.TestCase):
    def test_truncated_accepted_results_never_decode_as_accepted(self) -> None:
        for verb in ("register", "position", "ack", "status", "read", "wait", "append"):
            with self.subTest(verb=verb), self.assertRaises(fn_admin.WireError):
                fn_admin.decode_cns_reply(verb, cns_reply(b""))

    def test_ack_and_status_require_exact_fixed_results(self) -> None:
        ack = fn_admin.decode_cns_reply("ack", cns_reply(bytes(12)))
        self.assertEqual((ack["domain"], ack["position"]), (0, 0))
        status = fn_admin.decode_cns_reply("status", cns_reply(bytes(28)))
        self.assertEqual((status["position"], status["frontier"], status["gap"]), (0, 0, 0))
        for verb, result in (("ack", bytes(13)), ("status", bytes(29))):
            with self.subTest(verb=verb), self.assertRaises(fn_admin.WireError):
                fn_admin.decode_cns_reply(verb, cns_reply(result))

    def test_u32_request_fields_are_checked_before_encoding(self) -> None:
        cases = (
            ("read", {"cursor": b"x", "max_items": -1, "max_octets": 1}),
            ("read", {"cursor": b"x", "max_items": 1, "max_octets": 2**32}),
            ("wait", {"cursor": b"x", "max_items": 1, "max_octets": 1, "seconds": -1}),
            ("wait", {"cursor": b"x", "max_items": 1, "max_octets": 1, "seconds": 2**32}),
        )
        for verb, fields in cases:
            with self.subTest(verb=verb, fields=fields), self.assertRaises(ValueError):
                fn_admin.build_cns_request(verb, **fields)

    def test_truncated_authority_results_raise_wire_error(self) -> None:
        for verb in fn_admin.AUTH_OPCODES:
            with self.subTest(verb=verb), self.assertRaises(fn_admin.WireError):
                fn_admin.decode_auth_reply(verb, auth_reply(verb, b""))

    def test_empty_page_is_valid_and_length_exact(self) -> None:
        result = b"\x00" + fn_admin.octets16(CURSOR) + bytes(4) + fn_admin.octets32(b"")
        page = fn_admin.decode_cns_reply("read", cns_reply(result))
        self.assertEqual((page["outcome"], page["count"], page["next"]), ("accepted", 0, 5))
        with self.assertRaises(fn_admin.WireError):
            fn_admin.decode_cns_reply("read", cns_reply(result + b"\x00"))

    def test_truncated_item_fields_raise_wire_error_not_index_error(self) -> None:
        self.assertEqual(fn_admin.parse_cns_items(b""), [])
        for size in (1, 13, 14, 15, 16):
            with self.subTest(size=size), self.assertRaises(fn_admin.WireError):
                fn_admin.parse_cns_items(bytes(size))

    def test_invalid_booleans_and_evidence_are_rejected(self) -> None:
        page = b"\x02" + fn_admin.octets16(CURSOR) + bytes(4) + fn_admin.octets32(b"")
        with self.assertRaises(fn_admin.WireError):
            fn_admin.decode_cns_reply("read", cns_reply(page))
        append = (
            fn_admin.octets16(b"<a@b>") + bytes(12) + fn_admin.octets16(b"")
            + fn_admin.octets16(b"") + b"\xff"
        )
        with self.assertRaises(fn_admin.WireError):
            fn_admin.decode_cns_reply("append", cns_reply(append))
        auth = bytes([fn_admin.AUTH_OPCODES["grant-get"], 0]) + fn_admin.octets16(b"") + b"\x02\x00"
        with self.assertRaises(fn_admin.WireError):
            fn_admin.decode_auth_reply("grant-get", fn_admin.fnct_seal(fn_admin.KIND_AUTH_REPLY, auth))


class InvalidReplyOutcome(unittest.TestCase):
    def run_command(self, reply: bytes, *args: str, cursor_file: bool = False) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory) / "ctl.sock")
            ready = threading.Event()

            def serve() -> None:
                listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                try:
                    listener.bind(path)
                    listener.listen(1)
                    ready.set()
                    conn, _ = listener.accept()
                    with conn:
                        conn.recv(65536)
                        try:
                            conn.sendall(reply)
                        except BrokenPipeError:
                            # A local usage error closes without waiting for a reply.
                            pass
                finally:
                    listener.close()

            thread = threading.Thread(target=serve)
            thread.start()
            self.assertTrue(ready.wait(5))
            proc = subprocess.run(
                [str(ROOT / "fn"), *args, "--control-sock", path, "--json"]
                + (["--cursor-file", str(Path(directory) / "cursor")] if cursor_file else []),
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                timeout=10,
            )
            thread.join(5)
            self.assertFalse(thread.is_alive())
            return proc

    def test_invalid_mutating_reply_is_uncertain(self) -> None:
        for args in (
            ("stream", "register"),
            ("stream", "ack", "6", "--cursor", CURSOR.hex()),
            ("stream", "append", "--group", "local.test", "--body", "hello", "--op", "1"),
        ):
            with self.subTest(args=args):
                proc = self.run_command(cns_reply(b""), *args)
                self.assertEqual(proc.returncode, 3, (proc.stdout, proc.stderr))
                self.assertEqual(json.loads(proc.stdout)["outcome"], "uncertain")

    def test_invalid_read_only_reply_is_local_error(self) -> None:
        proc = self.run_command(
            cns_reply(b""), "stream", "read", "--cursor", CURSOR.hex()
        )
        self.assertEqual(proc.returncode, 2, (proc.stdout, proc.stderr))
        self.assertEqual(json.loads(proc.stdout)["outcome"], "error")

    def test_invalid_principal_create_reply_is_uncertain(self) -> None:
        proc = self.run_command(
            auth_reply("principal-create", b""), "principal", "create", "alice"
        )
        self.assertEqual(proc.returncode, 3, (proc.stdout, proc.stderr))
        self.assertEqual(json.loads(proc.stdout)["outcome"], "uncertain")

    def test_accepted_ack_survives_lost_cursor_refresh(self) -> None:
        receipt = bytes(4) + (6).to_bytes(8, "big")
        proc = self.run_command(
            cns_reply(receipt), "stream", "ack", "6", "--cursor", CURSOR.hex(),
            cursor_file=True,
        )
        self.assertEqual(proc.returncode, 0, (proc.stdout, proc.stderr))
        decoded = json.loads(proc.stdout)
        self.assertEqual(decoded["outcome"], "accepted")
        self.assertEqual(decoded["position"], 6)
        self.assertIn("cursor_refresh_error", decoded)

    def test_negative_limit_is_local_usage_error(self) -> None:
        proc = self.run_command(
            cns_reply(b""), "stream", "read", "--cursor", CURSOR.hex(), "--max-items", "-1"
        )
        self.assertEqual(proc.returncode, 2, (proc.stdout, proc.stderr))
        self.assertEqual(proc.stderr, "")
        self.assertEqual(json.loads(proc.stdout)["outcome"], "error")


if __name__ == "__main__":
    unittest.main()
