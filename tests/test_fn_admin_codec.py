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


def cns_reply(result: bytes, outcome: str = "accepted", reason: bytes = b"") -> bytes:
    payload = bytes([fn_admin.CLASSES.index(outcome)]) + fn_admin.octets16(reason) + fn_admin.octets32(result)
    return fn_admin.fnct_seal(fn_admin.KIND_CNS_REPLY, payload)


def auth_reply(verb: str, result: bytes) -> bytes:
    payload = bytes([fn_admin.AUTH_OPCODES[verb], 0]) + fn_admin.octets16(b"") + result
    return fn_admin.fnct_seal(fn_admin.KIND_AUTH_REPLY, payload)


class ReplyDecoding(unittest.TestCase):
    def test_cursor_layout_preserves_consumer_octets_and_version_width(self) -> None:
        ids = b"".join(fn_admin.octets_var(value) for value in
                       (b"history", b"inc", b"consumer", b"principal", b"query"))
        for version, tail_size, width in ((1, 16, 4), (2, 36, 8)):
            with self.subTest(version=version):
                prefix = b"fncu" + bytes([version]) + ids + bytes(tail_size - width)
                position = (1 << (8 * width)) - 1
                cursor = prefix + bytes(width)
                self.assertEqual(fn_admin.cursor_consumer_and_position_width(cursor), (b"consumer", width))
                changed = fn_admin.cursor_propose(cursor, position)
                self.assertEqual(changed, prefix + position.to_bytes(width, "big"))
                self.assertEqual(fn_admin.cursor_position(changed), position)
                for malformed in (cursor[:-1], cursor + b"\x00", cursor[:5] + b"\x41" + cursor[6:]):
                    with self.assertRaises(fn_admin.WireError):
                        fn_admin.cursor_position(malformed)

    def test_truncated_accepted_results_never_decode_as_accepted(self) -> None:
        for verb in ("register", "rebase", "position", "ack", "status", "read", "wait", "append", "fetch"):
            with self.subTest(verb=verb), self.assertRaises(fn_admin.WireError):
                fn_admin.decode_cns_reply(verb, cns_reply(b""))

    def test_rebase_sends_issued_cursor_and_decodes_replacement(self) -> None:
        for start, tag in (("keep", b"\x00"), ("history", b"\x02")):
            with self.subTest(start=start):
                request = fn_admin.build_cns_request("rebase", cursor=CURSOR, start=start)
                kind, body = fn_admin.fnct_open(request)
                self.assertEqual(kind, fn_admin.KIND_CNS_REQ)
                self.assertEqual(body, b"\x0c" + fn_admin.octets16(CURSOR) + bytes(2) + tag)
        replacement = fn_admin.cursor_propose(CURSOR, 0)
        result = fn_admin.decode_cns_reply("rebase", cns_reply(replacement))
        self.assertEqual((result["outcome"], result["position"], result["cursor"]),
                         ("accepted", 0, replacement.hex()))

    def test_fetch_canonical_widths_and_exact_binary_reply(self) -> None:
        mid = b"<fetch@example.invalid>"
        position = 0x123456789ABCDEF0
        frame = fn_admin.build_cns_request("fetch", message_id=mid, domain=0x12345678, position=position)
        kind, body = fn_admin.fnct_open(frame)
        self.assertEqual(kind, fn_admin.KIND_CNS_REQ)
        self.assertEqual(body, b"\x0d" + len(mid).to_bytes(2, "big") + mid
                         + bytes.fromhex("12345678123456789abcdef0"))
        article = b"Header: octets\r\n\r\n\x00\xff.dot\r\n"
        result = fn_admin.decode_cns_reply("fetch", cns_reply(fn_admin.octets32(article)))
        self.assertEqual(bytes.fromhex(result["article_hex"]), article)
        self.assertEqual(result["octets"], len(article))
        for malformed in (b"", b"\x00\x00\x00", fn_admin.octets32(article)[:-1],
                          fn_admin.octets32(article) + b"x"):
            with self.assertRaises(fn_admin.WireError):
                fn_admin.decode_cns_reply("fetch", cns_reply(malformed))
        for domain, pos in ((-1, 0), (2**32, 0), (0, -1), (0, 2**64)):
            with self.assertRaises(ValueError):
                fn_admin.build_cns_request("fetch", message_id=mid, domain=domain, position=pos)

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

    def test_read_and_wait_preserve_record_octets_and_reference_tag(self) -> None:
        # Both bodies render to the same replacement character in the text preview.
        articles = [b"a\xff\r\n", b"a\xfe\r\n"]
        digest = bytes(range(32))
        bodies = [(0, article) for article in articles]
        bodies.append((2, (6144).to_bytes(8, "big") + b"\x01" + digest))
        items = b"".join(
            bytes([kind]) + bytes(4) + n.to_bytes(8, "big") + b"\x00"
            + fn_admin.octets16(b"") + fn_admin.octets16(b"<item@test>") + fn_admin.octets32(body)
            for n, (kind, body) in enumerate(bodies, start=1)
        )
        payload = b"\x00" + fn_admin.octets16(CURSOR) + len(bodies).to_bytes(4, "big") + fn_admin.octets32(items)
        for verb in ("read", "wait"):
            with self.subTest(verb=verb):
                first, second, ref = fn_admin.decode_cns_reply(verb, cns_reply(payload))["items"]
                self.assertEqual(first["text"], second["text"])
                self.assertEqual([bytes.fromhex(item["article_hex"]) for item in (first, second)], articles)
                self.assertEqual((ref["octets"], ref["content_tag"], ref["content"]), (6144, 1, digest.hex()))

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
    def run_command(self, reply: bytes, *args: str, cursor_file: bool = False,
                    json_output: bool = True, position_reply: bytes | None = None,
                    position_consumer: bytes | None = None) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory) / "ctl.sock")
            ready = threading.Event()
            refresh_requests = []

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
                            if position_reply is not None:
                                conn.settimeout(5)
                                with conn.makefile("rb") as stream:
                                    header = stream.read(10)
                                    if header:
                                        length = fn_admin.fnct_payload_length(header)
                                        refresh_requests.append(header + stream.read(length + 32))
                                        conn.sendall(position_reply)
                        except BrokenPipeError:
                            # A local usage error closes without waiting for a reply.
                            pass
                finally:
                    listener.close()

            thread = threading.Thread(target=serve)
            thread.start()
            self.assertTrue(ready.wait(5))
            proc = subprocess.run(
                [str(ROOT / "fn"), *args, "--control-sock", path] + (["--json"] if json_output else [])
                + (["--cursor-file", str(Path(directory) / "cursor")] if cursor_file else []),
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=json_output,
                timeout=10,
            )
            thread.join(5)
            self.assertFalse(thread.is_alive())
            if position_consumer is not None:
                self.assertEqual(refresh_requests, [fn_admin.build_cns_request(
                    "position", consumer=position_consumer)])
            return proc

    def test_fetch_cli_preserves_binary_and_rejects_truncation(self) -> None:
        article = b"From: a@example.invalid\r\n\r\n\xff\x00.dot\r\n"
        args = ("stream", "fetch", "<fetch@example.invalid>", "--domain", "0", "--position", "4294967297")
        raw = self.run_command(cns_reply(fn_admin.octets32(article)), *args, json_output=False)
        self.assertEqual((raw.returncode, raw.stdout), (0, article), raw.stderr)
        encoded = self.run_command(cns_reply(fn_admin.octets32(article)), *args)
        self.assertEqual(encoded.returncode, 0, encoded.stderr)
        self.assertEqual(bytes.fromhex(json.loads(encoded.stdout)["article_hex"]), article)
        bad = self.run_command(cns_reply(fn_admin.octets32(article)[:-1]), *args)
        self.assertEqual(bad.returncode, 2, bad.stderr)
        self.assertEqual(json.loads(bad.stdout)["outcome"], "error")

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

    def test_conflict_reports_evidence_separately_from_article_refusal(self) -> None:
        args = ("stream", "append", "--group", "local.test", "--body", "hello", "--op", "71")
        mid = b"<conflict@example.invalid>"
        def result(evidence, event, identity=mid, numbers=b"", receipt=b""):
            return (fn_admin.octets16(identity) + bytes(4) + event.to_bytes(8, "big")
                    + fn_admin.octets16(numbers) + fn_admin.octets16(receipt)
                    + bytes([fn_admin.EVIDENCE_TYPES.index(evidence)]))

        for evidence, event in (("committed", 4294967297), ("uncertain", 0), ("refused", 0)):
            with self.subTest(evidence=evidence):
                detail = result(evidence, event)
                proc = self.run_command(cns_reply(detail, "refused", b"conflict"), *args)
                self.assertEqual(proc.returncode, 1, proc.stdout)
                self.assertEqual(json.loads(proc.stdout), dict(outcome="refused", reason="conflict",
                                 message_id=mid.decode(), domain=0, position=event, numbers="",
                                 receipt="", evidence=evidence, op=71))
        detail = result("committed", 71)
        for invalid, reason in ((b"", b"conflict"), (detail[:-1], b"conflict"),
                                (result("none", 0), b"conflict"), (result("committed", 0), b"conflict"),
                                (result("refused", 71), b"conflict"), (result("committed", 71, b""), b"conflict"),
                                (result("committed", 71, numbers=b"x"), b"conflict"),
                                (result("committed", 71, receipt=b"x"), b"conflict"),
                                (detail, b"operation-reused")):
            with self.subTest(detail=invalid, reason=reason):
                proc = self.run_command(cns_reply(invalid, "refused", reason), *args)
                self.assertEqual(proc.returncode, 3, proc.stdout)
                self.assertEqual(json.loads(proc.stdout)["op"], 71)

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

    def test_local_cursor_write_failure_preserves_accepted_register_and_ack(self) -> None:
        position = cns_reply(CURSOR)
        ack = cns_reply(bytes(4) + (6).to_bytes(8, "big"))
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "exists-as-directory"
            target.mkdir()
            for args, reply, refresh in ((("register", "--consumer", "reader"), position, None),
                                         (("ack", "6", "--cursor", CURSOR.hex()), ack, position)):
                with self.subTest(command=args[0]):
                    proc = self.run_command(reply, "stream", *args, "--cursor-file", str(target),
                                            position_reply=refresh,
                                            position_consumer=b"\x03" if refresh else None)
                    self.assertEqual(proc.returncode, 0, (proc.stdout, proc.stderr))
                    receipt = json.loads(proc.stdout)
                    self.assertEqual(receipt["outcome"], "accepted")
                    self.assertEqual(receipt["cursor"], CURSOR.hex())
                    self.assertIn("cursor_file_error", receipt)
                    self.assertEqual(list(Path(directory).iterdir()), [target])
                    self.assertTrue(target.is_dir())

    def test_register_replaces_local_cursor_with_private_issued_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "cursor"
            target.write_text("old\n", encoding="ascii")
            proc = self.run_command(cns_reply(CURSOR), "stream", "register", "--consumer",
                                    "reader", "--cursor-file", str(target))
            self.assertEqual(proc.returncode, 0, (proc.stdout, proc.stderr))
            self.assertNotIn("cursor_file_error", json.loads(proc.stdout))
            self.assertEqual(target.read_text(encoding="ascii"), CURSOR.hex() + "\n")
            self.assertEqual(target.stat().st_mode & 0o777, 0o600)

    def test_negative_limit_is_local_usage_error(self) -> None:
        proc = self.run_command(
            cns_reply(b""), "stream", "read", "--cursor", CURSOR.hex(), "--max-items", "-1"
        )
        self.assertEqual(proc.returncode, 2, (proc.stdout, proc.stderr))
        self.assertEqual(proc.stderr, "")
        self.assertEqual(json.loads(proc.stdout)["outcome"], "error")


if __name__ == "__main__":
    unittest.main()
