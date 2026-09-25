#!/usr/bin/env python3
"""Standalone interoperability probe for fn's experimental CBOR profile.

This is deliberately outside the default unittest suite.  ACL2 receives only
fixed function calls whose data arguments are decimal octet lists; the driver
does not interpolate or evaluate Lisp forms supplied by a peer.
"""

from __future__ import annotations


def _heap_capped(environment):
    """The pool's heap cap (tools/acl2_slots.py) for an ACL2 this check starts."""
    import sys as _sys
    from pathlib import Path as _Path
    _sys.path.insert(0, str(_Path(__file__).resolve().parents[1] / "tools"))
    import acl2_slots
    return acl2_slots.apply_heap_cap(environment)

import argparse
import datetime as dt
import hashlib
import importlib.metadata
import io
import json
import os
from pathlib import Path
import platform
import re
import select
import shutil
import subprocess
import sys
import time
from typing import Any

try:
    import cbor2
except ImportError as error:  # pragma: no cover - exercised by the usage error
    cbor2 = None
    CBOR_IMPORT_ERROR = str(error)
else:
    CBOR_IMPORT_ERROR = None


ROOT = Path(__file__).resolve().parents[1]
BUILD_ROOT = ROOT / "build" / "cbor-interop"
PROMPT = b"ACL2 !>"
MAX_ACL2_OUTPUT = 4 * 1024 * 1024
MAX_ACL2_INPUT = 4 * 1024 * 1024
OCTET_LIST = re.compile(r"^\((?:\s*[0-9]+)*\s*\)$|^NIL$")
STATUS = re.compile(r"^:(?:OK|ERROR)(?:\s|$)")


class ProbeError(RuntimeError):
    pass


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def acl2_executable() -> Path | None:
    configured = os.environ.get("FN_ACL2", "acl2")
    if os.sep in configured:
        candidate = Path(configured).expanduser()
        return candidate.resolve() if candidate.is_file() and os.access(candidate, os.X_OK) else None
    found = shutil.which(configured)
    return Path(found).resolve() if found else None


def read_prompt(proc: subprocess.Popen[bytes], timeout: float = 30.0) -> bytes:
    output = b""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        ready, _, _ = select.select([proc.stdout], [], [], 0.1)
        if not ready:
            continue
        chunk = os.read(proc.stdout.fileno(), 4096)
        if not chunk:
            raise ProbeError("ACL2 exited before producing a prompt")
        output += chunk
        if len(output) > MAX_ACL2_OUTPUT:
            raise ProbeError("ACL2 bridge output exceeded the fixed bound")
        if output.rstrip().endswith(PROMPT):
            return output
    raise ProbeError("ACL2 prompt timeout")


def acl2_body(output: bytes) -> str:
    data = output.strip()
    if not data.endswith(PROMPT):
        raise ProbeError("ACL2 output did not end with its prompt")
    return data[: -len(PROMPT)].strip().decode("ascii", errors="strict")


def octet_literal(values: bytes | list[int], *, quote: bool = True) -> str:
    body = "(" + " ".join(str(value) for value in values) + ")"
    return "'" + body if quote else body


def octets_from_acl2(body: str) -> bytes:
    if not OCTET_LIST.fullmatch(body):
        raise ProbeError(f"ACL2 did not return an octet list: {body[:120]!r}")
    if body == "NIL":
        return b""
    values = [int(value) for value in body[1:-1].split()]
    if any(value > 255 for value in values):
        raise ProbeError("ACL2 returned a value outside the octet range")
    return bytes(values)


class ACL2:
    """A fixed-call ACL2 bridge following the existing store/reader discipline."""

    def __init__(self, executable: Path):
        environment = os.environ.copy()
        environment["ACL2_CUSTOMIZATION"] = "NONE"
        environment["ACL2_BOOK_HASH_ALISTP"] = "NIL"  # content-hashed certificates: relocatable across worktrees and hosts
        environment = _heap_capped(environment)
        environment.pop("ACL2_SYSTEM_BOOKS", None)
        self.proc = subprocess.Popen(
            [str(executable)], cwd=ROOT, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=environment,
        )
        try:
            read_prompt(self.proc)
            self.call('(include-book "books/cbor")')
            self.call('(include-book "books/records-attach")')
            self.version = self.call('(@ acl2-version)').strip().strip('"')
        except BaseException:
            self.close()
            raise

    def call(self, form: str) -> str:
        encoded = (form + "\n").encode("ascii")
        if len(encoded) > MAX_ACL2_INPUT:
            raise ProbeError("generated ACL2 call exceeds the fixed input bound")
        self.proc.stdin.write(encoded)
        self.proc.stdin.flush()
        output = read_prompt(self.proc)
        body = acl2_body(output)
        upper = body.upper()
        if "ACL2 ERROR" in upper or "HARD ACL2 ERROR" in upper:
            raise ProbeError(body)
        return body

    def close(self) -> None:
        if getattr(self, "proc", None) is None:
            return
        try:
            if self.proc.poll() is None and self.proc.stdin and not self.proc.stdin.closed:
                try:
                    self.proc.stdin.write(b"(quit)\n")
                    self.proc.stdin.flush()
                except (BrokenPipeError, OSError):
                    pass
            if self.proc.poll() is None:
                try:
                    self.proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    self.proc.terminate()
                    self.proc.wait(timeout=3)
        finally:
            for stream in (self.proc.stdin, self.proc.stdout):
                if stream and not stream.closed:
                    stream.close()

    def __enter__(self) -> "ACL2":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()

    def cbor_encode_uint(self, value: int) -> bytes:
        return octets_from_acl2(self.call(f"(fn-cbor-encode (cons :uint {value}))"))

    def cbor_encode_bytes(self, value: bytes) -> bytes:
        return octets_from_acl2(
            self.call(f"(fn-cbor-encode (cons :bytes {octet_literal(value)}))")
        )

    def cbor_decode_summary(self, encoded: bytes) -> dict[str, Any]:
        form = (
            f"(let ((r (fn-cbor-decode-exact {octet_literal(encoded)}))) "
            "(if (fn-cbor-result-okp r) "
            "(let ((v (fn-cbor-result-value r))) "
            "(if (equal (car v) :uint) (list :ok :uint (cdr v)) "
            "(list :ok :bytes (cdr v)))) "
            "(list :error (car (cdr r)))))"
        )
        body = self.call(form)
        if body.startswith("(:OK :UINT ") and body.endswith(")"):
            return {"status": "ok", "kind": "uint", "value": int(body[11:-1])}
        if body.startswith("(:OK :BYTES ") and body.endswith(")"):
            return {"status": "ok", "kind": "bytes", "value": list(octets_from_acl2(body[12:-1]))}
        if body.startswith("(:ERROR :") and body.endswith(")"):
            return {"status": "error", "reason": body[8:-1].lower()}
        raise ProbeError(f"unexpected ACL2 CBOR summary: {body!r}")

    def record_encode(self, fixture: str) -> bytes:
        return octets_from_acl2(self.call(f"(fn-record-encode {fixture})"))

    def record_decode_status(self, encoded: bytes) -> str:
        form = (
            f"(let ((r (fn-record-decode-exact {octet_literal(encoded)}))) "
            "(if (fn-record-result-okp r) :ok (car (cdr r))))"
        )
        return self.call(form).lower()


def value_summary(value: Any) -> dict[str, Any]:
    if isinstance(value, bytes):
        return {"type": "bytes", "length": len(value), "sha256": hashlib.sha256(value).hexdigest()}
    if isinstance(value, (int, float, str, bool)) or value is None:
        return {"type": type(value).__name__, "value": value}
    if isinstance(value, list):
        return {"type": "array", "length": len(value), "values": [value_summary(v) for v in value]}
    if isinstance(value, dict):
        return {"type": "map", "length": len(value)}
    return {"type": type(value).__name__, "repr": repr(value)}


def cbor2_decode_one(encoded: bytes) -> tuple[bool, Any, str | None]:
    try:
        return True, cbor2.loads(encoded), None
    except Exception as error:  # cbor2 exposes several decode error subclasses by version
        return False, None, f"{type(error).__name__}: {error}"


def cbor2_decode_sequence(encoded: bytes) -> tuple[bool, list[Any], str | None]:
    values: list[Any] = []
    stream = io.BytesIO(encoded)
    decoder = cbor2.CBORDecoder(stream)
    try:
        while stream.tell() < len(encoded):
            values.append(decoder.decode())
        return True, values, None
    except Exception as error:
        return False, values, f"{type(error).__name__}: {error}"


def primitive_case(acl2: ACL2, name: str, value: Any, encoded: bytes | None = None) -> dict[str, Any]:
    if encoded is None:
        encoded = cbor2.dumps(value)
    generic_ok, generic, generic_error = cbor2_decode_one(encoded)
    if isinstance(value, int) and value >= 0:
        fn_encoded = acl2.cbor_encode_uint(value)
    elif isinstance(value, bytes):
        fn_encoded = acl2.cbor_encode_bytes(value)
    else:
        fn_encoded = None
    fn_decode = acl2.cbor_decode_summary(encoded)
    expected_accept = isinstance(value, int) and 0 <= value <= 0xFFFFFFFF or (
        isinstance(value, bytes) and len(value) <= 0xFFFF
    )
    actual_accept = fn_decode["status"] == "ok"
    return {
        "name": name,
        "input": value_summary(value),
        "encoded_length": len(encoded),
        "encoded_sha256": hashlib.sha256(encoded).hexdigest(),
        "cbor2_decode": {"accepted": generic_ok, "value": value_summary(generic) if generic_ok else None,
                         "error": generic_error},
        "cbor2_encode_matches_input": cbor2.dumps(value) == encoded,
        "fn_encode_matches_cbor2": fn_encoded == encoded if fn_encoded is not None else None,
        "fn_decode": fn_decode,
        "expected_fn_acceptance": expected_accept,
        "passed": generic_ok and actual_accept == expected_accept and (
            fn_encoded == encoded if fn_encoded is not None and expected_accept else True
        ),
    }


def refusal_case(
    acl2: ACL2,
    name: str,
    encoded: bytes,
    *,
    generic_sequence: bool = False,
    generic_expected: bool = True,
) -> dict[str, Any]:
    if generic_sequence:
        generic_ok, values, generic_error = cbor2_decode_sequence(encoded)
        generic_value: Any = values
    else:
        generic_ok, generic_value, generic_error = cbor2_decode_one(encoded)
    fn_decode = acl2.cbor_decode_summary(encoded)
    return {
        "name": name,
        "encoded_length": len(encoded),
        "encoded_sha256": hashlib.sha256(encoded).hexdigest(),
        "cbor2_decode": {"accepted": generic_ok, "value": value_summary(generic_value) if generic_ok else None,
                         "error": generic_error, "sequence": generic_sequence},
        "fn_decode": fn_decode,
        "expected_fn_acceptance": False,
        "expected_generic_acceptance": generic_expected,
        "passed": generic_ok == generic_expected and fn_decode["status"] == "error",
    }


def record_case(acl2: ACL2, name: str, fixture: str, expected_values: list[Any]) -> dict[str, Any]:
    acl2_encoded = acl2.record_encode(fixture)
    generic_ok, decoded, generic_error = cbor2_decode_sequence(acl2_encoded)
    reencoded = b"".join(cbor2.dumps(value) for value in decoded) if generic_ok else b""
    independent_encoded = b"".join(cbor2.dumps(value) for value in expected_values)
    acl2_independent_status = acl2.record_decode_status(independent_encoded)
    return {
        "name": name,
        "acl2_record_length": len(acl2_encoded),
        "acl2_record_sha256": hashlib.sha256(acl2_encoded).hexdigest(),
        "cbor2_decodes_acl2_record": generic_ok and decoded == expected_values,
        "cbor2_reencode_matches_acl2": generic_ok and reencoded == acl2_encoded,
        "independent_cbor2_length": len(independent_encoded),
        "independent_cbor2_sha256": hashlib.sha256(independent_encoded).hexdigest(),
        "acl2_decodes_independent_record": acl2_independent_status,
        "cbor2_error": generic_error,
        "passed": generic_ok and decoded == expected_values and reencoded == acl2_encoded
        and acl2_independent_status == ":ok",
    }


def run_probe(acl2: ACL2) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    integer_values = (0, 23, 24, 255, 256, 65535, 65536, 0xFFFFFFFF)
    for value in integer_values:
        results.append(primitive_case(acl2, f"uint-{value}", value))

    byte_values = (
        b"",
        bytes(range(23)),
        bytes(range(24)),
        bytes((i % 256 for i in range(255))),
        bytes((i % 256 for i in range(256))),
        bytes((i % 256 for i in range(65535))),
    )
    for value in byte_values:
        results.append(primitive_case(acl2, f"bytes-{len(value)}", value))

    nonminimal = (
        ("nonminimal-uint-0", bytes.fromhex("1800")),
        ("nonminimal-uint-23", bytes.fromhex("1817")),
        ("nonminimal-uint-255", bytes.fromhex("1900ff")),
        ("nonminimal-bytes-0", bytes.fromhex("5800")),
        ("nonminimal-bytes-23", bytes.fromhex("5817") + bytes(range(23))),
        ("nonminimal-bytes-255", bytes.fromhex("5900ff") + bytes(range(255))),
    )
    for name, encoded in nonminimal:
        results.append(refusal_case(acl2, name, encoded))

    unsupported = (
        ("negative-integer", bytes.fromhex("20")),
        ("text-string", bytes.fromhex("6161")),
        ("array", bytes.fromhex("8101")),
        ("map", bytes.fromhex("a10001")),
        ("tag", bytes.fromhex("d903e801")),
        ("float16", bytes.fromhex("f90000")),
        ("indefinite-bytes", bytes.fromhex("5f4100ff")),
        ("uint-64-bit", bytes.fromhex("1b0000000100000000")),
    )
    for name, encoded in unsupported:
        results.append(refusal_case(acl2, name, encoded))

    truncated = (
        ("truncated-empty", b""),
        ("truncated-uint8", bytes.fromhex("18")),
        ("truncated-uint16", bytes.fromhex("1901")),
        ("truncated-bytes8", bytes.fromhex("5818") + bytes(range(23))),
        ("truncated-bytes16", bytes.fromhex("590100") + bytes(range(255))),
    )
    for name, encoded in truncated:
        results.append(refusal_case(acl2, name, encoded, generic_expected=False))

    oversized_bytes = bytes.fromhex("590000") + bytes((i % 256 for i in range(65536)))
    results.append(refusal_case(acl2, "bytes-65536-profile-limit", oversized_bytes))
    over_input = b"\x00" + (b"\x00" * 65538)
    results.append(refusal_case(acl2, "input-over-65538-profile-limit", over_input, generic_sequence=True))
    results.append(refusal_case(acl2, "trailing-second-item", b"\x00\x00", generic_sequence=True))

    record_values = [b"fn-r", 0, 1, 2, 3, b"<a>", b"\x09\x08", 1, b"g", b"o", b"s", b"e", 4]
    record_fixture = '(fn-record-make 1 2 3 "<a>" \'(9 8) \'("g") "o" "s" "e" 4 :legacy)'
    results.append(record_case(acl2, "schema0-record-one-group", record_fixture, record_values))
    stamped_values = [b"fn-r", 1, 1, 2, 3, b"<a>", b"\x09\x08", 1, b"g", b"o", b"s", b"e", 4, 5]
    stamped_fixture = '(fn-record-make 1 2 3 "<a>" \'(9 8) \'("g") "o" "s" "e" 4 5)'
    results.append(record_case(acl2, "schema1-record-one-group", stamped_fixture, stamped_values))
    empty_groups_values = [b"fn-r", 0, 0, 0, 0, b"<b>", b"", 0, b"o", b"s", b"e", 0]
    empty_groups_fixture = '(fn-record-make 0 0 0 "<b>" nil nil "o" "s" "e" 0 :legacy)'
    results.append(record_case(acl2, "schema0-record-empty-groups", empty_groups_fixture, empty_groups_values))

    return {
        "cases": results,
        "passed": all(case["passed"] for case in results),
        "case_count": len(results),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout-seconds", type=int, default=120)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")

    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = BUILD_ROOT / f"run-{stamp}-{os.getpid()}"
    run_dir.mkdir(parents=True, exist_ok=False)
    manifest: dict[str, Any] = {
        "status": "failed",
        "started_utc": stamp,
        "command": [sys.executable, *sys.argv],
        "timeout_seconds": args.timeout_seconds,
        "python": sys.version,
        "platform": platform.platform(),
        "source_digests_sha256": {
            "books/cbor.lisp": digest(ROOT / "books/cbor.lisp"),
            "books/records.lisp": digest(ROOT / "books/records.lisp"),
            "tests/interop_cbor.py": digest(Path(__file__).resolve()),
        },
    }
    if cbor2 is None:
        manifest["failure"] = "cbor2 is unavailable: " + (CBOR_IMPORT_ERROR or "unknown import error")
        (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        print(manifest["failure"], file=sys.stderr)
        return 2
    manifest["cbor2_version"] = importlib.metadata.version("cbor2")
    manifest["cbor2_module"] = str(Path(cbor2.__file__).resolve())
    executable = acl2_executable()
    if executable is None:
        manifest["failure"] = "ACL2 executable is unavailable"
        (run_dir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        print(manifest["failure"], file=sys.stderr)
        return 2
    manifest["acl2_executable"] = str(executable)
    manifest["acl2_executable_sha256"] = digest(executable)
    try:
        with ACL2(executable) as acl2:
            manifest["acl2_version"] = acl2.version
            outcome = run_probe(acl2)
            manifest.update(outcome)
    except (OSError, ProbeError, ValueError) as error:
        manifest["failure"] = f"{type(error).__name__}: {error}"
    manifest["status"] = "passed" if manifest.get("passed") else "failed"
    output = run_dir / "manifest.json"
    output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(f"CBOR interoperability: {manifest['status']}")
    print(f"Cases: {manifest.get('case_count', 0)}")
    print(f"Evidence: {output.relative_to(ROOT)}")
    if manifest.get("failure"):
        print(manifest["failure"], file=sys.stderr)
    return 0 if manifest["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
