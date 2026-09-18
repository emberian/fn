"""Bounded local HTTP client for pinned dtn7-rs BPA observations.

This client is intentionally transport-only.  `download_bundle` returns the
opaque BP bundle bytes produced by dtn7-rs `/download`; it does not decode BP,
extract an ADU, accept an article, or issue a receipt.  The supported pinned
HTTP routes use the raw query form `/download?<BID>` and `/delete?<BID>`.
"""
from __future__ import annotations

from dataclasses import dataclass
import http.client
import json
import socket
from typing import Callable
from urllib.parse import quote

PINNED_DTN7_REVISION = "4daf02d7ea927e9293753b2a5c4497457f6e5a40"
PINNED_DTN7_VERSION = "0.21.0"
LOCAL_HOST = "::1"
DEFAULT_TIMEOUT_SECONDS = 2.0
MAX_TIMEOUT_SECONDS = 30.0
MAX_BID_BYTES = 512
MAX_INVENTORY_COUNT = 8192
# 8,192 quoted BIDs of 512 bytes plus JSON punctuation fits below this cap.
MAX_INVENTORY_RESPONSE_BYTES = 4 * 1024 * 1024 + 16 * 1024
# fn's isolated ingress admits at most 32 KiB of legacy article ADU.  This
# leaves bounded BP framing headroom without claiming a general BPA limit.
DEFAULT_MAX_BUNDLE_BYTES = 64 * 1024
MAX_ERROR_RESPONSE_BYTES = 4096
_READ_CHUNK_BYTES = 8192


class BpaDtn7Error(RuntimeError):
    """A local BPA I/O or response-boundary failure."""


class BpaDtn7Timeout(BpaDtn7Error):
    pass


class BpaDtn7ResponseTooLarge(BpaDtn7Error):
    pass


class BpaDtn7ProtocolError(BpaDtn7Error):
    pass


@dataclass(frozen=True)
class BpaDtn7HttpError(BpaDtn7Error):
    status: int
    operation: str
    detail: bytes = b""

    def __str__(self) -> str:
        suffix = f" ({self.detail.decode('utf-8', 'replace')})" if self.detail else ""
        return f"dtn7-rs {self.operation} returned HTTP {self.status}{suffix}"


def _bounded_visible_ascii(value: str, label: str) -> str:
    if not isinstance(value, str):
        raise BpaDtn7ProtocolError(f"{label} is not text")
    try:
        raw = value.encode("ascii", "strict")
    except UnicodeEncodeError as error:
        raise BpaDtn7ProtocolError(f"{label} is not ASCII") from error
    if not 1 <= len(raw) <= MAX_BID_BYTES or any(byte < 33 or byte > 126 for byte in raw):
        raise BpaDtn7ProtocolError(f"{label} is outside the bounded local profile")
    return value


def _raw_query_bid(bid: str) -> str:
    """Encode a raw-query BID without allowing query delimiter injection.

    Pinned dtn7-rs handlers use Axum `RawQuery`, so ordinary dtn BIDs retain
    URI structural characters (`:`, `/`, `@`) while unsafe query delimiters are
    percent encoded.  A BID containing such an encoded delimiter may be refused
    by this upstream revision, but it can never alter the requested operation.
    """
    return quote(_bounded_visible_ascii(bid, "BPA BID"), safe=":/@-._~")


class BpaDtn7Client:
    """Loopback-only bounded BPA inventory, bundle download, and delete client."""

    def __init__(self, port: int, *, host: str = LOCAL_HOST,
                 timeout_seconds: float = DEFAULT_TIMEOUT_SECONDS,
                 max_bundle_bytes: int = DEFAULT_MAX_BUNDLE_BYTES,
                 connection_factory: Callable[..., http.client.HTTPConnection] = http.client.HTTPConnection):
        if host != LOCAL_HOST:
            raise BpaDtn7ProtocolError("experimental BPA client permits only ::1")
        if not isinstance(port, int) or isinstance(port, bool) or not 1 <= port <= 65535:
            raise BpaDtn7ProtocolError("BPA port is outside range")
        if (not isinstance(timeout_seconds, (int, float)) or isinstance(timeout_seconds, bool) or
                not 0 < timeout_seconds <= MAX_TIMEOUT_SECONDS):
            raise BpaDtn7ProtocolError("BPA timeout is outside the local profile")
        if (not isinstance(max_bundle_bytes, int) or isinstance(max_bundle_bytes, bool) or
                not 1 <= max_bundle_bytes <= MAX_INVENTORY_RESPONSE_BYTES):
            raise BpaDtn7ProtocolError("BPA bundle cap is outside the local profile")
        self.port = port
        self.host = host
        self.timeout_seconds = float(timeout_seconds)
        self.max_bundle_bytes = max_bundle_bytes
        self._connection_factory = connection_factory

    def _read_bounded(self, response: http.client.HTTPResponse, limit: int) -> bytes:
        header = response.getheader("Content-Length")
        if header is not None:
            try:
                declared = int(header, 10)
            except ValueError as error:
                raise BpaDtn7ProtocolError("BPA response has invalid Content-Length") from error
            if declared < 0:
                raise BpaDtn7ProtocolError("BPA response has negative Content-Length")
            if declared > limit:
                raise BpaDtn7ResponseTooLarge("BPA response exceeds configured cap")
        output = bytearray()
        while True:
            try:
                chunk = response.read(min(_READ_CHUNK_BYTES, limit + 1 - len(output)))
            except socket.timeout as error:
                raise BpaDtn7Timeout("BPA response timed out") from error
            if not chunk:
                return bytes(output)
            if len(chunk) > limit - len(output):
                raise BpaDtn7ResponseTooLarge("BPA response exceeds configured cap")
            output.extend(chunk)
            if len(output) == limit:
                # One byte more distinguishes exact-at-cap from an oversized
                # chunked response without allocating beyond the configured cap.
                try:
                    extra = response.read(1)
                except socket.timeout as error:
                    raise BpaDtn7Timeout("BPA response timed out") from error
                if extra:
                    raise BpaDtn7ResponseTooLarge("BPA response exceeds configured cap")
                return bytes(output)

    def _get(self, path: str, operation: str, limit: int) -> bytes:
        connection = self._connection_factory(self.host, self.port, timeout=self.timeout_seconds)
        try:
            connection.request("GET", path, headers={"Accept": "application/json, application/octet-stream"})
            response = connection.getresponse()
            if response.status != 200:
                detail = self._read_bounded(response, MAX_ERROR_RESPONSE_BYTES)
                raise BpaDtn7HttpError(response.status, operation, detail)
            return self._read_bounded(response, limit)
        except BpaDtn7Error:
            raise
        except (socket.timeout, TimeoutError) as error:
            raise BpaDtn7Timeout(f"BPA {operation} timed out") from error
        except (OSError, http.client.HTTPException) as error:
            raise BpaDtn7Error(f"BPA {operation} failed") from error
        finally:
            connection.close()

    def inventory(self) -> tuple[str, ...]:
        """Return bounded BPA BIDs from pinned `/status/bundles` JSON."""
        raw = self._get("/status/bundles", "inventory", MAX_INVENTORY_RESPONSE_BYTES)
        try:
            decoded = raw.decode("utf-8", "strict")
            values = json.loads(decoded)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise BpaDtn7ProtocolError("BPA inventory is not UTF-8 JSON") from error
        if not isinstance(values, list) or len(values) > MAX_INVENTORY_COUNT:
            raise BpaDtn7ProtocolError("BPA inventory is not within the local bound")
        checked = tuple(_bounded_visible_ascii(value, "BPA inventory BID") for value in values)
        if len(set(checked)) != len(checked):
            raise BpaDtn7ProtocolError("BPA inventory contains duplicate BIDs")
        return checked

    def download_bundle(self, bid: str) -> bytes:
        """Non-destructively fetch opaque BP bundle bytes by BID.

        The method deliberately does not decode CBOR or extract an article ADU.
        """
        raw = self._get("/download?" + _raw_query_bid(bid), "download", self.max_bundle_bytes)
        if not raw:
            raise BpaDtn7ProtocolError("BPA download is empty")
        return raw

    def delete(self, bid: str) -> None:
        """Request explicit BPA deletion; it has no fn acceptance meaning."""
        self._get("/delete?" + _raw_query_bid(bid), "delete", MAX_ERROR_RESPONSE_BYTES)
