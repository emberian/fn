#!/usr/bin/env python3
"""Loopback human reader/composer for an fn NNTP node.

This is a separate client process. It never opens the Store, changes fn's
state directly, or treats viewing an article as a processing acknowledgement.
Use an SSH loopback forward for a remote node; the HTTP listener and its NNTP
target are both restricted to loopback for this first interface.
"""
from __future__ import annotations

import argparse
from collections import OrderedDict
import fcntl
import hashlib
import html
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import hmac
import json
import os
from pathlib import Path
import re
import secrets
import stat
import tempfile
import threading
from types import SimpleNamespace
from typing import Optional, Tuple
from urllib.parse import parse_qs, urlencode, urlsplit

import fn_client
from nntp_session import Disconnected, Session

MAX_LINE = 8192
MAX_BLOCK = 262144
MAX_BLOCK_LINES = 2048
MAX_FORM = 24576
MAX_BODY = 16384
MAX_RECENT = 40
MAX_ARTICLE_NUMBER = 9_999_999_999
MAX_SUBMISSIONS = 128


class BoundedSession(Session):
    """The existing NNTP wire client with finite reader allocation."""

    def line(self) -> str:
        while b"\r\n" not in self.buf:
            if len(self.buf) > MAX_LINE:
                raise Disconnected("NNTP line exceeds the web client limit")
            chunk = self.sock.recv(4096)
            if not chunk:
                raise Disconnected("the node closed the connection")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        if len(out) > MAX_LINE:
            raise Disconnected("NNTP line exceeds the web client limit")
        return out.decode("utf-8", "replace")

    def block(self) -> list[str]:
        lines, size = [], 0
        while True:
            one = self.line()
            if one == ".":
                return lines
            size += len(one.encode("utf-8")) + 2
            if size > MAX_BLOCK or len(lines) >= MAX_BLOCK_LINES:
                raise Disconnected("NNTP block exceeds the web client limit")
            lines.append(one[1:] if one.startswith("..") else one)


class FormErrors:
    def error(self, message: str) -> None:
        raise ValueError(message)


class Backend:
    def __init__(self, args, user: str, password: str):
        self.args, self.user, self.password = args, user, password

    def using(self, operation):
        client = fn_client.Client(self.args, self.user, self.password,
                                  session_factory=BoundedSession)
        try:
            client.open()
            return operation(client)
        finally:
            client.close()

    def groups(self):
        return self.using(lambda client: client.groups())

    def recent(self, group: str, start: Optional[int] = None,
               end: Optional[int] = None):
        # Validate before opening a connection. Explicit bounds identify one
        # stable local-number window; a newer GROUP high-water mark never
        # silently slides that window.
        if (start is None) != (end is None):
            raise ValueError("both article-window bounds are required")
        if start is not None and (start < 1 or end < start or
                                  end > MAX_ARTICLE_NUMBER or
                                  end - start + 1 > MAX_RECENT):
            raise ValueError("article window must contain at most 40 valid number slots")

        def query(client):
            status, _ = client.cmd("GROUP " + group)
            if not status.startswith("211"):
                return fn_client.Result(fn_client.REFUSED, status, {}, "")
            fields = status.split()
            low = fn_client.number(fields[2]) if len(fields) > 2 else None
            high = fn_client.number(fields[3]) if len(fields) > 3 else None
            if low is None or high is None or high < 0:
                raise fn_client.Stop(fn_client.UNCERTAIN, "invalid GROUP range: " + status)
            window_start, window_end = start, end
            if window_start is None:
                if high < low:
                    window_start, window_end = 1, 0
                else:
                    window_end = high
                    window_start = max(low, window_end - MAX_RECENT + 1)
            if window_start > window_end:
                rows = []
            else:
                overview, body = client.cmd("OVER %d-%d" % (window_start, window_end),
                                            multiline=True)
                if overview.startswith("224"):
                    rows = []
                    for line in body:
                        parts = line.split("\t")
                        number = fn_client.number(parts[0]) if parts else None
                        if number is None or not window_start <= number <= window_end:
                            continue
                        rows.append({"number": number,
                                     "subject": parts[1] if len(parts) > 1 else "(no subject)",
                                     "from": parts[2] if len(parts) > 2 else "",
                                     "date": parts[3] if len(parts) > 3 else "",
                                     "message_id": parts[4] if len(parts) > 4 else "",
                                     "references": parts[5] if len(parts) > 5 else ""})
                elif overview[:3] in ("420", "423"):
                    rows = []
                else:
                    return fn_client.Result(fn_client.REFUSED, overview, {}, "")
            return fn_client.Result(fn_client.DONE, status,
                                    {"group": group, "rows": rows, "low": low,
                                     "high": high, "window_start": window_start,
                                     "window_end": window_end}, "")
        return self.using(query)

    def article(self, group: str, number: int):
        def query(client):
            result = client.show(str(number), group)
            if result.word != fn_client.DONE:
                return result
            report = None
            try:
                # The ARTICLE header's Message-ID is article data and may not
                # identify the server's selected slot. Query that slot on this
                # same connection and accept only its exact numeric HDR row.
                status, lines = client.cmd("HDR :fn-verified " + str(number),
                                           multiline=True)
                if status.startswith("225") and len(lines) == 1:
                    report = parse_verdict_hdr(lines[0], number)
            except fn_client.Stop:
                # ARTICLE already succeeded; a failed optional metadata query
                # only makes the server report unavailable.
                pass
            result.data["fn_verified_report"] = report
            return result
        return self.using(query)

    def prepare(self, group: str, subject: str, sender: str, references: str,
                body: str):
        form = SimpleNamespace(group=group, subject=subject, sender=sender,
                               references=references, message_id="", body_file="",
                               host=self.args.host)
        return fn_client.compose(form, self.user, FormErrors(), body)

    def post(self, group: str, lines: tuple[str, ...], msgid: str):
        try:
            return self.using(lambda client: client.post(group, list(lines), msgid))
        except fn_client.Stop as exc:
            # A connection failure before POST still has a stable identifier
            # for later settlement. Keep it through the HTTP boundary.
            return fn_client.Result(exc.word, exc.detail,
                                    {"message_id": msgid}, "")


class SubmissionBook:
    """One process's bounded, exact source and outcome memory, never an fn ack."""

    def __init__(self, backend: Backend):
        self.backend = backend
        self.lock = threading.Lock()
        self.entries = OrderedDict()

    def new(self, group: str) -> str:
        with self.lock:
            if len(self.entries) >= MAX_SUBMISSIONS:
                self.entries.popitem(last=False)
            token = secrets.token_urlsafe(24)
            self.entries[token] = {"group": group, "lines": None, "message_id": "",
                                   "result": None, "settlement": None}
            return token

    def get(self, token: str):
        with self.lock:
            return self.entries.get(token)

    def submit(self, token: str, group: str, subject: str, sender: str,
               references: str, body: str):
        # Hold the lock through the finite NNTP operation. Two HTTP requests
        # with this token cannot both issue POST, even when they race.
        with self.lock:
            entry = self.entries.get(token)
            if entry is None:
                return None
            if group != entry["group"]:
                raise ValueError("form group does not match its submission identifier")
            if entry["result"] is not None:
                return entry
            lines, msgid = self.backend.prepare(group, subject, sender,
                                                 references, body)
            entry["lines"] = tuple(lines)
            entry["message_id"] = msgid
            try:
                entry["result"] = self.backend.post(group, entry["lines"], msgid)
            except (OSError, Disconnected) as exc:
                entry["result"] = fn_client.Result(
                    fn_client.UNCERTAIN, fn_client.unsettled(msgid, str(exc)),
                    {"message_id": msgid}, "")
            return entry

    def settle(self, token: str):
        with self.lock:
            entry = self.entries.get(token)
            if entry is None or not entry["message_id"]:
                return entry
            try:
                result = self.backend.using(
                    lambda client: client.show(entry["message_id"], ""))
            except fn_client.Stop as exc:
                result = fn_client.Result(exc.word, exc.detail, {}, "")
            except (OSError, Disconnected) as exc:
                result = fn_client.Result(fn_client.UNCERTAIN, str(exc), {}, "")
            entry["settlement"] = result
            return entry


class OutboxError(Exception):
    """Local outbox persistence failed; no new network submission is safe."""


class OutboxFull(OutboxError):
    pass


class DurableSubmissionBook(SubmissionBook):
    """Private single-writer spool; intent reaches disk before any NNTP call."""

    def __init__(self, backend: Backend, directory: Path):
        super().__init__(backend)
        self.durable = True
        self.directory = directory.expanduser().absolute()
        self.fenced = None
        self.lock_fd = None
        self.dir_fd = None
        self.target = self._target()
        try:
            self.directory.mkdir(mode=0o700, parents=True, exist_ok=True)
            info = self.directory.lstat()
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or \
                    stat.S_IMODE(info.st_mode) != 0o700:
                raise OutboxError("outbox directory must be owned by this user with mode 0700")
            self.dir_fd = os.open(self.directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            self.lock_fd = os.open(self.directory / ".lock",
                                   os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
            lock_info = os.fstat(self.lock_fd)
            if not stat.S_ISREG(lock_info.st_mode) or lock_info.st_uid != os.getuid() or \
                    stat.S_IMODE(lock_info.st_mode) != 0o600:
                raise OutboxError("outbox lock must be a private regular file")
            try:
                fcntl.flock(self.lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise OutboxError("outbox is open in another client") from exc
            paths = sorted(self.directory.iterdir())
            if len(paths) > MAX_SUBMISSIONS * 2 + 1:
                raise OutboxError("outbox has too many files")
            for path in paths:
                if path.name == ".lock":
                    continue
                if re.fullmatch(r"\.record-[A-Za-z0-9_]{8}", path.name):
                    leftover = path.lstat()
                    if not stat.S_ISREG(leftover.st_mode) or \
                            leftover.st_uid != os.getuid() or \
                            stat.S_IMODE(leftover.st_mode) != 0o600:
                        raise OutboxError("outbox has an unsafe temporary file")
                    path.unlink()
                    os.fsync(self.dir_fd)
                    continue
                if not re.fullmatch(r"[A-Za-z0-9_-]{32}\.json", path.name):
                    raise OutboxError("outbox contains an unexpected file")
                entry = self._read(path)
                self.entries[path.stem] = entry
            if len(self.entries) > MAX_SUBMISSIONS:
                raise OutboxError("outbox exceeds its record limit")
        except Exception:
            self.close()
            raise

    def _target(self):
        args = self.backend.args
        cafile = getattr(args, "cafile", None)
        ca_digest = hashlib.sha256(Path(cafile).expanduser().read_bytes()).hexdigest() \
            if cafile and not args.plain else ""
        return {"host": args.host, "port": args.port, "plain": bool(args.plain),
                "user": self.backend.user, "ca_sha256": ca_digest}

    def close(self):
        if self.lock_fd is not None:
            os.close(self.lock_fd)
            self.lock_fd = None
        if self.dir_fd is not None:
            os.close(self.dir_fd)
            self.dir_fd = None

    def _read(self, path):
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
        try:
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or \
                    stat.S_IMODE(info.st_mode) != 0o600 or info.st_size > 32768:
                raise OutboxError("outbox record is not a bounded private file")
            raw = bytearray()
            while len(raw) <= 32768:
                chunk = os.read(fd, 32769 - len(raw))
                if not chunk:
                    break
                raw.extend(chunk)
        finally:
            os.close(fd)
        try:
            saved = json.loads(raw)
            if saved["version"] != 1 or saved["target"] != self.target:
                raise OutboxError("outbox record has another version or target")
            if saved["token"] != path.stem or not group_token(saved["group"]) or \
                    not isinstance(saved["lines"], list) or not saved["lines"] or \
                    not all(isinstance(line, str) for line in saved["lines"]) or \
                    len("\r\n".join(saved["lines"]).encode()) > MAX_BODY + 4096 or \
                    not isinstance(saved["message_id"], str) or \
                    not saved["message_id"].startswith("<") or \
                    not saved["message_id"].endswith(">"):
                raise OutboxError("outbox record is malformed")
            original = saved["result"]
            if original is None:
                result = fn_client.Result(fn_client.UNCERTAIN,
                    fn_client.unsettled(saved["message_id"],
                        "the client restarted with an in-flight durable intent"),
                    {"message_id": saved["message_id"]}, "")
            elif isinstance(original, dict) and original["word"] in (
                    fn_client.ACCEPTED, fn_client.REFUSED,
                                       fn_client.UNCERTAIN) and isinstance(original["detail"], str):
                result = fn_client.Result(original["word"], original["detail"],
                                          {"message_id": saved["message_id"]}, "")
            else:
                raise OutboxError("outbox outcome is malformed")
            observation = saved.get("settlement")
            if observation is not None and (not isinstance(observation, dict) or
                    observation["word"] not in
                    (fn_client.DONE, fn_client.REFUSED, fn_client.UNCERTAIN) or
                    not isinstance(observation["detail"], str)):
                raise OutboxError("outbox observation is malformed")
            return {"group": saved["group"], "lines": tuple(saved["lines"]),
                    "message_id": saved["message_id"], "result": result,
                    "settlement": (fn_client.Result(observation["word"],
                                   observation["detail"], {}, "") if observation else None),
                    "original_recorded": original is not None, "record_error": None}
        except (KeyError, TypeError, UnicodeError, ValueError, AttributeError) as exc:
            raise OutboxError("outbox record is malformed") from exc

    def _write(self, token, entry, original, settlement):
        saved = {"version": 1, "token": token, "target": self.target,
                 "group": entry["group"], "lines": list(entry["lines"]),
                 "message_id": entry["message_id"], "result": original,
                 "settlement": settlement}
        data = json.dumps(saved, ensure_ascii=True, separators=(",", ":")).encode()
        if len(data) > 32768:
            raise OutboxError("outbox record exceeds 32 KiB")
        fd, temporary = tempfile.mkstemp(prefix=".record-", dir=self.directory)
        try:
            with os.fdopen(fd, "wb") as stream:
                stream.write(data)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, self.directory / (token + ".json"))
            os.fsync(self.dir_fd)
        finally:
            if os.path.exists(temporary):
                os.unlink(temporary)

    def _fence(self, exc):
        self.fenced = "outbox persistence failed: " + str(exc)
        return self.fenced

    def new(self, group: str) -> str:
        with self.lock:
            if self.fenced:
                raise OutboxError(self.fenced)
            if len(self.entries) >= MAX_SUBMISSIONS:
                stale = next((token for token, entry in self.entries.items()
                              if entry["lines"] is None), None)
                if stale is None:
                    raise OutboxFull("outbox is full; archive records while the client is stopped")
                del self.entries[stale]
            token = secrets.token_urlsafe(24)
            self.entries[token] = {"group": group, "lines": None, "message_id": "",
                                   "result": None, "settlement": None,
                                   "original_recorded": False, "record_error": None}
            return token

    def submit(self, token, group, subject, sender, references, body):
        with self.lock:
            entry = self.entries.get(token)
            if entry is None:
                return None
            if group != entry["group"]:
                raise ValueError("form group does not match its submission identifier")
            if entry["result"] is not None:
                return entry
            if self.fenced:
                raise OutboxError(self.fenced)
            lines, msgid = self.backend.prepare(group, subject, sender, references, body)
            entry["lines"], entry["message_id"] = tuple(lines), msgid
            if sum(one["lines"] is not None for one in self.entries.values()) > MAX_SUBMISSIONS:
                raise OutboxFull("outbox is full")
            try:
                self._write(token, entry, None, None)
            except (OSError, OutboxError) as exc:
                raise OutboxError(self._fence(exc)) from exc
            # The durable in-flight marker also prevents a second send if a
            # later local exception occurs before the response is recorded.
            entry["result"] = fn_client.Result(fn_client.UNCERTAIN,
                fn_client.unsettled(msgid, "an in-flight attempt has no recorded answer"),
                {"message_id": msgid}, "")
            try:
                answer = self.backend.post(group, entry["lines"], msgid)
            except (OSError, Disconnected) as exc:
                answer = fn_client.Result(fn_client.UNCERTAIN,
                    fn_client.unsettled(msgid, str(exc)), {"message_id": msgid}, "")
            entry["result"] = answer
            original = {"word": answer.word, "detail": answer.detail}
            try:
                self._write(token, entry, original, None)
                entry["original_recorded"] = True
            except (OSError, OutboxError) as exc:
                entry["record_error"] = self._fence(exc)
            return entry

    def settle(self, token):
        entry = super().settle(token)
        with self.lock:
            if entry is not None and entry["settlement"] is not None and not self.fenced:
                observation = {"word": entry["settlement"].word,
                               "detail": entry["settlement"].detail}
                original = ({"word": entry["result"].word, "detail": entry["result"].detail}
                            if entry["original_recorded"] else None)
                try:
                    self._write(token, entry, original, observation)
                except (OSError, OutboxError) as exc:
                    entry["record_error"] = self._fence(exc)
        return entry


def e(value) -> str:
    return html.escape(str(value if value is not None else ""), quote=True)


def parse_verdict_hdr(line: str, expected_number: int):
    """Accept only the bounded three-outcome HDR grammar; never infer a verdict."""
    fields = line.split()
    if len(fields) < 3 or fields[0] != str(expected_number):
        return None
    outcome = fields[1]
    if outcome == "verified":
        if len(fields) == 5 and re.fullmatch(r"[0-9a-fA-F]{64}", fields[2]) and \
                fields[3] == "keyring" and fields[4].isascii() and fields[4].isdecimal():
            return "verified by principal " + fields[2].lower() + \
                   " under keyring generation " + fields[4]
        if len(fields) == 5 and fields[2] == "legacy" and fields[3] == "keyring" and \
                fields[4].isascii() and fields[4].isdecimal():
            return "verified (legacy recorded detail) under keyring generation " + fields[4]
        return None
    if outcome == "unverified":
        if len(fields) == 5 and fields[2] in {
                "malformed", "ref-mismatch", "signature", "unknown"} and \
                fields[3] == "keyring" and fields[4].isascii() and fields[4].isdecimal():
            return "unverified: " + fields[2] + ", keyring generation " + fields[4]
        return None
    if outcome == "absent" and len(fields) == 3 and fields[2] in {"no-field", "no-record"}:
        return "absent: " + fields[2]
    return None


def href(path: str, **parameters) -> str:
    return path + ("?" + urlencode(parameters) if parameters else "")


def group_token(value: str) -> bool:
    return bool(value) and len(value) <= 240 and all(
        c.isascii() and (c.isalnum() or c in ".-_+") for c in value)


def article_window(values: dict) -> Optional[Tuple[int, int]]:
    """Parse one bounded explicit window, or None for initial recent view."""
    has_start, has_end = "start" in values, "end" in values
    if not has_start and not has_end:
        return None
    if has_start != has_end:
        raise ValueError("both article-window bounds are required")
    start_text, end_text = values["start"], values["end"]
    if (not start_text.isascii() or not start_text.isdecimal() or len(start_text) > 10 or
            not end_text.isascii() or not end_text.isdecimal() or len(end_text) > 10):
        raise ValueError("invalid article-window bounds")
    start, end = int(start_text), int(end_text)
    if (start < 1 or end < start or end > MAX_ARTICLE_NUMBER or
            end - start + 1 > MAX_RECENT):
        raise ValueError("article window must contain at most 40 valid number slots")
    return start, end


def group_summary(row: dict) -> str:
    first, last = row["first"], row["last"]
    address = ("No local articles yet" if first is None or last is None or last < first else
               "Local article numbers %s–%s" % (first, last))
    policy = {"y": "posting allowed", "n": "read only", "m": "moderated"}.get(
        row["status"], "status " + row["status"])
    return address + " · " + policy


def depth_of(row: dict, by_id: dict, seen=None) -> int:
    seen = set() if seen is None else seen
    msgid = row["message_id"]
    if msgid in seen:
        return 0
    refs = row["references"].split()
    parent = next((by_id[ref] for ref in reversed(refs)
                   if ref in by_id and ref != msgid), None)
    return min(4, 1 + depth_of(parent, by_id, seen | {msgid})) if parent else 0


STYLE = """
:root { color-scheme: light; font-family: system-ui, sans-serif; background:#f5f3eb; color:#172725 }
body { max-width: 940px; margin: 0 auto; padding: 1.5rem 1rem 5rem; line-height:1.5 }
header { display:flex; align-items:baseline; justify-content:space-between; border-bottom:2px solid #214e43; margin-bottom:1.5rem }
h1,h2 { line-height:1.2; letter-spacing:-.03em } h1 { font-size:2rem; margin:.5rem 0 } h2 { font-size:1.45rem }
a { color:#145f50; text-decoration-thickness:1px; text-underline-offset:.17em }
a:hover { color:#922e24 } nav a { margin-right:1rem }
.card, article { background:#fffefa; border:1px solid #cbd5cd; border-radius:12px; padding:1rem 1.2rem; margin:.7rem 0; box-shadow:0 2px 5px #193d2b0d }
.meta { color:#52645d; font-size:.88rem; overflow-wrap:anywhere }
.badge { display:inline-block; border-radius:100px; padding:.15rem .6rem; font-size:.8rem; background:#e2efe7; color:#144d3d }
.accepted { background:#daf1df } .refused { background:#fae0d9 } .uncertain { background:#fff0be }
.thread { border-left:3px solid #b7d5c6 } pre { white-space:pre-wrap; overflow-wrap:anywhere; font-family:ui-monospace, monospace }
details { margin-top:1rem; border-top:1px solid #d9e1d9; padding-top:.6rem } summary { cursor:pointer; font-weight:650 }
.hint { border-left:3px solid #d1a24b; padding:.5rem .8rem; background:#fff9e8 }
input,textarea { box-sizing:border-box; width:100%; padding:.7rem; margin:.2rem 0 .9rem; border:1px solid #9cad9e; border-radius:6px; font:inherit; background:#fff }
textarea { min-height:12rem } label { display:block; font-weight:650 }
button,.button { display:inline-block; border:0; border-radius:6px; padding:.65rem 1rem; background:#145f50; color:white; font:inherit; cursor:pointer; text-decoration:none }
button:hover,.button:hover { background:#0b4439 } .muted { color:#52645d }
"""


class Handler(BaseHTTPRequestHandler):
    server: "WebServer"

    def setup(self):
        super().setup()
        self.connection.settimeout(15)

    def log_message(self, *_args) -> None:
        # Paths contain article identifiers and form handling may carry private
        # content. The local UI does not put requests into access logs.
        pass

    def page(self, title: str, content: str, status: int = 200):
        page = ("<!doctype html><html lang='en'><meta charset='utf-8'>"
                "<meta name='viewport' content='width=device-width,initial-scale=1'>"
                "<title>" + e(title) + " · fn</title><style>" + STYLE + "</style>"
                "<body><header><h1><a href='/'>fn / news</a></h1>"
                + ("<a href='/outbox'>Local outbox</a>" if getattr(
                    self.server.submissions, "durable", False) else
                   "<span class='muted'>local reader</span>") +
                "</header>" + content + "</body></html>")
        encoded = page.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(encoded)))
        self.send_header("Cache-Control", "no-store")
        # Chromium sends Origin: null for a same-origin form when no-referrer
        # is set; same-origin still prevents a referrer going to another site.
        self.send_header("Referrer-Policy", "same-origin")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'none'; style-src 'unsafe-inline'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'")
        self.end_headers()
        self.wfile.write(encoded)

    def valid_host(self) -> bool:
        return self.headers.get("Host") == "127.0.0.1:%d" % self.server.server_port

    def get_parameters(self):
        if len(self.path) > 2048:
            raise ValueError("request URL is too long")
        parts = urlsplit(self.path)
        parsed = parse_qs(parts.query, keep_blank_values=True)
        if any(key in parsed and len(parsed[key]) != 1 for key in ("start", "end")):
            raise ValueError("article-window bounds may appear only once")
        return parts.path, {k: v[0] for k, v in parsed.items()}

    def outcome(self, word: str, detail: str, msgid: str = ""):
        link = ("<p><a href='" + e(href("/find", id=msgid)) +
                "'>Check this Message-ID</a></p>") if msgid else ""
        self.page(word.title(), "<div class='card'><span class='badge " + e(word) +
                  "'>" + e(word) + "</span><h2>" + e(detail) + "</h2>" +
                  ("<p>Message-ID: <code>" + e(msgid) + "</code></p>" if msgid else "") +
                  link + "</div>", 200 if word in ("done", "accepted") else 503)

    def submission_result(self, token: str, settle: bool = False):
        entry = (self.server.submissions.settle(token) if settle else
                 self.server.submissions.get(token))
        if entry is None:
            self.page("Submission unavailable", "<p>No local record has this identifier. "
                      "A form may have expired before its first submission. "
                      "Check the node by Message-ID if you kept it.</p>", 410)
            return
        result = entry["result"]
        if result is None:
            self.page("Draft", "<p>This form has not been submitted.</p>", 200)
            return
        word, msgid = result.word, entry["message_id"]
        if word == fn_client.ACCEPTED:
            meaning = "The node answered that it accepted this article."
        elif word == fn_client.REFUSED:
            meaning = "The node refused this exact article. This form will not post it again."
        else:
            meaning = ("The article may or may not have been accepted. Do not post a "
                       "new copy while its status is unknown.")
        observed = ""
        if entry["settlement"] is not None:
            found = entry["settlement"]
            if found.word == fn_client.DONE:
                finding = "The node now serves this Message-ID. The original POST response remains recorded above."
            elif found.word == fn_client.REFUSED:
                finding = "The node did not serve this Message-ID in this lookup. The original POST outcome has not changed."
            else:
                finding = "The lookup could not establish whether the article is served."
            observed = "<p class='hint'>" + e(finding) + "</p>"
        self.page("Post " + word, "<nav><a href='/'>Groups</a></nav><article>"
                  "<span class='badge " + e(word) + "'>" + e(word) + "</span>"
                  "<h2>" + e(meaning) + "</h2>"
                  "<p class='meta'>Message-ID: <code>" + e(msgid) + "</code></p>"
                  + observed + "<p><a href='" + e(href("/settle", id=token)) +
                  "'>Check whether the node serves this Message-ID</a></p>"
                  "<details><summary>Node response and diagnostic detail</summary><pre>" +
                  e(result.detail) + "</pre></details>"
                  + ("<p class='hint'>" + e(entry.get("record_error")) +
                     ". This process is fenced from new submissions. The node answer above "
                     "was observed here, but its local recording is uncertain.</p>"
                     if entry.get("record_error") else "") +
                  "<p class='muted'>Refresh this page safely; it never sends another POST. "
                  + ("The durable outbox keeps the source and recorded result across restart."
                     if getattr(self.server.submissions, "durable", False) else
                     "This client keeps the exact submitted source and result only while "
                     "this process runs and the form remains in its bounded memory.") + "</p>"
                  "</article>")

    def redirect(self, location: str):
        self.send_response(303)
        self.send_header("Location", location)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def run_backend(self, operation):
        try:
            return operation()
        except fn_client.Stop as exc:
            self.outcome(exc.word, exc.detail)
        except (OSError, Disconnected) as exc:
            self.outcome(fn_client.UNCERTAIN, "The NNTP connection failed: " + str(exc))
        return None

    def do_GET(self):
        if not self.valid_host():
            self.send_error(400)
            return
        try:
            path, values = self.get_parameters()
            if path == "/":
                result = self.run_backend(self.server.backend.groups)
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                cards = "".join("<article><h2><a href='" + e(href("/g", name=row["group"])) +
                                "'>" + e(row["group"]) + "</a></h2><p class='meta'>" +
                                e(group_summary(row)) + "</p></article>"
                                for row in result.data["groups"])
                self.page("Groups", "<h2>Groups</h2>" + (cards or "<p>No groups are served.</p>"))
            elif path == "/outbox" and getattr(self.server.submissions, "durable", False):
                with self.server.submissions.lock:
                    rows = [(token, entry["message_id"], entry["result"].word)
                            for token, entry in self.server.submissions.entries.items()
                            if entry["message_id"]]
                cards = "".join("<article><a href='" + e(href("/result", id=token)) +
                                "'>" + e(msgid) + "</a> · " + e(word) + "</article>"
                                for token, msgid, word in rows)
                self.page("Outbox", "<nav><a href='/'>Groups</a></nav><h2>Local outbox</h2>" +
                          (cards or "<p>No submitted records.</p>"))
            elif path == "/g":
                group = values.get("name", "")
                if not group_token(group):
                    raise ValueError("invalid group name")
                window = article_window(values)
                result = self.run_backend(lambda: self.server.backend.recent(
                    group, *(window or (None, None))))
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                rows = result.data["rows"]
                start = result.data["window_start"]
                end = result.data["window_end"]
                low, high = result.data["low"], result.data["high"]
                has_group_numbers = high >= low
                by_id = {row["message_id"]: row for row in rows if row["message_id"]}
                cards = "".join("<article class='thread' style='margin-left:" +
                                str(depth_of(row, by_id) * 18) + "px'><h2><a href='" +
                                e(href("/a", group=group, number=row["number"])) + "'>" +
                                e(row["subject"]) + "</a></h2><p class='meta'>" +
                                e(" · ".join(x for x in (row["from"], row["date"],
                                                 "local #%s" % row["number"]) if x)) +
                                "</p></article>"
                                for row in rows)
                older = ("<a rel='prev' href='" + e(href("/g", name=group,
                          start=max(low, start - MAX_RECENT), end=start - 1)) +
                         "'>Older</a>" if has_group_numbers and start > low else "")
                newer = ("<a rel='next' href='" + e(href("/g", name=group,
                          start=end + 1, end=min(MAX_ARTICLE_NUMBER, end + MAX_RECENT))) +
                         "'>Newer</a>" if has_group_numbers and end < high and
                         end < MAX_ARTICLE_NUMBER else "")
                page_window = ("Local article numbers %s–%s" % (start, end)
                               if end >= start else "No local article numbers")
                frontier = (" · group currently spans %s–%s" % (low, high)
                            if high >= low else " · group currently has no articles")
                self.page(group, "<nav><a href='/'>Groups</a><a href='" +
                          e(href("/compose", group=group)) + "'>Write a post</a></nav>"
                          "<h2>" + e(group) + "</h2><p class='muted'>" +
                          e(page_window + frontier) + " · viewing does not acknowledge processing</p>"
                          "<nav aria-label='Article number windows'>" + older + " " + newer + "</nav>" +
                          (cards or "<p>No articles in this number window.</p>"))
            elif path == "/a":
                group, raw = values.get("group", ""), values.get("number", "")
                if not group_token(group) or not raw.isascii() or not raw.isdecimal() or len(raw) > 10:
                    raise ValueError("invalid article address")
                number = int(raw)
                if number < 1:
                    raise ValueError("invalid article number")
                result = self.run_backend(lambda: self.server.backend.article(group, number))
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                one = result.data["articles"][0]
                fields = one["headers"]
                first = lambda name: fn_client.first(fields, name) or ""
                statement = bool(first("fn-statement"))
                carrier = bool(first("fn-authorship"))
                verdict = result.data.get("fn_verified_report")
                verdict_html = ("<p class='meta'>Server report of historical verification "
                                "verdict: " + e(verdict) + ". This reports what this node "
                                "recorded; it is not an independent cryptographic check or "
                                "current authorization.</p>" if verdict else
                                "<p class='meta'>Server report of historical verification "
                                "verdict: unavailable.</p>")
                provenance = ("<p class='hint'><strong>Who wrote this?</strong> The displayed "
                              "From name is a claim in the article. This reader has not "
                              "verified the writer's identity.</p><p class='meta'>"
                              + ("FN-Statement present; not verified here" if statement else
                                 "No FN-Statement recorded in this article") + "<br>" +
                              ("FN-Authorship carrier present; not verified here" if carrier else
                               "No FN-Authorship carrier recorded in this article") + "</p>" +
                              verdict_html +
                              "<details><summary>Recorded handling details</summary>"
                              "<p class='meta'>From (claimed): " + e(first("from")) +
                              "<br>Path: " + e(first("path") or "not supplied") +
                              "<br>Injection-Info: " + e(first("injection-info") or "not supplied") +
                              "<br>Injection-Date: " + e(first("injection-date") or "not supplied") +
                              "</p></details><p class='muted'>Viewing does not acknowledge application processing.</p>")
                self.page(first("subject") or "Article", "<nav><a href='" +
                          e(href("/g", name=group)) + "'>" + e(group) + "</a><a href='" +
                          e(href("/compose", group=group, reply=number)) + "'>Reply</a></nav>"
                          "<article><h2>" + e(first("subject") or "(no subject)") +
                          "</h2><p class='meta'>" + e(one["message_id"]) +
                          " · local #" + e(number) + "</p>" + provenance +
                          "<pre>" + e("\n".join(one["body"])) + "</pre></article>")
            elif path == "/compose":
                group = values.get("group", "")
                if not group_token(group):
                    raise ValueError("invalid group name")
                subject, references = "", ""
                if "reply" in values:
                    raw = values["reply"]
                    if not raw.isascii() or not raw.isdecimal() or len(raw) > 10 or int(raw) < 1:
                        raise ValueError("invalid reply number")
                    result = self.run_backend(lambda: self.server.backend.article(group, int(raw)))
                    if result is None:
                        return
                    if result.word != fn_client.DONE:
                        self.outcome(result.word, result.detail)
                        return
                    fields = result.data["articles"][0]["headers"]
                    old_subject = fn_client.first(fields, "subject") or ""
                    subject = old_subject if old_subject.lower().startswith("re:") else "Re: " + old_subject
                    msgid = fn_client.first(fields, "message-id") or ""
                    references = ((fn_client.first(fields, "references") or "") + " " +
                                  msgid).strip()
                    if len(references) > 800:
                        references = msgid
                submission_id = self.server.submissions.new(group)
                form = ("<form method='post' action='/post'><input type='hidden' name='csrf' value='" +
                        e(self.server.token) + "'><input type='hidden' name='group' value='" + e(group) +
                        "'><input type='hidden' name='submission_id' value='" + e(submission_id) +
                        "'><input type='hidden' name='references' value='" + e(references) +
                        "'><label>Subject<input name='subject' maxlength='240' required value='" +
                        e(subject[:240]) + "'></label><label>From (optional)<input name='sender' maxlength='240' value='" +
                        e(self.server.backend.user) + "'></label><label>Message<textarea name='body' maxlength='16384' required></textarea></label>"
                        "<button>Post to " + e(group) + "</button></form>")
                self.page("Compose", "<nav><a href='" + e(href("/g", name=group)) +
                          "'>" + e(group) + "</a></nav><h2>Write a post</h2>"
                          "<p class='muted'>One form sends one exact article. If the reply "
                          "is uncertain, keep its Message-ID and check it before trying again.</p>" + form)
            elif path in ("/result", "/settle"):
                token = values.get("id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                self.submission_result(token, settle=(path == "/settle"))
            elif path == "/find":
                msgid = values.get("id", "")
                if not (len(msgid) <= 250 and msgid.startswith("<") and msgid.endswith(">")
                        and "\r" not in msgid and "\n" not in msgid):
                    raise ValueError("invalid Message-ID")
                result = self.run_backend(lambda: self.server.backend.using(
                    lambda client: client.show(msgid, "")))
                if result is None:
                    return
                self.outcome(result.word, result.detail, msgid)
            else:
                self.page("Not found", "<p>Page not found.</p>", 404)
        except ValueError as exc:
            self.page("Invalid request", "<p>" + e(exc) + "</p>", 400)
        except OutboxFull as exc:
            self.page("Outbox full", "<p>" + e(exc) + "</p>", 507)
        except OutboxError as exc:
            self.page("Outbox unavailable", "<p>" + e(exc) + "</p>", 503)

    def do_POST(self):
        if not self.valid_host() or self.path != "/post":
            self.send_error(400)
            return
        expected = "http://127.0.0.1:%d" % self.server.server_port
        if self.headers.get("Origin") != expected:
            self.page("Refused", "<p>Form origin was not this local reader.</p>", 403)
            return
        try:
            length = int(self.headers.get("Content-Length", "-1"))
            if not 0 <= length <= MAX_FORM:
                raise ValueError("form is too large")
            raw = self.rfile.read(length)
            values = {k: v[0] for k, v in parse_qs(raw.decode("utf-8", "strict"),
                                                    keep_blank_values=True,
                                                    max_num_fields=16).items()}
            if not hmac.compare_digest(values.get("csrf", ""), self.server.token):
                self.page("Refused", "<p>Form token is invalid.</p>", 403)
                return
            submission_id = values.get("submission_id", "")
            if not submission_id or len(submission_id) > 64:
                raise ValueError("invalid submission identifier")
            group, subject = values.get("group", ""), values.get("subject", "")
            sender, references, body = (values.get("sender", ""),
                                        values.get("references", ""), values.get("body", ""))
            if (not group_token(group) or not subject or len(subject) > 240 or
                    len(sender) > 240 or len(references) > 800 or len(body.encode()) > MAX_BODY or
                    not body.strip() or any("\r" in x or "\n" in x
                                            for x in (subject, sender, references)) or
                    any(len(line.encode()) > 998 for line in body.splitlines())):
                raise ValueError("post fields are invalid or too large")
            entry = self.server.submissions.submit(
                submission_id, group, subject, sender, references, body)
            if entry is None:
                self.page("Submission unavailable", "<p>This form's local record "
                          "expired or the web client restarted. No POST was sent.</p>", 410)
                return
            self.redirect(href("/result", id=submission_id))
        except (ValueError, UnicodeDecodeError) as exc:
            self.page("Invalid post", "<p>" + e(exc) + "</p>", 400)
        except OutboxFull as exc:
            self.page("Outbox full", "<p>" + e(exc) + "</p>", 507)
        except OutboxError as exc:
            self.page("Outbox unavailable", "<p>" + e(exc) + "</p>", 503)


class WebServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, port: int, backend: Backend, outbox: Optional[Path] = None):
        self.backend = backend
        self.token = secrets.token_urlsafe(32)
        self.submissions = (DurableSubmissionBook(backend, outbox) if outbox else
                            SubmissionBook(backend))
        try:
            super().__init__(("127.0.0.1", port), Handler)
        except Exception:
            if outbox:
                self.submissions.close()
            raise

    def server_close(self):
        super().server_close()
        if getattr(self.submissions, "durable", False):
            self.submissions.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node", default="127.0.0.1:1119")
    parser.add_argument("--port", type=int, default=8919, help="loopback HTTP port")
    parser.add_argument("--cafile")
    parser.add_argument("--plain", action="store_true")
    parser.add_argument("--credentials")
    parser.add_argument("--outbox", type=Path,
                        help="private durable local submission directory")
    parser.add_argument("--timeout", type=float, default=15.0)
    args = parser.parse_args(argv)
    fn_client.resolve(args, parser)
    if args.host not in ("127.0.0.1", "::1"):
        parser.error("the initial web client requires a loopback NNTP target")
    if not 0 <= args.port < 65536 or not 0 < args.timeout <= 60:
        parser.error("invalid HTTP port or timeout")
    user, password = ("", "") if args.plain else fn_client.credentials(args, parser)
    if not args.plain and not (user and password):
        parser.error("set client credentials or pass a mode-0600 --credentials file")
    try:
        with WebServer(args.port, Backend(args, user, password), args.outbox) as server:
            print("fn web client: http://127.0.0.1:%d/" % server.server_port, flush=True)
            server.serve_forever()
    except (OSError, OutboxError) as exc:
        parser.error("local web client: " + str(exc))


if __name__ == "__main__":
    main()
