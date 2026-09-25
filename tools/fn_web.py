#!/usr/bin/env python3
"""Loopback human reader/composer for an fn NNTP node.

This is a separate client process. It never opens the Store, changes fn's
state directly, or treats viewing an article as a processing acknowledgement.
The HTTP listener is always 127.0.0.1. The NNTP target is either a loopback
development node (--plain) or any node reached over STARTTLS with a verified
certificate (--tls-cert) and an AUTHINFO login; every accept, refuse, number
and verdict shown is the node's answer, never this process's decision.

    python3 tools/fn_web.py --node 192.168.50.39:1119 --tls-cert hbox-cert.pem --user ember
"""
from __future__ import annotations

import argparse
import datetime
import email.utils
import subprocess
from collections import OrderedDict
import fcntl
import getpass
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
import sys
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
MAX_READ_NUMBERS = 4096
MAX_REFERENCES = 800
# Work per search request (numbers the node is asked to scan in one XPAT);
# a bound on work, not on the group, which the next page continues past.
SEARCH_SPAN = 2000
MAX_SEARCH_HITS = 200
MAX_RECORD = 65536
MAX_SIGNED_EXTRA = 24576
LOOPBACK = ("127.0.0.1", "::1")


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


class SigningError(Exception):
    """Local signing failed; nothing was sent to the node."""


class Signer:
    """The login's hybrid key on this machine, and the fn image that signs with it.

    The honest choice among the three (D28 spike record): the secret key stays
    on the author's machine in a 0700 directory, and the signed preimage and
    FN-Authorship carrier are rendered by ACL2 inside the local fn image
    (`hybrid-sign-carrier`, which verifies both signatures before writing).
    A browser-held key would need a JavaScript re-implementation of the ACL2
    preimage and carrier codec (a second owner) and an unreviewed ML-DSA-65
    library; a node signing verb would give the node custody of the secret,
    so `verified` would mean only "the node says this login posted".  Trust
    implied here: this machine, its fn image and the key directory's mode.

    ;; SPIKE: defers the login-to-principal binding.  The node relates no
    ;; AUTHINFO user to a hybrid principal; this client signs with whatever
    ;; key directory it was given, and the node judges the carrier only
    ;; against its enrollment of the principal inside it.
    """

    FILES = ("principal.bin", "ed-public.bin", "ed-secret.bin", "ml-public.pem",
             "ml-private.pem")

    def __init__(self, directory: Path, image: Path, tree: Optional[Path] = None):
        self.directory = directory.expanduser().absolute()
        self.image, self.tree = Path(image).absolute(), tree
        info = self.directory.stat()
        if stat.S_IMODE(info.st_mode) & 0o077 or info.st_uid != os.getuid():
            raise SigningError("signing key directory must be private to this user")
        for name in self.FILES:
            if not (self.directory / name).is_file():
                raise SigningError("signing key directory lacks " + name)
        self.principal = (self.directory / "principal.bin").read_bytes().hex()
        if len(self.principal) != 64:
            raise SigningError("principal.bin must be 32 octets")

    def sign(self, lines: list) -> list:
        with tempfile.TemporaryDirectory(prefix="fn-web-sign-") as work:
            source, out = Path(work) / "source.eml", Path(work) / "carrier.eml"
            source.write_bytes(("\r\n".join(lines) + "\r\n").encode("utf-8"))
            try:
                done = subprocess.run(
                    [str(self.image), "--fn", "hybrid-sign-carrier",
                     *[str(self.directory / name) for name in self.FILES],
                     str(source), str(out)],
                    cwd=str(self.tree) if self.tree else None, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, timeout=120, check=False)
            except (OSError, subprocess.TimeoutExpired) as exc:
                raise SigningError("the local fn image did not sign: %s" % exc) from exc
            if done.returncode != 0 or not out.is_file():
                raise SigningError("the local fn image refused to sign: " +
                                   (done.stderr or done.stdout).decode("utf-8", "replace")
                                   .strip()[-400:])
            octets = out.read_bytes()
        text = octets.decode("utf-8", "strict")
        if text.endswith("\r\n"):
            text = text[:-2]
        return text.split("\r\n")


class Backend:
    def __init__(self, args, user: str, password: str, sender: str = "",
                 signer: Optional[Signer] = None):
        self.args, self.user, self.password = args, user, password
        self.sender = sender
        self.signer = signer

    @property
    def node(self) -> str:
        return fn_client.node_name(self.args.host, self.args.port)

    def default_from(self) -> str:
        # Display only: fn_client.compose writes this same default when the
        # From field is left empty; the node decides whether it is acceptable.
        user = self.user or "anonymous"
        return self.sender or "%s <%s@%s>" % (user, user, self.args.host)

    def login_check(self):
        """Open one connection exactly as every page does: STARTTLS, verify, 281.

        The node answers; a refusal (481, a certificate that does not verify)
        and an uncertain outcome (unreachable, handshake cut) stay distinct.
        """
        def query(client):
            tls = client.session.tls
            return fn_client.Result(fn_client.DONE, "logged in", {"tls": tls}, "")
        try:
            return self.using(query)
        except fn_client.Stop as exc:
            return fn_client.Result(exc.word, exc.detail, {}, "")

    def slot(self, group: str, number: int):
        """What the node serves at one local number now: its OVER row, or none."""
        def query(client):
            status, _ = client.cmd("GROUP " + group)
            if not status.startswith("211"):
                return fn_client.Result(fn_client.REFUSED, status, {}, "")
            overview, body = client.cmd("OVER %d" % number, multiline=True)
            row = None
            if overview.startswith("224"):
                for line in body:
                    parts = line.split("\t")
                    if parts and fn_client.number(parts[0]) == number and len(parts) > 4:
                        row = {"number": number, "subject": parts[1],
                               "message_id": parts[4]}
            elif overview[:3] not in ("420", "423"):
                return fn_client.Result(fn_client.REFUSED, overview, {}, "")
            fields = status.split()
            return fn_client.Result(fn_client.DONE, status,
                                    {"row": row,
                                     "low": fn_client.number(fields[2]) if len(fields) > 2 else None,
                                     "high": fn_client.number(fields[3]) if len(fields) > 3 else None},
                                    "")
        return self.using(query)

    def using(self, operation):
        client = fn_client.Client(self.args, self.user, self.password,
                                  session_factory=BoundedSession)
        try:
            client.open()
            return operation(client)
        finally:
            client.close()

    def groups(self):
        """The group list with exact counts when the node answers LIST COUNTS.

        Each row carries `count` (RFC 6048 section 2.2, the node's count of
        the articles it holds in the group).  Where the count is smaller than
        the water-mark span, the group has gaps, and the row also carries the
        node's LISTGROUP numbers so unread counts are exact there too.  A node
        without LIST COUNTS gets LIST ACTIVE and rows with `count` None.
        """
        def query(client):
            counted = client.counts()
            if counted.word != fn_client.DONE:
                return client.groups()
            for row in counted.data["groups"]:
                if row["count"] and row["count"] != fn_client.span(row["first"], row["last"]):
                    listed = client.listgroup(row["group"])
                    if listed.word != fn_client.DONE:
                        return listed
                    row["numbers"] = listed.data["numbers"]
            return counted
        return self.using(query)

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
            wanted = {row["number"] for row in rows}
            if rows:
                try:
                    # In-Reply-To is not an OVER field: one bounded HDR over
                    # the same window, accepted per numeric slot.
                    irt, lines = client.cmd("HDR In-Reply-To %d-%d"
                                            % (window_start, window_end), multiline=True)
                    if irt.startswith("225"):
                        by_number = {row["number"]: row for row in rows}
                        for line in lines[:MAX_RECENT]:
                            number, _, value = line.partition(" ")
                            one = fn_client.number(number)
                            if one in by_number:
                                ids = re.findall(r"<[^<>\s]+>", value)
                                by_number[one]["in_reply_to"] = ids[0] if ids else ""
                except fn_client.Stop:
                    pass
                try:
                    # One bounded HDR over the same window; each row's report
                    # is accepted only under its own numeric slot.
                    hdr, lines = client.cmd("HDR :fn-verified %d-%d"
                                            % (window_start, window_end), multiline=True)
                    if hdr.startswith("225"):
                        for line in lines[:MAX_RECENT]:
                            one = fn_client.number(line.split(" ", 1)[0])
                            if one in wanted:
                                report = parse_verdict_hdr(line, one)
                                if report:
                                    for row in rows:
                                        if row["number"] == one:
                                            row["verdict"] = report
                except fn_client.Stop:
                    pass
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
            # spike/control: the node's HDR :fn-control claim for this slot
            # (a control article's decision: "executed withdrawal <id>
            # author|authority", "declined <reason>", ...).  Optional.
            control = None
            try:
                status, lines = client.cmd("HDR :fn-control " + str(number),
                                           multiline=True)
                if status.startswith("225") and len(lines) == 1:
                    head, _, rest = lines[0].partition(" ")
                    if head == str(number) and rest and rest != "none":
                        control = rest[:512]
            except fn_client.Stop:
                pass
            result.data["fn_control_report"] = control
            return result
        return self.using(query)

    def prepare(self, group: str, subject: str, sender: str, references: str,
                body: str, sign: bool = False):
        form = SimpleNamespace(group=group, subject=subject, sender=sender or self.sender,
                               references=references, message_id="", body_file="",
                               host=self.args.host)
        lines, msgid = fn_client.compose(form, self.user, FormErrors(), body)
        if sign and self.signer is not None:
            # The signed source carries the author's Date (identity spec,
            # "the signed bytes"); the node adds Path and Injection-* outside it.
            cut = lines.index("")
            lines = lines[:cut] + ["Date: " + email.utils.format_datetime(
                datetime.datetime.now(datetime.timezone.utc))] + lines[cut:]
            lines = self.signer.sign(lines)
        return lines, msgid

    def search(self, group: str, field: str, query: str, before: Optional[int] = None):
        """Articles in one bounded number window whose field matches, as the node says.

        The node answers with `XPAT <field> <low>-<high> <wildmat>` (RFC 2980
        section 2.9): the web layer builds `*query*`, turning each character
        the wildmat grammar reserves into `?`, and keeps no index.  The window
        is SEARCH_SPAN numbers ending at `before` (default the high-water
        mark); the page links the next older window.  Matching is the node's:
        case-sensitive, one pattern per request.
        """
        if field not in ("subject", "from"):
            raise ValueError("search field is subject or from")
        query = query.strip()
        if not query or len(query) > 120 or any(ord(c) < 32 for c in query):
            raise ValueError("search text must be 1 to 120 printable characters")
        pattern = "*" + "".join("?" if c in "!*,?[\\] \t" else c for c in query) + "*"

        def run(client):
            status, _ = client.cmd("GROUP " + group)
            if not status.startswith("211"):
                return fn_client.Result(fn_client.REFUSED, status, {}, "")
            fields = status.split()
            low, high = fn_client.number(fields[2]), fn_client.number(fields[3])
            if low is None or high is None:
                raise fn_client.Stop(fn_client.UNCERTAIN, "invalid GROUP range: " + status)
            end = min(high, before) if before is not None else high
            start = max(low, end - SEARCH_SPAN + 1)
            hits, command = [], ""
            if end >= start and high >= low:
                command = "XPAT %s %d-%d %s" % (field.title(), start, end, pattern)
                answer, lines = client.cmd(command, multiline=True)
                if not answer.startswith("221"):
                    return fn_client.Result(fn_client.REFUSED, answer, {"command": command}, "")
                for line in lines[:MAX_SEARCH_HITS]:
                    number, _, value = line.partition(" ")
                    one = fn_client.number(number)
                    if one is not None and start <= one <= end:
                        hits.append({"number": one, "value": value})
                if hits:
                    first, last = min(h["number"] for h in hits), max(h["number"] for h in hits)
                    overview, body = client.cmd("OVER %d-%d" % (first, last), multiline=True)
                    rows = {}
                    if overview.startswith("224"):
                        for row in body:
                            parts = row.split("\t")
                            if parts and len(parts) > 4:
                                rows[fn_client.number(parts[0])] = parts
                    for hit in hits:
                        parts = rows.get(hit["number"])
                        hit["subject"] = parts[1] if parts else hit["value"]
                        hit["from"] = parts[2] if parts else ""
                        hit["date"] = parts[3] if parts else ""
            return fn_client.Result(fn_client.DONE, status,
                                    {"hits": hits, "start": start, "end": end, "low": low,
                                     "high": high, "command": command,
                                     "pattern": pattern}, "")
        return self.using(run)

    def overview_counts(self):
        """LIST COUNTS, CAPABILITIES and DATE: what any login can see of the node."""
        def run(client):
            caps, capability_lines = client.cmd("CAPABILITIES", multiline=True)
            date, _ = client.cmd("DATE")
            counted = client.counts()
            return fn_client.Result(fn_client.DONE, date,
                                    {"capabilities": capability_lines if caps.startswith("101") else [],
                                     "date": date,
                                     "groups": counted.data.get("groups", []) if counted.word == fn_client.DONE else [],
                                     "counts": counted.detail}, "")
        return self.using(run)

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
               references: str, body: str, sign: bool = False):
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
                                                 references, body, sign)
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
        self.parent_fd = None
        self.target = self._target()
        try:
            if not self.directory.parent.is_dir():
                raise OutboxError("outbox parent must already exist and be durable")
            self.directory.mkdir(mode=0o700, parents=False, exist_ok=True)
            info = self.directory.lstat()
            if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or \
                    stat.S_IMODE(info.st_mode) != 0o700:
                raise OutboxError("outbox directory must be owned by this user with mode 0700")
            self.parent_fd = os.open(self.directory.parent,
                                     os.O_RDONLY | os.O_DIRECTORY)
            # The leaf's directory entry must precede every network attempt.
            # Repeat the barrier on startup to reconcile a prior failed one.
            os.fsync(self.parent_fd)
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
        if self.parent_fd is not None:
            os.close(self.parent_fd)
            self.parent_fd = None

    def _read(self, path):
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
        try:
            info = os.fstat(fd)
            if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid() or \
                    stat.S_IMODE(info.st_mode) != 0o600 or info.st_size > MAX_RECORD:
                raise OutboxError("outbox record is not a bounded private file")
            raw = bytearray()
            while len(raw) <= MAX_RECORD:
                chunk = os.read(fd, MAX_RECORD + 1 - len(raw))
                if not chunk:
                    break
                raw.extend(chunk)
        finally:
            os.close(fd)
        try:
            saved = json.loads(raw)
            if saved["version"] != 1 or saved["target"] != self.target:
                raise OutboxError("outbox record has another version or target")
            if saved["token"] != path.stem or not group_token(saved["group"]):
                raise OutboxError("outbox record is malformed")
            draft = saved.get("draft")
            if draft is not None:
                if (not isinstance(draft, dict) or
                        any(not isinstance(draft.get(name), str) for name in
                            ("subject", "sender", "references", "body")) or
                        len(draft["subject"]) > 240 or len(draft["sender"]) > 240 or
                        len(draft["references"]) > 800 or
                        len(draft["body"].encode()) > MAX_BODY or
                        saved["lines"] is not None or saved["message_id"] != "" or
                        saved["result"] is not None or saved.get("settlement") is not None):
                    raise OutboxError("outbox draft is malformed")
                return {"group": saved["group"], "lines": None,
                        "message_id": "", "result": None, "settlement": None,
                        "draft": draft, "original_recorded": False,
                        "record_error": None}
            if not isinstance(saved["lines"], list) or not saved["lines"] or \
                    not all(isinstance(line, str) for line in saved["lines"]) or \
                    len("\r\n".join(saved["lines"]).encode()) > MAX_BODY + MAX_SIGNED_EXTRA or \
                    not isinstance(saved["message_id"], str) or \
                    not saved["message_id"].startswith("<") or \
                    not saved["message_id"].endswith(">"):
                raise OutboxError("outbox submission is malformed")
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
                    "draft": None, "original_recorded": original is not None,
                    "record_error": None}
        except (KeyError, TypeError, UnicodeError, ValueError, AttributeError) as exc:
            raise OutboxError("outbox record is malformed") from exc

    def _write(self, token, entry, original, settlement):
        saved = {"version": 1, "token": token, "target": self.target,
                 "group": entry["group"],
                 "lines": list(entry["lines"]) if entry["lines"] is not None else None,
                 "message_id": entry["message_id"], "result": original,
                 "settlement": settlement, "draft": entry.get("draft")}
        data = json.dumps(saved, ensure_ascii=True, separators=(",", ":")).encode()
        if len(data) > MAX_RECORD:
            raise OutboxError("outbox record exceeds 64 KiB")
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
                              if entry["lines"] is None and entry["draft"] is None), None)
                if stale is None:
                    raise OutboxFull("outbox is full; archive records while the client is stopped")
                del self.entries[stale]
            token = secrets.token_urlsafe(24)
            self.entries[token] = {"group": group, "lines": None, "message_id": "",
                                   "result": None, "settlement": None, "draft": None,
                                   "original_recorded": False, "record_error": None}
            return token

    def save_draft(self, token, group, subject, sender, references, body):
        with self.lock:
            entry = self.entries.get(token)
            if entry is None:
                return None
            if group != entry["group"] or entry["result"] is not None:
                raise ValueError("this submission identifier cannot save a draft")
            if self.fenced:
                raise OutboxError(self.fenced)
            entry["draft"] = {"subject": subject, "sender": sender,
                              "references": references, "body": body}
            try:
                self._write(token, entry, None, None)
            except (OSError, OutboxError) as exc:
                entry["record_error"] = self._fence(exc)
                raise OutboxError(entry["record_error"]) from exc
            return entry

    def submit(self, token, group, subject, sender, references, body, sign=False):
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
            lines, msgid = self.backend.prepare(group, subject, sender, references, body, sign)
            entry["lines"], entry["message_id"] = tuple(lines), msgid
            entry["draft"] = None
            if sum(one["lines"] is not None for one in self.entries.values()) > MAX_SUBMISSIONS:
                raise OutboxFull("outbox is full")
            try:
                self._write(token, entry, None, None)
            except (OSError, OutboxError) as exc:
                entry["record_error"] = self._fence(exc)
                raise OutboxError(entry["record_error"]) from exc
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


class ReadMarks:
    """This principal's read marks on this node, kept only on this machine.

    NNTP (RFC 3977) has no server-side read state, and fn keeps none: these
    marks are the client's note of which local article numbers this browser
    opened, not an fn record, not a processing acknowledgement and not a
    consumer cursor. Local numbers belong to one node, so the file is keyed
    by node and principal and marks are never compared across nodes.
    """

    def __init__(self, path: Optional[Path], node: str, user: str):
        self.path = path.expanduser().absolute() if path is not None else None
        self.node, self.user = node, user
        self.lock = threading.Lock()
        self.groups: dict = {}
        self.error = None
        if self.path is not None:
            self._load()

    def _load(self):
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
        except FileNotFoundError:
            return
        except (OSError, ValueError) as exc:
            self._refuse("the read-marks file could not be read (%s)" % exc)
            return
        if not isinstance(data, dict) or data.get("version") != 1 or \
                data.get("node") != self.node or data.get("user") != self.user or \
                not isinstance(data.get("groups"), dict):
            self._refuse("the read-marks file belongs to another node or principal")
            return
        for group, mark in data["groups"].items():
            try:
                through, read = mark["through"], mark["read"]
                last = mark.get("last")
                if not group_token(group) or not isinstance(through, int) or through < 0 or \
                        not isinstance(read, list) or len(read) > MAX_READ_NUMBERS or \
                        not all(isinstance(n, int) and n > through for n in read):
                    raise ValueError(group)
                if last is not None and not (
                        isinstance(last, dict) and isinstance(last.get("number"), int) and
                        isinstance(last.get("message_id"), str) and
                        len(last["message_id"]) <= 250):
                    raise ValueError(group)
            except (KeyError, TypeError, ValueError):
                self._refuse("the read-marks file is malformed")
                return
            self.groups[group] = {"through": through, "read": set(read), "last": last}

    def _refuse(self, why: str):
        # Never overwrite a file this process could not understand.
        self.error = why + "; marks start empty and are not saved this run"
        self.groups = {}
        self.path = None

    def _entry(self, group):
        return self.groups.setdefault(group, {"through": 0, "read": set(), "last": None})

    def _compact(self, entry):
        entry["read"] = {n for n in entry["read"] if n > entry["through"]}
        while entry["through"] + 1 in entry["read"]:
            entry["through"] += 1
            entry["read"].discard(entry["through"])
        while len(entry["read"]) > MAX_READ_NUMBERS:
            entry["read"].discard(min(entry["read"]))

    def _save(self):
        if self.path is None:
            return
        document = {"version": 1, "node": self.node, "user": self.user,
                    "groups": {g: {"through": m["through"], "read": sorted(m["read"]),
                                   "last": m["last"]}
                               for g, m in sorted(self.groups.items())}}
        try:
            if not self.path.parent.is_dir():
                self.path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            fd, temporary = tempfile.mkstemp(prefix=".marks-", dir=self.path.parent)
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as stream:
                    stream.write(json.dumps(document, separators=(",", ":")))
                os.replace(temporary, self.path)
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
            self.error = None
        except OSError as exc:
            self.error = "read marks were not saved (%s); they hold only until restart" % exc

    def is_read(self, group: str, number: int) -> bool:
        with self.lock:
            entry = self.groups.get(group)
            return bool(entry) and (number <= entry["through"] or number in entry["read"])

    def unread(self, row: dict):
        """(unread, exact) for one group row of Backend.groups.

        With the node's LIST COUNTS count the answer is exact: when the count
        fills the water-mark span every number in it holds an article, and
        otherwise the row carries the node's LISTGROUP numbers.  A node
        without LIST COUNTS leaves only the span, an upper bound.
        """
        low, high, count = row.get("first"), row.get("last"), row.get("count")
        if count is None:
            return self.unread_upper(row["group"], low, high), False
        if count == 0:
            return 0, True
        numbers = row.get("numbers")
        if numbers is None:
            return self.unread_upper(row["group"], low, high), True
        return sum(1 for n in set(numbers) if not self.is_read(row["group"], n)), True

    def unread_upper(self, group: str, low, high) -> int:
        """Number slots in the node's current low..high this principal has not opened.

        Exact when every number in the span holds an article (the node's
        LIST COUNTS count equals the span); otherwise an upper bound.
        """
        if low is None or high is None or high < low:
            return 0
        with self.lock:
            entry = self.groups.get(group) or {"through": 0, "read": set()}
            start = max(low, entry["through"] + 1)
            if start > high:
                return 0
            return high - start + 1 - sum(1 for n in entry["read"] if start <= n <= high)

    def last(self, group: str):
        with self.lock:
            entry = self.groups.get(group)
            return dict(entry["last"]) if entry and entry["last"] else None

    def mark(self, group: str, number: int, message_id: str):
        with self.lock:
            entry = self._entry(group)
            entry["read"].add(number)
            if message_id and len(message_id) <= 250 and \
                    (entry["last"] is None or number >= entry["last"]["number"]):
                entry["last"] = {"number": number, "message_id": message_id}
            self._compact(entry)
            self._save()

    def mark_through(self, group: str, number: int):
        with self.lock:
            entry = self._entry(group)
            entry["through"] = max(entry["through"], number)
            self._compact(entry)
            self._save()


def default_marks_path(host: str, port: int, user: str) -> Path:
    name = re.sub(r"[^A-Za-z0-9._-]", "-", "%s_%d_%s" % (host, port, user or "anonymous"))
    return Path.home() / ".fn-web" / (name + ".json")


def thread_rows(rows: list) -> list:
    """(row, depth, reply_outside_window) in References order within one window.

    A row's parent is the last References entry (RFC 5536 section 3.2.10)
    that names another row in this window; rows with no such parent are
    roots, ordered by local number. Only display order: it decides nothing.
    """
    by_id, parent = {}, {}
    for row in rows:
        if row["message_id"] and row["message_id"] not in by_id:
            by_id[row["message_id"]] = row
    for row in rows:
        refs = row["references"].split()
        if not refs and row.get("in_reply_to"):
            # RFC 5322 section 3.6.4: a reply with no References names its
            # parent in In-Reply-To (mail gateways and some readers do this).
            refs = [row["in_reply_to"]]
        parent[row["number"]] = next((by_id[ref]["number"] for ref in reversed(refs)
                                      if ref in by_id and ref != row["message_id"]), None)
    children = {row["number"]: [] for row in rows}
    roots = []
    for row in sorted(rows, key=lambda one: one["number"]):
        seen, up = {row["number"]}, parent[row["number"]]
        while up is not None and up not in seen:
            seen.add(up)
            up = parent[up]
        if parent[row["number"]] is None or up is not None:
            roots.append(row)          # no parent here, or a References cycle
        else:
            children[parent[row["number"]]].append(row)
    ordered, stack = [], [(row, 0) for row in reversed(roots)]
    while stack:
        row, depth = stack.pop()
        ordered.append((row, depth, bool(row["references"].split() or row.get("in_reply_to"))
                        and depth == 0))
        stack.extend((child, depth + 1) for child in reversed(children[row["number"]]))
    return ordered


def reply_subject(subject: str) -> str:
    subject = subject.strip()
    return (subject if re.match(r"(?i)re:", subject) else "Re: " + subject)[:240]


def reply_references(parent_references: str, parent_id: str) -> str:
    """RFC 5537 section 3.4.4: the parent's References plus its Message-ID.

    Trimmed to the form's bound by removing entries after the first while
    keeping the first and the last three, as that section requires.
    """
    refs = [ref for ref in parent_references.split()
            if ref.startswith("<") and ref.endswith(">")]
    if parent_id:
        refs.append(parent_id)
    while len(" ".join(refs)) > MAX_REFERENCES and len(refs) > 4:
        del refs[1]
    if len(" ".join(refs)) > MAX_REFERENCES:
        refs = [parent_id] if parent_id and len(parent_id) <= MAX_REFERENCES else []
    return " ".join(refs)


def frozen_fields(lines) -> dict:
    """The editable fields of an article this client composed, for a new draft."""
    lines = list(lines or ())
    cut = lines.index("") if "" in lines else len(lines)
    fields = fn_client.headers(lines[:cut])
    return {"subject": fn_client.first(fields, "subject") or "",
            "sender": fn_client.first(fields, "from") or "",
            "references": fn_client.first(fields, "references") or "",
            "body": "\n".join(lines[cut + 1:])}


def verdict_kind(report) -> str:
    if not report:
        return "unavailable"
    return report.split(" ", 1)[0].rstrip(":")


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
    if outcome == "carried" and len(fields) == 3 and re.fullmatch(r"[0-9a-fA-F]{64}", fields[2]):
        # D23 (identity spec, "Carried, not verified"): held for a neighbour
        # whose boundary lists this principal; the node verified nothing.
        return ("carried for principal " + fields[2].lower() +
                "; this node verified nothing")
    if outcome == "revoked":
        # spike/peering's renderer (tools/fn_verify.py there): revoked at
        # keyring generation G; not `verified`.
        if len(fields) == 5 and re.fullmatch(r"[0-9a-fA-F]{64}", fields[2]) and \
                fields[3] == "keyring" and fields[4].isascii() and fields[4].isdecimal():
            return ("revoked: principal " + fields[2].lower() + " revoked at keyring "
                    "generation " + fields[4])
        return None
    if outcome == "withdrawn" and 3 <= len(fields) <= 8 and \
            all(len(one) <= 80 and one.isprintable() for one in fields[2:]):
        # SPIKE: defers the grammar of these tokens to the control spike's
        # ACL2 renderer; the reader shows the node's words and infers nothing.
        return outcome + ": " + " ".join(fields[2:])
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
    if row.get("count") is not None:
        address += " · %d article%s" % (row["count"], "" if row["count"] == 1 else "s")
    policy = {"y": "posting allowed", "n": "read only", "m": "moderated"}.get(
        row["status"], "status " + row["status"])
    return address + " · " + policy


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
.verified { background:#daf1df; color:#0f4a2a } .unverified { background:#fae0d9; color:#7a2217 }
.absent,.unavailable { background:#ecebe4; color:#4a4a42 } .withdrawn { background:#d9d9d9; color:#333 } .control { background:#e8eef7; color:#233 } .unread { font-weight:700 }
.unread-dot { color:#922e24 } .reason { font-family:ui-monospace, monospace; background:#fdf1ee; padding:.5rem .8rem; border-radius:6px; overflow-wrap:anywhere }
.identity { font-size:.85rem } .resume code { overflow-wrap:anywhere } form.inline { display:inline }
form.inline button { padding:.35rem .7rem; font-size:.85rem } .row { display:flex; gap:.6rem; flex-wrap:wrap }
.row label { flex:1 1 12rem }
.carried { background:#e3e9f7; color:#1f3a73 } .revoked,.withdrawn { background:#f3dff0; color:#6b1f5e }
.depth-1 { margin-left:18px } .depth-2 { margin-left:36px } .depth-3 { margin-left:54px }
.depth-4,.depth-5,.depth-6,.depth-7,.depth-8 { margin-left:72px }
.search { display:flex; gap:.5rem; flex-wrap:wrap; align-items:end } .search label { flex:1 1 10rem }
.search select { padding:.6rem; margin:.2rem 0 .9rem } table.ops { border-collapse:collapse; width:100% }
table.ops td,table.ops th { text-align:left; padding:.3rem .5rem; border-bottom:1px solid #d9e1d9; overflow-wrap:anywhere }
.signing { border-left:3px solid #1f3a73; padding:.4rem .8rem; background:#eef2fb }
.check { display:flex; gap:.5rem; align-items:center; font-weight:400 } .check input { width:auto; margin:0 }
@media (max-width: 600px) {
  body { padding: .8rem .75rem 4rem } h1 { font-size:1.4rem } h2 { font-size:1.15rem }
  header { flex-wrap:wrap; gap:.3rem } .identity { flex-basis:100% }
  .card, article { padding:.75rem .8rem; border-radius:8px }
  .depth-1 { margin-left:8px } .depth-2 { margin-left:16px } .depth-3 { margin-left:24px }
  .depth-4,.depth-5,.depth-6,.depth-7,.depth-8 { margin-left:32px }
  nav a { display:inline-block; margin:.2rem .8rem .2rem 0 } button,.button { width:100%; margin:.2rem 0 }
  form.inline button { width:auto } textarea { min-height:9rem }
}
"""

# Served as /static/draft.js (script-src 'self'). Restores a draft kept in
# this browser's origin storage and saves it on
# every edit. Per-viewer convenience only: the durable outbox (Save draft)
# is the record that survives a client restart.
DRAFT_SCRIPT = """
(function(){var f=document.querySelector('form[data-draft-key]');if(!f)return;
var k='fn-draft:'+f.getAttribute('data-draft-key');var names=['subject','sender','body'];
function get(){try{return JSON.parse(localStorage.getItem(k)||'null')}catch(e){return null}}
var d=get();if(d){var empty=names.every(function(n){var el=f.elements[n];return !el||!el.value||el.defaultValue===el.value});
 if(empty&&!f.hasAttribute('data-seeded')){names.forEach(function(n){if(f.elements[n]&&d[n]!=null)f.elements[n].value=d[n]});
 var note=document.getElementById('draft-note');if(note)note.textContent='Restored the draft this browser kept for this form.'}}
f.addEventListener('input',function(){var o={};names.forEach(function(n){if(f.elements[n])o[n]=f.elements[n].value});
 try{localStorage.setItem(k,JSON.stringify(o))}catch(e){}});})();
"""
CLEAR_SCRIPT = """
(function(){var m=document.querySelector('[data-clear-draft]');if(!m)return;
try{localStorage.removeItem('fn-draft:'+m.getAttribute('data-clear-draft'))}catch(e){}})();
"""


def draft_key(group: str, references: str) -> str:
    refs = references.split()
    return group + "|" + (refs[-1] if refs else "new")


def verdict_badge(report) -> str:
    kind = verdict_kind(report)
    return ("<span class='badge " + e(kind) + "' title='" +
            e(report or "server report unavailable") + "'>" + e(kind) + "</span>")


class Handler(BaseHTTPRequestHandler):
    server: "WebServer"

    def setup(self):
        super().setup()
        self.connection.settimeout(15)

    def log_message(self, *_args) -> None:
        # Paths contain article identifiers and form handling may carry private
        # content. The local UI does not put requests into access logs.
        pass

    def page(self, title: str, content: str, status: int = 200, script: str = ""):
        page = ("<!doctype html><html lang='en'><meta charset='utf-8'>"
                "<meta name='viewport' content='width=device-width,initial-scale=1'>"
                "<title>" + e(title) + " · fn</title><style>" + STYLE + "</style>"
                "<body><header><h1><a href='/'>fn / news</a></h1>"
                "<span class='identity muted'>" + e(self.server.identity) + "</span>"
                + ("<a href='/outbox'>Local outbox</a>" if getattr(
                    self.server.submissions, "durable", False) else
                   "<span class='muted'>local reader</span>") +
                "</header><nav class='top'><a href='/'>Groups</a><a href='/operator'>Node</a></nav>"
                + content + ("<script src='/static/" + script + ".js'></script>"
                             if script else "") + "</body></html>")
        encoded = page.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(encoded)))
        self.send_header("Cache-Control", "no-store")
        # Chromium sends Origin: null for a same-origin form when no-referrer
        # is set; same-origin still prevents a referrer going to another site.
        self.send_header("Referrer-Policy", "same-origin")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", "default-src 'none'; style-src 'unsafe-inline'; script-src 'self'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'")
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
            if entry.get("record_error"):
                self.page("Outbox write uncertain", "<p class='hint'>" +
                          e(entry["record_error"]) + ". No NNTP POST was made by this "
                          "attempt. The local record may have changed; new submissions "
                          "are fenced until restart and inspection.</p>", 503)
                return
            self.page("Draft", "<p>This form has not been submitted.</p>", 200)
            return
        word, msgid = result.word, entry["message_id"]
        group = entry["group"]
        source = "\n".join(entry["lines"] or ())
        clear = ""
        if word == fn_client.ACCEPTED:
            fields = frozen_fields(entry["lines"])
            clear = ("<span data-clear-draft='" + e(draft_key(group, fields["references"])) +
                     "'></span>")
            meaning = "The node answered that it accepted this article."
            said = ("<p>The node's answer:</p><p class='reason'>" +
                    e(result.detail.rsplit(msgid, 1)[-1].strip() or result.detail) + "</p>"
                    "<p><a href='" + e(href("/g", name=group)) + "'>Back to " + e(group) +
                    "</a></p>")
        elif word == fn_client.REFUSED:
            meaning = "The node refused this exact article. This form will not post it again."
            said = ("<p>The node's reason, as it sent it (the 441 text is the node's ACL2 "
                    "decision word, not this client's):</p><p class='reason'>" +
                    e(result.detail) + "</p><p>Nothing was stored. You can edit the text "
                    "into a new post; it gets a new Message-ID.</p><p><a class='button' href='" +
                    e(href("/compose", group=group, edit=token)) +
                    "'>Edit as a new post</a></p>")
        else:
            meaning = ("The article may or may not have been accepted. Do not post a "
                       "new copy while its status is unknown.")
            said = ("<p class='reason'>" + e(result.detail) + "</p>"
                    "<p class='hint'>Do not repost. Your text is kept below exactly as it "
                    "was sent" + (", and in the local outbox across restarts"
                                   if getattr(self.server.submissions, "durable", False)
                                   else ", while this process runs") +
                    ". Check the Message-ID first: if the node serves it, it was accepted.</p>")
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
        signed = any(line.lower().startswith("fn-authorship:") for line in (entry["lines"] or ()))
        self.page("Post " + word, clear + "<article>"
                  "<span class='badge " + e(word) + "'>" + e(word) + "</span>"
                  "<h2>" + e(meaning) + "</h2>"
                  "<p class='meta'>Message-ID: <code>" + e(msgid) + "</code> · " +
                  ("signed on this machine (FN-Authorship carrier)" if signed else "unsigned") +
                  "</p>" + said
                  + observed + "<p><a href='" + e(href("/settle", id=token)) +
                  "'>Check whether the node serves this Message-ID</a></p>"
                  "<details" + (" open" if word == fn_client.UNCERTAIN else "") +
                  "><summary>The exact article sent</summary><pre>" + e(source) +
                  "</pre></details>"
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
                  "</article>", script="clear" if clear else "")

    def control_html(self, control):
        """spike/control: the node's report on a control article, labelled as
        the node's claim.  A withdrawal names its target and its basis."""
        if not control:
            return ""
        words = control.split()
        if words[:2] == ["executed", "withdrawal"] and len(words) >= 4:
            return ("<p><span class='badge withdrawn'>withdrawn by " + e(words[3]) +
                    "</span> <span class='meta'>this cancel withdrew <code>" +
                    e(words[2]) + "</code> (node's report; readers of this node "
                    "no longer see it)</span></p>")
        return ("<p><span class='badge control'>control: " + e(control) +
                "</span> <span class='meta'>(node's report)</span></p>")

    def article_html(self, group, number, one, verdict, has_verdict_lookup,
                     control=None):
        fields = one["headers"]
        first = lambda name: fn_client.first(fields, name) or ""
        statement = bool(first("fn-statement"))
        carrier = bool(first("fn-authorship"))
        kind = verdict_kind(verdict) if has_verdict_lookup else "unavailable"
        badge = ("<p><span class='badge " + e(kind) + "'>node verdict: " + e(kind) +
                 "</span></p>")
        verdict_html = (("<p class='meta'>Server report of historical verification "
                         "verdict: " + e(verdict) + ". This reports what this node "
                         "recorded; it is not an independent cryptographic check or "
                         "current authorization.</p>") if verdict else
                        "<p class='meta'>Server report of historical verification "
                        "verdict: unavailable" +
                        ("" if has_verdict_lookup else
                         " (HDR :fn-verified needs a group and local number; this view "
                         "was reached by Message-ID)") + ".</p>")
        provenance = (badge + self.control_html(control) +
                      "<p class='hint'><strong>Who wrote this?</strong> The displayed "
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
                      "<br>References: " + e(first("references") or "none") +
                      "</p></details><p class='muted'>Viewing does not acknowledge application processing.</p>")
        msgid = one["message_id"] or ""
        resume = ""
        if number and msgid:
            resume = ("<details class='resume'><summary>Resume from here</summary>"
                      "<p class='meta'>Group <code>" + e(group) + "</code>, local #" +
                      e(number) + ", Message-ID <code>" + e(msgid) + "</code>. Local "
                      "numbers belong to this node; the Message-ID is what the resume "
                      "checks the number against.</p><p><a href='" +
                      e(href("/resume", group=group, number=number, id=msgid)) +
                      "'>Open the articles after this one</a></p><p class='meta'>Command "
                      "line: <code>" + e("fn_client.py read %s --since %d" % (group, number)) +
                      "</code></p></details>")
        nav = ("<nav><a href='" + e(href("/g", name=group)) + "'>" + e(group) +
               "</a><a href='" + e(href("/compose", group=group, reply=number)) +
               "'>Reply</a></nav>" if group and number else
               "<nav><a href='/'>Groups</a></nav>")
        return (nav + "<article><h2>" + e(first("subject") or "(no subject)") +
                "</h2><p class='meta'>" + e(msgid) +
                (" · local #" + e(number) if number else
                 " · local number not reported by a lookup by Message-ID") + "</p>" +
                provenance + "<pre>" + e("\n".join(one["body"])) + "</pre>" + resume +
                "</article>")

    def marks_note(self) -> str:
        error = self.server.marks.error
        return "<p class='hint'>" + e(error) + ".</p>" if error else ""

    def search_form(self, group, field="subject", query="") -> str:
        return ("<form class='search' method='get' action='/search'>"
                "<input type='hidden' name='group' value='" + e(group) + "'>"
                "<label>Search " + e(group) + "<input name='q' maxlength='120' value='" +
                e(query) + "' placeholder='text in the subject or author'></label>"
                "<select name='field' aria-label='field'>" +
                "".join("<option value='%s'%s>%s</option>" % (value, " selected" if value == field
                                                              else "", label)
                        for value, label in (("subject", "Subject"), ("from", "Author"))) +
                "</select><button type='submit'>Search</button></form>")

    def search_page(self, values):
        group, field, query = values.get("group", ""), values.get("field", "subject"), values.get("q", "")
        if not group_token(group):
            raise ValueError("invalid group name")
        before = None
        if "before" in values:
            raw = values["before"]
            if not raw.isascii() or not raw.isdecimal() or len(raw) > 10 or int(raw) < 1:
                raise ValueError("invalid search window")
            before = int(raw)
        result = self.run_backend(lambda: self.server.backend.search(group, field, query, before))
        if result is None:
            return
        if result.word != fn_client.DONE:
            self.outcome(result.word, result.detail + (" (" + result.data["command"] + ")"
                                                       if result.data.get("command") else ""))
            return
        data, marks = result.data, self.server.marks
        rows = "".join(
            "<article><h2" + ("" if marks.is_read(group, hit["number"]) else " class='unread'") +
            "><a href='" + e(href("/a", group=group, number=hit["number"])) + "'>" +
            e(hit["subject"]) + "</a></h2><p class='meta'>" +
            e(" · ".join(x for x in (hit["from"], hit["date"], "local #%d" % hit["number"]) if x)) +
            "</p></article>" for hit in sorted(data["hits"], key=lambda h: -h["number"]))
        older = ("<a rel='prev' href='" + e(href("/search", group=group, field=field, q=query,
                                                  before=data["start"] - 1)) +
                 "'>Search older articles</a>" if data["start"] > data["low"] else "")
        self.page("Search " + group, "<nav><a href='" + e(href("/g", name=group)) + "'>" +
                  e(group) + "</a></nav>" + self.search_form(group, field, query) +
                  "<p class='muted'>The node answered <code>" + e(data["command"] or
                  "nothing: the window is empty") + "</code> over local numbers " +
                  e("%d–%d" % (data["start"], data["end"])) + " (at most %d numbers per page, "
                  "case-sensitive, reserved wildmat characters and spaces match any one "
                  "character). This page keeps no index.</p>" % SEARCH_SPAN +
                  (rows or "<p>No matches in this window.</p>") + "<nav>" + older + "</nav>")

    def operator_page(self):
        result = self.run_backend(self.server.backend.overview_counts)
        if result is None:
            return
        data = result.data
        groups = "".join("<tr><td>" + e(row["group"]) + "</td><td>" + e(row.get("count")) +
                         "</td><td>" + e("%s–%s" % (row["first"], row["last"])) + "</td><td>" +
                         e(row["status"]) + "</td></tr>" for row in data["groups"])
        local = ""
        for label, command, output, code in self.server.operator_reports():
            local += ("<tr><th>" + e(label) + "</th><td><code>" + e(command) + "</code><br>exit " +
                      e(code) + "<pre>" + e(output) + "</pre></td></tr>")
        self.page("Node", "<h2>Node</h2><p class='muted'>Read-only. Every value here is the "
                  "node's answer or a local command's output, shown verbatim.</p>"
                  "<article><h2>Over NNTP</h2><p class='meta'>" + e(data["date"]) + "</p>"
                  "<table class='ops'><tr><th>group</th><th>articles</th><th>numbers</th>"
                  "<th>status</th></tr>" + groups + "</table><details><summary>Capabilities"
                  "</summary><pre>" + e("\n".join(data["capabilities"])) + "</pre></details>"
                  "</article><article><h2>On this machine</h2>" +
                  ("<table class='ops'>" + local + "</table>" if local else
                   "<p class='meta'>No --operator-store was given; status, headroom, peers and "
                   "pins need the operator's local Store and image.</p>") + "</article>")

    def resume_form(self) -> str:
        return ("<details><summary>Resume from a (group, local number, Message-ID)</summary>"
                "<form method='get' action='/resume'><div class='row'>"
                "<label>Group<input name='group' maxlength='240' required></label>"
                "<label>Local number<input name='number' maxlength='10' inputmode='numeric' required></label>"
                "<label>Message-ID<input name='id' maxlength='250' required></label></div>"
                "<button type='submit'>Resume after it</button></form>"
                "<p class='meta'>The node is asked what it serves at that number now; "
                "if it is not the same Message-ID, you are told so instead of being "
                "moved.</p></details>")

    def compose_form(self, token, group, subject="", sender="", references="", body=""):
        save = ("<button name='action' value='save' type='submit' formnovalidate>"
                "Save draft</button> "
                if getattr(self.server.submissions, "durable", False) else "")
        signer = self.server.backend.signer
        signing = ("<div class='signing'><label class='check'><input type='checkbox' name='sign' "
                   "value='1' checked> Sign with principal <code>" + e(signer.principal[:16]) +
                   "…</code></label><p class='meta'>The key stays on this machine; the local fn "
                   "image renders and signs ACL2's preimage. The node then judges the carrier "
                   "against its own enrollment and answers 240 or 441 with its reason.</p></div>"
                   if signer is not None else
                   "<p class='meta'>Unsigned: this client has no signing key "
                   "(start it with --signing-key).</p>")
        seeded = " data-seeded" if (subject and not references) or body else ""
        return ("<form method='post' action='/post' data-draft-key='" +
                e(draft_key(group, references)) + "'" + seeded + ">"
                "<p id='draft-note' class='meta'></p>"
                "<input type='hidden' name='csrf' value='" + e(self.server.token) + "'>"
                "<input type='hidden' name='group' value='" + e(group) + "'>"
                "<input type='hidden' name='submission_id' value='" + e(token) + "'>"
                "<input type='hidden' name='references' value='" + e(references) + "'>"
                "<label>Subject<input name='subject' maxlength='240' required value='" +
                e(subject[:240]) + "'></label>"
                + ("<p class='meta'>In reply to: <code>" + e(references.split()[-1]) +
                   "</code> (References carries " + e(len(references.split())) +
                   " Message-ID(s))</p>" if references.split() else "") +
                "<label>From (optional)<input name='sender' maxlength='240' value='" +
                e(sender) + "' placeholder='" + e(self.server.backend.default_from()) +
                "'></label>"
                "<label>Message<textarea name='body' maxlength='16384' required>" +
                e(body) + "</textarea></label>" + signing + save +
                "<button name='action' value='post' type='submit'>Post to " + e(group) +
                "</button></form>")

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
                marks = self.server.marks
                cards = []
                for row in result.data["groups"]:
                    unread, exact = marks.unread(row)
                    last = marks.last(row["group"])
                    cards.append(
                        "<article><h2><a href='" + e(href("/g", name=row["group"])) +
                        "'>" + e(row["group"]) + "</a> <span class='badge" +
                        (" unread" if unread else "") + "'>" +
                        e(("%d unread" if exact else "at most %d unread") % unread
                          if unread else "nothing unread") +
                        "</span></h2><p class='meta'>" + e(group_summary(row)) + "</p>" +
                        ("<p class='meta resume'>Resume from local #" + e(last["number"]) +
                         " <code>" + e(last["message_id"]) + "</code> · <a href='" +
                         e(href("/resume", group=row["group"], number=last["number"],
                                id=last["message_id"])) + "'>continue after it</a></p>"
                         if last else "") + "</article>")
                self.page("Groups", "<h2>Groups</h2>" + self.marks_note() +
                          ("".join(cards) or "<p>No groups are served.</p>") +
                          self.resume_form())
            elif path in ("/static/draft.js", "/static/clear.js"):
                body = (DRAFT_SCRIPT if path.endswith("draft.js") else CLEAR_SCRIPT).encode()
                self.send_response(200)
                self.send_header("Content-Type", "text/javascript; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("X-Content-Type-Options", "nosniff")
                self.end_headers()
                self.wfile.write(body)
            elif path == "/search":
                self.search_page(values)
            elif path == "/operator":
                self.operator_page()
            elif path == "/outbox" and getattr(self.server.submissions, "durable", False):
                with self.server.submissions.lock:
                    rows = [(token, entry["message_id"],
                             entry["result"].word if entry["result"] else
                             ("local write uncertain" if entry.get("record_error") else "draft"),
                             entry.get("draft"), entry.get("record_error"))
                            for token, entry in self.server.submissions.entries.items()
                            if entry["message_id"] or entry.get("draft") is not None]
                cards = "".join(
                    ("<article><a href='" + e(href("/draft", id=token)) + "'>Draft: " +
                     e(draft["subject"] or "(untitled)") + "</a>" +
                     (" · local write uncertain" if error else "") + "</article>"
                     if draft is not None
                     else "<article><a href='" + e(href("/result", id=token)) +
                     "'>" + e(msgid) + "</a> · " + e(word) + "</article>")
                    for token, msgid, word, draft, error in rows)
                self.page("Outbox", "<nav><a href='/'>Groups</a></nav><h2>Local outbox</h2>" +
                          (cards or "<p>No saved drafts or submitted records.</p>"))
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
                marks = self.server.marks
                cards = "".join(
                    "<article class='thread depth-" + str(min(depth, 8)) + "'><h2" + ("" if marks.is_read(group, row["number"]) else
                                 " class='unread'") + ">" +
                    ("" if marks.is_read(group, row["number"]) else
                     "<span class='unread-dot' title='not opened in this client'>● </span>") +
                    "<a href='" + e(href("/a", group=group, number=row["number"])) + "'>" +
                    e(row["subject"]) + "</a> " + verdict_badge(row.get("verdict")) +
                    "</h2><p class='meta'>" +
                    e(" · ".join(x for x in (row["from"], row["date"],
                                             "local #%s" % row["number"],
                                             "reply to an article outside this window"
                                             if outside else "") if x)) +
                    "</p></article>"
                    for row, depth, outside in thread_rows(rows))
                mark_all = (("<form class='inline' method='post' action='/mark'>"
                             "<input type='hidden' name='csrf' value='" + e(self.server.token) +
                             "'><input type='hidden' name='group' value='" + e(group) +
                             "'><input type='hidden' name='through' value='" + e(min(end, high)) +
                             "'><button type='submit'>Mark read through local #" +
                             e(min(end, high)) +
                             "</button></form>") if rows else "")
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
                          e(page_window + frontier) + " · viewing does not acknowledge processing</p>" +
                          self.search_form(group) +
                          "<p class='muted'>Threaded by References (In-Reply-To when a reply "
                          "has none) within this window. "
                          "Unread marks are this client's, not the node's.</p>" +
                          self.marks_note() +
                          "<nav aria-label='Article number windows'>" + older + " " + newer +
                          " " + mark_all + "</nav>" +
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
                self.server.marks.mark(group, number, one["message_id"] or "")
                self.page(fn_client.first(one["headers"], "subject") or "Article",
                          self.article_html(group, number, one,
                                            result.data.get("fn_verified_report"), True,
                                            result.data.get("fn_control_report")))
            elif path == "/compose":
                group = values.get("group", "")
                if not group_token(group):
                    raise ValueError("invalid group name")
                subject, references, sender, body = "", "", "", ""
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
                    subject = reply_subject(fn_client.first(fields, "subject") or "")
                    references = reply_references(fn_client.first(fields, "references") or "",
                                                  fn_client.first(fields, "message-id") or "")
                elif "edit" in values:
                    # Only a refused submission's text may seed a new post: the
                    # node said it stored nothing. An uncertain one never does.
                    old = values["edit"]
                    if not old or len(old) > 64:
                        raise ValueError("invalid submission identifier")
                    entry = self.server.submissions.get(old)
                    if entry is None or entry["result"] is None or \
                            entry["result"].word != fn_client.REFUSED or entry["group"] != group:
                        raise ValueError("only a refused submission of this group can be edited "
                                         "into a new post")
                    fields = frozen_fields(entry["lines"])
                    subject, sender = fields["subject"], fields["sender"]
                    references, body = fields["references"], fields["body"]
                    if sender == self.server.backend.default_from():
                        sender = ""
                submission_id = self.server.submissions.new(group)
                form = self.compose_form(submission_id, group, subject, sender,
                                         references, body)
                self.page("Compose", "<nav><a href='" + e(href("/g", name=group)) +
                          "'>" + e(group) + "</a></nav><h2>Write a post</h2>"
                          "<p class='muted'>One form sends one exact article. If the reply "
                          "is uncertain, keep its Message-ID and check it before trying again.</p>" + form,
                          script="draft")
            elif path == "/draft" and getattr(self.server.submissions, "durable", False):
                token = values.get("id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                with self.server.submissions.lock:
                    entry = self.server.submissions.entries.get(token)
                    draft = dict(entry["draft"]) if entry and entry.get("draft") else None
                    group = entry["group"] if entry else ""
                    record_error = entry.get("record_error") if entry else None
                if draft is None:
                    self.page("Draft unavailable", "<p>No saved draft has this identifier.</p>", 410)
                    return
                self.page("Saved draft", "<nav><a href='/outbox'>Outbox</a></nav>"
                          "<h2>Saved draft</h2><p class='muted'>Editing does not contact the node. "
                          "Posting freezes one exact article and sends it once.</p>" +
                          ("<p class='hint'>" + e(record_error) +
                           ". This draft's latest local save is uncertain.</p>"
                           if record_error else "") +
                          self.compose_form(token, group, draft["subject"], draft["sender"],
                                            draft["references"], draft["body"]),
                          script="draft")
            elif path in ("/result", "/settle"):
                token = values.get("id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                self.submission_result(token, settle=(path == "/settle"))
            elif path == "/find":
                msgid, within = values.get("id", ""), values.get("group", "")
                if not (len(msgid) <= 250 and msgid.startswith("<") and msgid.endswith(">")
                        and "\r" not in msgid and "\n" not in msgid):
                    raise ValueError("invalid Message-ID")
                if within and not group_token(within):
                    raise ValueError("invalid group name")
                # With a group, the node selects it first and answers the
                # article's local number there, or 0 when it is not in it
                # (RFC 3977 section 6.2.1.2): that number is a resume point.
                result = self.run_backend(lambda: self.server.backend.using(
                    lambda client: client.show(msgid, within)))
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail, msgid)
                    return
                one = result.data["articles"][0]
                groups = (fn_client.first(one["headers"], "newsgroups") or "").split(",")
                found = one["number"] if within else None
                if found:
                    where = ("<p class='meta resume'>Local #" + e(found) + " in " + e(within) +
                             " · <a href='" + e(href("/resume", group=within, number=found,
                                                    id=msgid)) +
                             "'>continue after it</a> · <a href='" +
                             e(href("/g", name=within, start=found,
                                    end=min(MAX_ARTICLE_NUMBER, found + MAX_RECENT - 1))) +
                             "'>open the group from here</a></p>")
                elif within:
                    where = ("<p class='meta'>The node does not carry it in " + e(within) +
                             " (it answered local number 0).</p>")
                else:
                    where = ""
                shown = within if found else (groups[0].strip() if group_token(
                    groups[0].strip()) else "")
                self.page(fn_client.first(one["headers"], "subject") or "Article",
                          "<p><span class='badge done'>served</span> The node serves "
                          "<code>" + e(msgid) + "</code>.</p>" + where +
                          self.article_html(shown, found or None, one, None, False))
            elif path == "/resume":
                group, raw, msgid = (values.get("group", ""), values.get("number", ""),
                                     values.get("id", ""))
                if not group_token(group) or not raw.isascii() or not raw.isdecimal() or \
                        len(raw) > 10 or int(raw) < 1 or not (
                            len(msgid) <= 250 and msgid.startswith("<") and
                            msgid.endswith(">") and "\r" not in msgid and "\n" not in msgid):
                    raise ValueError("a resume point is a group, a local number and a Message-ID")
                number = int(raw)
                result = self.run_backend(lambda: self.server.backend.slot(group, number))
                if result is None:
                    return
                if result.word != fn_client.DONE:
                    self.outcome(result.word, result.detail)
                    return
                row, high = result.data["row"], result.data["high"]
                if row is not None and row["message_id"] == msgid:
                    start = number + 1
                    end = min(MAX_ARTICLE_NUMBER, number + MAX_RECENT)
                    if high is not None and start > high:
                        self.page("Resume", "<nav><a href='" + e(href("/g", name=group)) +
                                  "'>" + e(group) + "</a></nav><p>Local #" + e(number) +
                                  " still carries <code>" + e(msgid) + "</code>. Nothing "
                                  "newer: the group ends at local #" + e(high) + ".</p>")
                        return
                    self.redirect(href("/g", name=group, start=start, end=end))
                    return
                now = ("the node serves <code>" + e(row["message_id"]) + "</code> there"
                       if row else "the node serves no article at that number")
                self.page("Resume point moved", "<nav><a href='" + e(href("/g", name=group)) +
                          "'>" + e(group) + "</a></nav><article><span class='badge refused'>"
                          "not the same article</span><h2>Local #" + e(number) + " in " +
                          e(group) + " is not <code>" + e(msgid) + "</code></h2><p>Now " +
                          now + ". The article was removed, or this node's local numbering "
                          "is not the one the resume point was taken from. The client does not "
                          "guess a new position.</p><p><a href='" + e(href("/find", id=msgid, group=group)) +
                          "'>Look up the Message-ID</a> · <a href='" +
                          e(href("/g", name=group)) + "'>Open the newest articles</a></p>"
                          "</article>", 409)
            else:
                self.page("Not found", "<p>Page not found.</p>", 404)
        except ValueError as exc:
            self.page("Invalid request", "<p>" + e(exc) + "</p>", 400)
        except OutboxFull as exc:
            self.page("Outbox full", "<p>" + e(exc) + "</p>", 507)
        except OutboxError as exc:
            self.page("Outbox unavailable", "<p>" + e(exc) + "</p>", 503)

    def do_POST(self):
        if not self.valid_host() or self.path not in ("/post", "/mark"):
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
                                                    max_num_fields=17).items()}
            if not hmac.compare_digest(values.get("csrf", ""), self.server.token):
                self.page("Refused", "<p>Form token is invalid.</p>", 403)
                return
            if self.path == "/mark":
                # Local read marks only; nothing is sent to the node.
                group, through = values.get("group", ""), values.get("through", "")
                if not group_token(group) or not through.isascii() or \
                        not through.isdecimal() or len(through) > 10:
                    raise ValueError("invalid read mark")
                self.server.marks.mark_through(group, int(through))
                self.redirect(href("/g", name=group))
                return
            submission_id = values.get("submission_id", "")
            if not submission_id or len(submission_id) > 64:
                raise ValueError("invalid submission identifier")
            group, subject = values.get("group", ""), values.get("subject", "")
            sender, references, body = (values.get("sender", ""),
                                        values.get("references", ""), values.get("body", ""))
            action = values.get("action", "post")
            if action not in ("post", "save") or \
                    (action == "save" and not getattr(self.server.submissions,
                                                       "durable", False)):
                raise ValueError("invalid submission action")
            if (not group_token(group) or len(subject) > 240 or
                    len(sender) > 240 or len(references) > 800 or len(body.encode()) > MAX_BODY or
                    (action == "post" and (not subject or not body.strip())) or
                    any("\r" in x or "\n" in x
                                            for x in (subject, sender, references)) or
                    any(len(line.encode()) > 998 for line in body.splitlines())):
                raise ValueError("post fields are invalid or too large")
            if action == "save":
                entry = self.server.submissions.save_draft(
                    submission_id, group, subject, sender, references, body)
            else:
                entry = self.server.submissions.submit(
                    submission_id, group, subject, sender, references, body,
                    values.get("sign") == "1")
            if entry is None:
                self.page("Submission unavailable", "<p>This form's local record "
                          "expired or the web client restarted. No POST was sent.</p>", 410)
                return
            self.redirect(href("/draft" if action == "save"
                               else "/result", id=submission_id))
        except SigningError as exc:
            self.page("Not signed", "<p class='hint'>" + e(exc) + ". Nothing was sent to the "
                      "node.</p>", 500)
        except (ValueError, UnicodeDecodeError) as exc:
            self.page("Invalid post", "<p>" + e(exc) + "</p>", 400)
        except OutboxFull as exc:
            self.page("Outbox full", "<p>" + e(exc) + "</p>", 507)
        except OutboxError as exc:
            self.page("Outbox unavailable", "<p>" + e(exc) + "</p>", 503)


class WebServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, port: int, backend: Backend, outbox: Optional[Path] = None,
                 marks: Optional[ReadMarks] = None, identity: str = ""):
        self.backend = backend
        self.token = secrets.token_urlsafe(32)
        self.marks = marks if marks is not None else ReadMarks(None, backend.node,
                                                                backend.user)
        self.identity = identity or (
            "plain loopback node " + backend.node if backend.args.plain else
            "%s at %s over TLS" % (backend.user, backend.node))
        self.submissions = (DurableSubmissionBook(backend, outbox) if outbox else
                            SubmissionBook(backend))
        try:
            super().__init__(("127.0.0.1", port), Handler)
        except Exception:
            if outbox:
                self.submissions.close()
            raise

    operator = None

    def operator_reports(self):
        """Read-only local status commands, run only when the operator named a Store.

        SPIKE: defers a live read-only status verb to the owner.  While an
        owner holds the Store these commands answer `store is already locked`
        and the page shows exactly that.
        """
        op = self.operator
        if not op:
            return []
        image, tree = op["image"], op.get("tree") or None
        commands = [("status and headroom", [image, "--fn", "store", op["store"], "status"]),
                    ("retention pins", [image, "--fn", "store", op["store"], "retention"])]
        if op.get("config") and tree:
            commands.append(("peers", [sys.executable, str(Path(tree) / "bin" / "fn"),
                                       "--config", op["config"], "peer", "list"]))
        out = []
        for label, command in commands:
            try:
                done = subprocess.run(command, cwd=tree, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, timeout=60, check=False)
                out.append((label, " ".join(command[1:] if command[0] == image else command[1:]),
                            done.stdout.decode("utf-8", "replace")[-2000:], done.returncode))
            except (OSError, subprocess.TimeoutExpired) as exc:
                out.append((label, " ".join(command), str(exc), "none"))
        return out

    def server_close(self):
        super().server_close()
        if getattr(self.submissions, "durable", False):
            self.submissions.close()


def web_credentials(args, parser, environ=None, prompt=None):
    """The principal and its password: --credentials, or --user/FN_CLIENT_USER plus
    FN_CLIENT_PASSWORD, or a terminal prompt. Never argv, never a page or a file."""
    environ = os.environ if environ is None else environ
    if args.plain:
        return "", ""
    if args.credentials:
        user, password = fn_client.credentials(args, parser)
        if args.user and args.user != user:
            parser.error("--user %s does not match the --credentials file" % args.user)
        return user, password
    user = args.user or environ.get("FN_CLIENT_USER", "")
    if not user:
        parser.error("name the principal with --user or FN_CLIENT_USER")
    password = environ.get("FN_CLIENT_PASSWORD", "")
    if not password:
        if prompt is None:
            if not sys.stdin.isatty():
                parser.error("no password: set FN_CLIENT_PASSWORD, give --credentials, "
                             "or run from a terminal to be prompted")
            prompt = getpass.getpass
        password = prompt("fn password for %s at %s: " % (
            user, fn_client.node_name(args.host, args.port)))
    if not password:
        parser.error("an empty password cannot log in")
    return user, password


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--node", default="127.0.0.1:1119",
                        help="HOST:PORT of the NNTP node")
    # Not `port`: fn_client.resolve writes the NNTP port there from --node,
    # which silently made the HTTP listener try to bind the node's port.
    parser.add_argument("--port", dest="http_port", type=int, default=8919,
                        help="loopback HTTP port")
    parser.add_argument("--tls-cert", "--cafile", dest="cafile",
                        help="the node's certificate (or its CA); STARTTLS is verified against it")
    parser.add_argument("--plain", action="store_true",
                        help="no TLS and no login; loopback development node only")
    parser.add_argument("--user", help="the principal to log in as")
    parser.add_argument("--credentials", help="a mode-0600 file holding `user password`")
    parser.add_argument("--from", dest="sender", default=os.environ.get("FN_CLIENT_FROM", ""),
                        help="default From for new posts (a mailbox; the node checks it)")
    parser.add_argument("--outbox", type=Path,
                        help="private durable local submission directory")
    parser.add_argument("--marks", type=Path,
                        help="local read-marks file (default ~/.fn-web/HOST_PORT_USER.json)")
    parser.add_argument("--no-marks", action="store_true",
                        help="keep read marks in memory only")
    parser.add_argument("--timeout", type=float, default=15.0)
    parser.add_argument("--signing-key", type=Path,
                        help="private directory with principal.bin, ed-public.bin, ed-secret.bin, "
                             "ml-public.pem, ml-private.pem")
    parser.add_argument("--fn-image", type=Path,
                        help="the local fn image that signs (hybrid-sign-carrier) and reports status")
    parser.add_argument("--fn-tree", type=Path, help="the source tree the image runs from")
    parser.add_argument("--operator-store", help="the node's Store, for the read-only Node page")
    parser.add_argument("--operator-config", help="the node's operator config, for its peer list")
    args = parser.parse_args(argv)
    fn_client.resolve(args, parser)
    if args.plain and args.host not in LOOPBACK:
        parser.error("--plain is for a loopback development node; a remote node needs "
                     "--tls-cert and a login")
    if not 0 <= args.http_port < 65536 or not 0 < args.timeout <= 60:
        parser.error("invalid HTTP port or timeout")
    if args.plain and args.user:
        parser.error("--plain sends no login, so --user cannot apply")
    user, password = web_credentials(args, parser)
    signer = None
    if args.signing_key:
        if not args.fn_image:
            parser.error("--signing-key needs --fn-image (the image that signs)")
        try:
            signer = Signer(args.signing_key, args.fn_image, args.fn_tree)
        except (OSError, SigningError) as exc:
            parser.error("signing key: %s" % exc)
    backend = Backend(args, user, password, args.sender, signer)
    checked = backend.login_check()
    if checked.word != fn_client.DONE:
        detail = checked.detail.replace(password, "[password]") if password else checked.detail
        sys.stderr.write("fn web client: %s %s\n" % (checked.word, detail))
        sys.exit(fn_client.EXIT[checked.word])
    tls = checked.data.get("tls")
    identity = ("plain loopback node " + backend.node if args.plain else
                "%s at %s · %s, certificate verified" % (
                    user, backend.node, (tls or {}).get("version") or "TLS"))
    marks = ReadMarks(None if args.no_marks else
                      (args.marks or default_marks_path(args.host, args.port, user)),
                      backend.node, user)
    try:
        with WebServer(args.http_port, backend, args.outbox, marks, identity) as server:
            if args.operator_store and args.fn_image:
                server.operator = {"image": str(args.fn_image.absolute()),
                                   "tree": str(args.fn_tree.absolute()) if args.fn_tree else "",
                                   "store": str(Path(args.operator_store).absolute()),
                                   "config": (str(Path(args.operator_config).absolute())
                                              if args.operator_config else None)}
            print("fn web client: %s; open http://127.0.0.1:%d/" % (identity, server.server_port),
                  flush=True)
            if marks.error:
                print("fn web client: " + marks.error, flush=True)
            server.serve_forever()
    except (OSError, OutboxError) as exc:
        parser.error("local web client: " + str(exc))
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
