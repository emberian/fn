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
LOOPBACK = ("127.0.0.1", "::1")


# Work per search request: the numbers the node is asked to scan in one XPAT,
# and the hits one page shows.  Bounds on work, not on the group, which the
# next page continues past.
SEARCH_SPAN = 2000
MAX_SEARCH_HITS = 200
# A conversation page asks about at most this many References entries (the
# form's References is at most 800 characters) and shows at most MAX_RECENT
# replies per window; the page links the next window.
MAX_THREAD_REFERENCES = 40
# RFC 3977 section 4.1: a wildmat cannot state these characters exactly; the
# conversation query stands `?` for each and says so on the page.
WILDMAT_SPECIAL = set('*?[]\\,!')


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
    def __init__(self, args, user: str, password: str, sender: str = ""):
        self.args, self.user, self.password = args, user, password
        self.sender = sender

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
            # Numbers inside the window and the group's current range that
            # carry no overview row: ask the node what each one is now.  At
            # most MAX_RECENT STATs; the answer (`423 withdrawn`, `423 no
            # article with that number`, or an article that arrived since) is
            # shown as the node sent it.
            holes = []
            if high >= low and window_end >= window_start:
                for one in range(max(window_start, low), min(window_end, high) + 1):
                    if one not in wanted:
                        answer, _ = client.cmd("STAT %d" % one)
                        holes.append({"number": one, "answer": answer})
            return fn_client.Result(fn_client.DONE, status,
                                    {"group": group, "rows": rows, "low": low,
                                     "high": high, "window_start": window_start,
                                     "window_end": window_end, "holes": holes}, "")
        return self.using(query)

    @staticmethod
    def over_row(client, number: int):
        """The node's OVER row for one number, or (None, its answer)."""
        overview, body = client.cmd("OVER %d" % number, multiline=True)
        if overview.startswith("224"):
            for line in body:
                parts = line.split("\t")
                if parts and fn_client.number(parts[0]) == number:
                    return ({"number": number,
                             "subject": parts[1] if len(parts) > 1 else "(no subject)",
                             "from": parts[2] if len(parts) > 2 else "",
                             "date": parts[3] if len(parts) > 3 else "",
                             "message_id": parts[4] if len(parts) > 4 else "",
                             "references": parts[5] if len(parts) > 5 else ""}, overview)
            return None, overview
        return None, overview

    def thread(self, group: str, number: int, before: Optional[int] = None):
        """One conversation around a local article, within a stated scope.

        The article's References are asked about one by one (`STAT <id>`):
        the node answers where it serves each in this group, that it was
        withdrawn, or that it does not serve it.  The replies are the node's
        answer to `XPAT References <low>-<high> *<root>*` over one window of
        at most SEARCH_SPAN numbers ending at `before` (default the group's
        high-water mark): the node matches, over what it serves
        (books/nntp-search-scope.lisp).  The client orders what the node
        answered for display and decides nothing about membership.
        """
        def query(client):
            status, _ = client.cmd("GROUP " + group)
            if not status.startswith("211"):
                return fn_client.Result(fn_client.REFUSED, status, {}, "")
            fields = status.split()
            low = fn_client.number(fields[2]) if len(fields) > 2 else None
            high = fn_client.number(fields[3]) if len(fields) > 3 else None
            if low is None or high is None:
                raise fn_client.Stop(fn_client.UNCERTAIN, "invalid GROUP range: " + status)
            row, answer = self.over_row(client, number)
            if row is None:
                stat, _ = client.cmd("STAT %d" % number)
                return fn_client.Result(fn_client.REFUSED, stat, {"number": number}, "")
            references = row["references"].split()
            root = references[0] if references else row["message_id"]
            ancestors = []
            for ident in references[:MAX_THREAD_REFERENCES]:
                entry = {"message_id": ident, "answer": "", "row": None}
                if not (ident.startswith("<") and ident.endswith(">") and len(ident) <= 250):
                    entry["answer"] = "not a Message-ID; not asked"
                    ancestors.append(entry)
                    continue
                stat, _ = client.cmd("STAT " + ident)
                entry["answer"] = stat
                parts = stat.split()
                if stat.startswith("223") and len(parts) > 1:
                    found = fn_client.number(parts[1])
                    if found:
                        entry["row"], _ = self.over_row(client, found)
                ancestors.append(entry)
            end = min(high, before) if before is not None else high
            start = max(low, end - SEARCH_SPAN + 1)
            pattern = "*" + "".join("?" if c in WILDMAT_SPECIAL else c for c in root) + "*"
            hits, command = [], ""
            if end >= start and high >= low and root.startswith("<"):
                command = "XPAT References %d-%d %s" % (start, end, pattern)
                reply, lines = client.cmd(command, multiline=True)
                if not reply.startswith("221"):
                    return fn_client.Result(fn_client.REFUSED, reply, {"command": command}, "")
                for line in lines[:MAX_SEARCH_HITS]:
                    one = fn_client.number(line.partition(" ")[0])
                    if one is not None and start <= one <= end:
                        hits.append(one)
            shown = sorted(set(hits))[-MAX_RECENT:]
            rows = {row["number"]: row}
            for entry in ancestors:
                if entry["row"]:
                    rows[entry["row"]["number"]] = entry["row"]
            for one in shown:
                if one not in rows:
                    found, _ = self.over_row(client, one)
                    if found:
                        rows[one] = found
            # An earlier message the node does not serve here keeps its place
            # in the conversation as a placeholder carrying the node's answer,
            # so a reply to it is shown under it rather than under its parent.
            placeholders = [
                {"number": -1 - index, "message_id": entry["message_id"],
                 "references": " ".join(references[:index]), "subject": "",
                 "from": "", "date": "", "placeholder": entry["answer"]}
                for index, entry in enumerate(ancestors) if not entry["row"]]
            return fn_client.Result(fn_client.DONE, status, {
                "group": group, "row": row, "root": root, "ancestors": ancestors,
                "rows": placeholders + [rows[k] for k in sorted(rows)],
                "hits": len(set(hits)),
                "shown": len(shown), "start": start, "end": end, "low": low,
                "high": high, "command": command,
                "approximate": any(c in WILDMAT_SPECIAL for c in root)}, "")
        return self.using(query)

    def search(self, group: str, field: str, pattern: str, before: Optional[int] = None):
        """Articles in one bounded number window whose field the node matches.

        The pattern is the reader's wildmat, sent to the node verbatim as
        `XPAT <field> <low>-<high> <pattern>` (RFC 2980 section 2.9): the node
        parses it (books/wildmat.lisp, the header-value profile) and matches
        it, case-sensitively (RFC 3977 section 4.2); arguments separated by
        spaces are joined by the node into one pattern, and the comma is the
        alternative.  This client builds no pattern and keeps no index.  The
        window is SEARCH_SPAN numbers ending at `before` (default the
        high-water mark), a bound on work per request; the page links the
        next older window.
        """
        if field not in ("subject", "from"):
            raise ValueError("search field is subject or from")
        pattern = pattern.strip()
        if not pattern or len(pattern.encode("utf-8")) > 400 or \
                any(ord(c) < 32 or ord(c) == 127 for c in pattern):
            raise ValueError("a search pattern is 1 to 400 octets of printable text")

        def query(client):
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
                    return fn_client.Result(fn_client.REFUSED, answer,
                                            {"command": command}, "")
                for line in lines[:MAX_SEARCH_HITS]:
                    number, _, value = line.partition(" ")
                    one = fn_client.number(number)
                    if one is not None and start <= one <= end:
                        hits.append({"number": one, "value": value})
            return fn_client.Result(fn_client.DONE, status,
                                    {"hits": hits, "start": start, "end": end, "low": low,
                                     "high": high, "command": command}, "")
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
        form = SimpleNamespace(group=group, subject=subject, sender=sender or self.sender,
                               references=references, message_id="", body_file="",
                               host=self.args.host)
        return fn_client.compose(form, self.user, FormErrors(), body)

    def post(self, group: str, lines: tuple[str, ...], msgid: str):
        def send(client):
            answer = client.post(group, list(lines), msgid)
            answer.status_lines = list(client.lines)
            return answer
        try:
            return self.using(send)
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
                                   "result": None, "settlement": None,
                                   "reconciliation": None}
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

    def reconcile(self, token: str):
        """Settle an uncertain POST by re-sending its exact lines (NNT-019).

        The same article under the same Message-ID: the node answers from what
        it stored (D25), including an article since withdrawn or reclaimed.
        The original outcome is never rewritten; the answer is recorded
        beside it.  Only an uncertain original is re-sent, and only until a
        reconciliation settles it."""
        with self.lock:
            entry = self.entries.get(token)
            if entry is None or entry["lines"] is None or entry["result"] is None:
                return entry
            if entry["result"].word != fn_client.UNCERTAIN or \
                    reconciled(entry.get("reconciliation")):
                return entry
            if getattr(self, "fenced", None):
                raise OutboxError(self.fenced)
            try:
                answer = self.backend.post(entry["group"], entry["lines"],
                                           entry["message_id"])
            except (OSError, Disconnected) as exc:
                answer = fn_client.Result(fn_client.UNCERTAIN, str(exc),
                                          {"message_id": entry["message_id"]}, "")
            entry["reconciliation"] = fn_client.reconciliation(answer)
            self._record(token, entry)
            return entry

    def _record(self, token, entry):
        """Memory only; the durable book writes the record."""


def reconciled(result) -> bool:
    return result is not None and result.word in (fn_client.ACCEPTED, fn_client.REFUSED)


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
                        "reconciliation": None,
                        "draft": draft, "original_recorded": False,
                        "record_error": None}
            if not isinstance(saved["lines"], list) or not saved["lines"] or \
                    not all(isinstance(line, str) for line in saved["lines"]) or \
                    len("\r\n".join(saved["lines"]).encode()) > MAX_BODY + 4096 or \
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
            settled = saved.get("reconciliation")
            if settled is not None and (not isinstance(settled, dict) or
                    settled["word"] not in (fn_client.ACCEPTED, fn_client.REFUSED,
                                            fn_client.UNRESOLVED) or
                    not isinstance(settled["detail"], str) or
                    not isinstance(settled.get("settled"), str) or
                    result.word != fn_client.UNCERTAIN):
                raise OutboxError("outbox reconciliation is malformed")
            return {"group": saved["group"], "lines": tuple(saved["lines"]),
                    "message_id": saved["message_id"], "result": result,
                    "reconciliation": (fn_client.Result(settled["word"], settled["detail"],
                                                        {"settled": settled["settled"]}, "")
                                       if settled else None),
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
        settled = entry.get("reconciliation")
        if settled is not None:
            saved["reconciliation"] = {"word": settled.word, "detail": settled.detail,
                                       "settled": settled.data.get("settled", "")}
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
                              if entry["lines"] is None and entry["draft"] is None), None)
                if stale is None:
                    raise OutboxFull("outbox is full; archive records while the client is stopped")
                del self.entries[stale]
            token = secrets.token_urlsafe(24)
            self.entries[token] = {"group": group, "lines": None, "message_id": "",
                                   "result": None, "settlement": None, "draft": None,
                                   "reconciliation": None,
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

    def _recorded(self, entry):
        original = ({"word": entry["result"].word, "detail": entry["result"].detail}
                    if entry["original_recorded"] else None)
        observation = ({"word": entry["settlement"].word,
                        "detail": entry["settlement"].detail}
                       if entry["settlement"] is not None else None)
        return original, observation

    def _record(self, token, entry):
        # Called with the lock held, after a reconciliation answer.
        if self.fenced:
            return
        original = ({"word": entry["result"].word, "detail": entry["result"].detail}
                    if entry["original_recorded"] else None)
        settlement = ({"word": entry["settlement"].word, "detail": entry["settlement"].detail}
                      if entry["settlement"] is not None else None)
        try:
            self._write(token, entry, original, settlement)
        except (OSError, OutboxError) as exc:
            entry["record_error"] = self._fence(exc)

    def settle(self, token):
        entry = super().settle(token)
        with self.lock:
            if entry is not None and entry["settlement"] is not None and not self.fenced:
                try:
                    self._write(token, entry, *self._recorded(entry))
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
        ordered.append((row, depth, bool(row["references"].split()) and depth == 0))
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


def answer_kind(answer: str) -> str:
    """A CSS label for a node's retrieval answer; the text shown is the node's."""
    if answer.startswith(("423 withdrawn", "430 withdrawn")):
        return "withdrawn"
    if answer.startswith(("220", "221", "222", "223")):
        return "served"
    return "unavailable"


def withdrawn_note(answer: str) -> str:
    return ("The node answered <code>" + e(answer) + "</code>: an authorized cancel "
            "withdrew this article from what the node serves. The withdrawal says the "
            "article was held here (C3); people may already have read it, and copies "
            "elsewhere are not erased. The withdrawal is the node's record, not this "
            "reader's.")


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
.accepted { background:#daf1df } .refused { background:#fae0d9 } .uncertain { background:#fff0be } .unresolved { background:#f3e2ff }
.thread { border-left:3px solid #b7d5c6 } pre { white-space:pre-wrap; overflow-wrap:anywhere; font-family:ui-monospace, monospace }
details { margin-top:1rem; border-top:1px solid #d9e1d9; padding-top:.6rem } summary { cursor:pointer; font-weight:650 }
.hint { border-left:3px solid #d1a24b; padding:.5rem .8rem; background:#fff9e8 }
input,textarea { box-sizing:border-box; width:100%; padding:.7rem; margin:.2rem 0 .9rem; border:1px solid #9cad9e; border-radius:6px; font:inherit; background:#fff }
textarea { min-height:12rem } label { display:block; font-weight:650 }
button,.button { display:inline-block; border:0; border-radius:6px; padding:.65rem 1rem; background:#145f50; color:white; font:inherit; cursor:pointer; text-decoration:none }
button:hover,.button:hover { background:#0b4439 } .muted { color:#52645d }
.verified { background:#daf1df; color:#0f4a2a } .unverified { background:#fae0d9; color:#7a2217 }
.absent,.unavailable { background:#ecebe4; color:#4a4a42 } .unread { font-weight:700 }
.unread-dot { color:#922e24 } .reason { font-family:ui-monospace, monospace; background:#fdf1ee; padding:.5rem .8rem; border-radius:6px; overflow-wrap:anywhere }
.identity { font-size:.85rem } .resume code { overflow-wrap:anywhere } form.inline { display:inline }
form.inline button { padding:.35rem .7rem; font-size:.85rem } .row { display:flex; gap:.6rem; flex-wrap:wrap }
.row label { flex:1 1 12rem }
dl.facts { display:grid; grid-template-columns:minmax(9rem,14rem) 1fr; gap:.3rem 1rem; margin:.6rem 0 }
dl.facts dt { font-weight:650 } dl.facts dd { margin:0; overflow-wrap:anywhere }
@media (max-width: 560px) { dl.facts { grid-template-columns:1fr } dl.facts dd { margin-bottom:.4rem } }
.withdrawn { background:#ece3f3; color:#4b2a63 } .hole { border-style:dashed; background:#faf9f4 }
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
                "<span class='identity muted'>" + e(self.server.identity) + "</span>"
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

    def cross_site(self) -> bool:
        # Fetch metadata (W3C Fetch Metadata Request Headers): a browser says
        # where a request came from.  Another site's page, image, iframe or
        # form reaching this loopback reader is refused before any NNTP
        # command or local write; a typed address or bookmark says `none`.
        return self.headers.get("Sec-Fetch-Site", "none") not in ("same-origin", "none")

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

    def submission_result(self, token: str):
        entry = self.server.submissions.get(token)
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
        if word == fn_client.ACCEPTED:
            meaning = "The node answered that it accepted this article."
            said = ("<p>The node's answer:</p><p class='reason'>" +
                    e(result.detail.rsplit(msgid, 1)[-1].strip() or result.detail) + "</p>"
                    "<p><a href='" + e(href("/g", name=group)) + "'>Back to " + e(group) +
                    "</a></p>")
        elif word == fn_client.REFUSED:
            meaning = "The node refused this exact article. This form will not post it again."
            said = ("<p>The node's reason, as it sent it:</p><p class='reason'>" +
                    e(result.detail) + "</p><p>Nothing was stored. You can edit the text "
                    "into a new post; it gets a new Message-ID.</p><p><a class='button' href='" +
                    e(href("/compose", group=group, edit=token)) +
                    "'>Edit as a new post</a></p>")
        else:
            meaning = ("The article may or may not have been accepted. Do not post a "
                       "new copy while its status is unknown.")
            # The walk's third finding: "Do not repost" beside a "Send the
            # same bytes again" button read as a contradiction, and "as it was
            # sent" was false when the connection never opened.
            said = ("<p class='reason'>" + e(result.detail) + "</p>"
                    "<p class='hint'>Do not write this again as a new post: a new post "
                    "gets a new Message-ID, and the node could then hold both. Your "
                    "article is kept below exactly as prepared" +
                    (", and in the local outbox across restarts"
                     if getattr(self.server.submissions, "durable", False)
                     else ", while this process runs") +
                    ". A lookup shows only what this reader is served now: an article can be "
                    "accepted and then withdrawn or reclaimed, and answer 430. To settle it, "
                    "re-send this same article under the same Message-ID; the node answers "
                    "from what it stored and never stores it twice.</p>")
        observed = ""
        if entry["settlement"] is not None:
            found = entry["settlement"]
            if found.word == fn_client.DONE:
                finding = "The node now serves this Message-ID. The original POST response remains recorded above."
            elif found.word == fn_client.REFUSED:
                finding = ("The node did not serve this Message-ID to this reader in this lookup "
                           "(withdrawn, reclaimed, not held, or not visible here). That is not "
                           "evidence about acceptance; the original POST outcome has not changed.")
            else:
                finding = "The lookup could not establish whether the article is served."
            observed = "<p class='hint'>" + e(finding) + "</p>"
        observed += self.reconciliation_html(token, entry)
        hidden = ("<input type='hidden' name='csrf' value='" + e(self.server.token) +
                  "'><input type='hidden' name='submission_id' value='" + e(token) + "'>")
        actions = ("<form class='inline' method='post' action='/settle'>" + hidden +
                   "<button type='submit'>Check whether the node serves this "
                   "Message-ID</button></form>")
        settled = entry.get("reconciliation")
        if settled is not None and reconciled(settled):
            # The walk's fifth finding: after the node settled a re-send, the
            # headline still said "may or may not have been accepted".
            meaning = ("Settled by re-sending the same article; the first attempt's "
                       "outcome stays recorded as it was.")
            # (The final walk's leftover: the "to settle it" advice stayed.)
            said = "<p class='reason'>" + e(result.detail) + "</p>"
        local = ("<span class='badge uncertain'>local record uncertain</span> "
                 if entry.get("record_error") else "")
        self.page("Post " + word, "<nav><a href='/'>Groups</a></nav><article>"
                  "Outcome: <span class='badge " + e(word) + "'>" + e(word) + "</span> "
                  + local + "<h2>" + e(meaning) + "</h2>"
                  "<p class='meta'>Message-ID: <code>" + e(msgid) + "</code></p>" + said
                  + observed + "<p>" + actions + "</p>"
                  "<details" + (" open" if word == fn_client.UNCERTAIN else "") +
                  "><summary>The exact article sent</summary><pre>" + e(source) +
                  "</pre></details>"
                  "<details><summary>Node response and diagnostic detail</summary><pre>" +
                  e(result.detail) + "</pre></details>"
                  + ("<p class='hint'>" + e(entry.get("record_error")) +
                     ". This process is fenced from new submissions. The node answer above "
                     "was observed here, but this client could not record it locally: "
                     "that is this machine's failure, not the node refusing the post.</p>"
                     if entry.get("record_error") else "") +
                  "<p class='muted'>Refresh this page safely; it never sends another POST. "
                  + ("The durable outbox keeps the source and recorded result across restart."
                     if getattr(self.server.submissions, "durable", False) else
                     "This client keeps the exact submitted source and result only while "
                     "this process runs and the form remains in its bounded memory.") + "</p>"
                  "</article>")

    def reconciliation_html(self, token, entry) -> str:
        """The settlement of an uncertain POST, beside (never over) the original."""
        if entry["result"].word != fn_client.UNCERTAIN:
            return ""
        settled = entry.get("reconciliation")
        meaning = {
            "accepted-now": "Settled: the node accepted this article on the re-send. It is "
                            "stored once.",
            "already-stored": "Settled: the node already holds this exact article, so the "
                              "original post was accepted. Nothing was stored twice.",
            "conflict": "Settled: a different article holds this Message-ID; this text is "
                        "not stored under it.",
        }
        if settled is not None and reconciled(settled):
            key = settled.data.get("settled", "")
            return ("<div class='card'><span class='badge " + e(settled.word) + "'>" +
                    e(settled.word) + "</span> <strong>" +
                    e(meaning.get(key, settled.detail)) + "</strong><p class='meta'>" +
                    e(settled.detail) + "</p></div>")
        why = (("<p class='meta'>" + e(settled.detail) + "</p>") if settled is not None else "")
        return ("<div class='card'><span class='badge unresolved'>unresolved</span> "
                "<strong>Whether the node accepted this article is not settled.</strong>" + why +
                "<form method='post' action='/reconcile'>"
                "<input type='hidden' name='csrf' value='" + e(self.server.token) + "'>"
                "<input type='hidden' name='submission_id' value='" + e(token) + "'>"
                "<button type='submit'>Re-send this same article to settle it</button></form>"
                "<p class='muted'>This sends the exact text above under the same Message-ID. "
                "It never creates a second article.</p></div>")

    def article_html(self, group, number, one, verdict, has_verdict_lookup):
        fields = one["headers"]
        first = lambda name: fn_client.first(fields, name) or ""
        statement = bool(first("fn-statement"))
        carrier = bool(first("fn-authorship"))
        kind = verdict_kind(verdict) if has_verdict_lookup else "unavailable"
        if verdict:
            recorded = ("<span class='badge " + e(kind) + "'>" + e(kind) + "</span> "
                        "<code>" + e(verdict) + "</code> — what this node recorded when it "
                        "checked the article's authorship; a key retired later does not "
                        "change this record")
        elif has_verdict_lookup:
            recorded = ("<span class='badge unavailable'>unavailable</span> the node gave "
                        "no usable <code>HDR :fn-verified</code> line for this number")
        else:
            recorded = ("<span class='badge unavailable'>unavailable</span> "
                        "<code>HDR :fn-verified</code> needs a group and local number; this "
                        "view was reached by Message-ID")
        carried = [name for name, present in (("FN-Statement", statement),
                                              ("FN-Authorship", carrier)) if present]
        provenance = (
            "<p><span class='badge " + e(kind) + "'>node verdict: " + e(kind) +
            "</span></p><dl class='facts'>"
            "<dt>Claimed author</dt><dd>" + e(first("from") or "(no From)") +
            " <span class='muted'>— the From line is what the poster wrote; nobody "
            "has checked it</span></dd>"
            "<dt>Authorship evidence carried</dt><dd>" +
            (e(" and ".join(carried)) + " present in the article" if carried else
             "none: the article carries no FN-Statement or FN-Authorship") + "</dd>"
            "<dt>The node's historical verdict</dt><dd>" + recorded + "</dd>"
            "<dt>Current enrollment or authorization</dt><dd>not available: this node "
            "serves no query for a key's current status, so this page cannot say "
            "whether the signer is still enrolled</dd>"
            "<dt>Independent verification here</dt><dd>" +
            ("not performed: carried but not independently verified here" if carried else
             "not performed, and nothing is carried to verify") + "</dd></dl>"
            "<details><summary>Recorded handling details</summary>"
            "<p class='meta'>From (claimed): " + e(first("from")) +
            "<br>Path: " + e(first("path") or "not supplied") +
            "<br>Injection-Info: " + e(first("injection-info") or "not supplied") +
            "<br>Injection-Date: " + e(first("injection-date") or "not supplied") +
            "<br>References: " + e(first("references") or "none") +
            "</p></details><p class='muted'>Viewing does not acknowledge application "
            "processing.</p>")
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
               "</a><a href='" + e(href("/t", group=group, number=number)) +
               "'>Conversation</a><a href='" + e(href("/compose", group=group, reply=number)) +
               "'>Reply</a></nav>" if group and number else
               "<nav><a href='/'>Groups</a></nav>")
        return (nav + "<article><h2>" + e(first("subject") or "(no subject)") +
                "</h2><p class='meta'>" + e(msgid) +
                (" · local #" + e(number) if number else
                 " · local number not reported by a lookup by Message-ID") + "</p>" +
                provenance + "<pre>" + e("\n".join(one["body"])) + "</pre>" + resume +
                "</article>")

    def search_form(self, group, field="subject", pattern="") -> str:
        return ("<form method='get' action='/search'>"
                "<input type='hidden' name='group' value='" + e(group) + "'>"
                "<label>Search " + e(group) + " (a wildmat the node matches: * any text, "
                "? one character, a,b either; case-sensitive)<input name='q' maxlength='400' "
                "value='" + e(pattern) + "' placeholder='*probe*'></label>"
                "<select name='field' aria-label='field'>" +
                "".join("<option value='%s'%s>%s</option>" % (value, " selected"
                                                              if value == field else "", label)
                        for value, label in (("subject", "Subject"), ("from", "Author"))) +
                "</select><button type='submit'>Search</button></form>")

    def search_page(self, values):
        group, field = values.get("group", ""), values.get("field", "subject")
        pattern = values.get("q", "")
        if not group_token(group):
            raise ValueError("invalid group name")
        before = None
        if "before" in values:
            raw = values["before"]
            if not raw.isascii() or not raw.isdecimal() or len(raw) > 10 or int(raw) < 1:
                raise ValueError("invalid search window")
            before = int(raw)
        result = self.run_backend(lambda: self.server.backend.search(
            group, field, pattern, before))
        if result is None:
            return
        if result.word != fn_client.DONE:
            self.outcome(result.word, result.detail + (
                " (" + result.data["command"] + ")" if result.data.get("command") else ""))
            return
        data, marks = result.data, self.server.marks
        rows = "".join(
            "<article><h2" + ("" if marks.is_read(group, hit["number"]) else " class='unread'") +
            "><a href='" + e(href("/a", group=group, number=hit["number"])) + "'>" +
            e(hit["value"]) + "</a></h2><p class='meta'>local #" + e(hit["number"]) +
            "</p></article>" for hit in sorted(data["hits"], key=lambda h: -h["number"]))
        older = ("<a rel='prev' href='" + e(href("/search", group=group, field=field,
                                                  q=pattern, before=data["start"] - 1)) +
                 "'>Search older articles</a>" if data["start"] > data["low"] else "")
        self.page("Search " + group, "<nav><a href='" + e(href("/g", name=group)) + "'>" +
                  e(group) + "</a></nav>" + self.search_form(group, field, pattern) +
                  "<p class='muted'>The node answered <code>" +
                  e(data["command"] or "nothing: the window is empty") +
                  "</code> over local numbers " + e("%d–%d" % (data["start"], data["end"])) +
                  " (at most %d numbers per page). The match is the node's; this page "
                  "keeps no index.</p>" % SEARCH_SPAN +
                  (rows or "<p>No matches in this window.</p>") + "<nav>" + older + "</nav>")

    def thread_page(self, values):
        group, raw = values.get("group", ""), values.get("number", "")
        if not group_token(group) or not raw.isascii() or not raw.isdecimal() or \
                len(raw) > 10 or int(raw) < 1:
            raise ValueError("invalid article address")
        number = int(raw)
        before = None
        if "before" in values:
            limit = values["before"]
            if not limit.isascii() or not limit.isdecimal() or len(limit) > 10 or int(limit) < 1:
                raise ValueError("invalid conversation window")
            before = int(limit)
        result = self.run_backend(lambda: self.server.backend.thread(group, number, before))
        if result is None:
            return
        if result.word != fn_client.DONE:
            if answer_kind(result.detail) == "withdrawn":
                self.page("Withdrawn", "<nav><a href='" + e(href("/g", name=group)) + "'>" +
                          e(group) + "</a></nav><article><span class='badge withdrawn'>"
                          "withdrawn</span><h2>Local #" + e(number) + " was withdrawn</h2><p>" +
                          withdrawn_note(result.detail) + "</p></article>", 410)
                return
            self.outcome(result.word, result.detail + (
                " (" + result.data["command"] + ")" if result.data.get("command") else ""))
            return
        data, marks = result.data, self.server.marks
        def card(row, depth, outside):
            indent = "style='margin-left:" + str(min(depth, 8) * 18) + "px'"
            if row.get("placeholder") is not None:
                kind = answer_kind(row["placeholder"])
                label = {"withdrawn": "withdrawn", "served": "in another group"}.get(
                    kind, "not served here")
                return ("<article class='thread hole' " + indent + "><span class='badge " +
                        e(kind) + "'>" + e(label) + "</span> an earlier message, <code>" +
                        e(row["message_id"]) + "</code>; the node answered <code>" +
                        e(row["placeholder"]) + "</code>" +
                        (" · <a href='" + e(href("/find", id=row["message_id"])) +
                         "'>look it up</a>" if kind == "served" else "") + "</article>")
            return ("<article class='thread' " + indent + "><h2" +
                    ("" if marks.is_read(group, row["number"]) else " class='unread'") + ">" +
                    ("<strong>▸ </strong>" if row["number"] == number else "") +
                    "<a href='" + e(href("/a", group=group, number=row["number"])) + "'>" +
                    e(row["subject"]) + "</a></h2><p class='meta'>" +
                    e(" · ".join(x for x in (row["from"], row["date"],
                                             "local #%s" % row["number"],
                                             "its parent is not shown here" if outside else "")
                                 if x)) + "</p></article>")
        cards = "".join(card(*one) for one in thread_rows(data["rows"]))
        more = data["hits"] - data["shown"]
        older = ("<a rel='prev' href='" + e(href("/t", group=group, number=number,
                                                  before=data["start"] - 1)) +
                 "'>Look for replies in older articles</a>" if data["start"] > data["low"] else "")
        self.page("Conversation", "<nav><a href='" + e(href("/g", name=group)) + "'>" +
                  e(group) + "</a><a href='" + e(href("/a", group=group, number=number)) +
                  "'>The article</a><a href='" + e(href("/compose", group=group, reply=number)) +
                  "'>Reply</a></nav><h2>Conversation</h2>"
                  "<p class='muted'>Started by <code>" + e(data["root"]) + "</code>. "
                  "Earlier messages are the article's References, each asked of the node by "
                  "Message-ID. Replies are the node's answer to <code>" +
                  e(data["command"] or "nothing: the window is empty") + "</code> over local "
                  "numbers " + e("%d–%d" % (data["start"], data["end"])) + " of " + e(group) +
                  ": the node decides which served articles match; replies outside this "
                  "window or this group are not shown." +
                  (" The Message-ID has characters a wildmat cannot state exactly; the "
                   "pattern stands ? for each, so a near-identical Message-ID could also "
                   "match." if data["approximate"] else "") + "</p>" +
                  cards +
                  ("<p class='muted'>" + e(more) + " more matching article(s) in this window "
                   "are not shown; the newest " + e(data["shown"]) + " are.</p>" if more > 0 else "") +
                  "<nav>" + older + "</nav>")

    def marks_note(self) -> str:
        error = self.server.marks.error
        return "<p class='hint'>" + e(error) + ".</p>" if error else ""

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
        return ("<form method='post' action='/post'>"
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
                e(body) + "</textarea></label>" + save +
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
        if self.cross_site():
            self.page("Refused", "<p>Requests from another site are not served.</p>", 403)
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
            elif path == "/outbox" and getattr(self.server.submissions, "durable", False):
                # The walk's fourth finding: a list of bare Message-IDs in
                # arbitrary order does not tell a person which post is which,
                # nor which one needs attention.  Uncertain first, then drafts,
                # then settled records; each with its subject and group.
                with self.server.submissions.lock:
                    rows = [(token, entry["message_id"],
                             entry["result"].word if entry["result"] else
                             ("local write uncertain" if entry.get("record_error") else "draft"),
                             entry.get("draft"), entry.get("record_error"), entry["group"],
                             frozen_fields(entry["lines"])["subject"] if entry["lines"] else "",
                             entry.get("reconciliation"))
                            for token, entry in self.server.submissions.entries.items()
                            if entry["message_id"] or entry.get("draft") is not None]
                rank = {fn_client.UNCERTAIN: 0, "local write uncertain": 0, "draft": 1}
                rows.sort(key=lambda row: (rank.get(row[2], 2), row[6] or row[1]))
                cards = "".join(
                    ("<article><span class='badge'>draft</span> <a href='" +
                     e(href("/draft", id=token)) + "'>" + e(draft["subject"] or "(untitled)") +
                     "</a> <span class='meta'>" + e(group) + " · saved here, not posted" +
                     (" · local write uncertain" if error else "") + "</span></article>"
                     if draft is not None
                     else "<article><span class='badge " + e(word) + "'>" + e(word) +
                     "</span> <a href='" + e(href("/result", id=token)) + "'>" +
                     e(subject or "(no subject)") + "</a> <span class='meta'>" + e(group) +
                     " · <code>" + e(msgid) + "</code>" +
                     (" · settled by re-sending: " + resent.word if reconciled(resent) else
                      " · needs settling" if word == fn_client.UNCERTAIN else "") +
                     "</span></article>")
                    for token, msgid, word, draft, error, group, subject, resent in rows)
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
                    "<article class='thread' style='margin-left:" + str(min(depth, 8) * 18) +
                    "px'><h2" + ("" if marks.is_read(group, row["number"]) else
                                 " class='unread'") + ">" +
                    ("" if marks.is_read(group, row["number"]) else
                     "<span class='unread-dot' title='not opened in this client'>● </span>") +
                    "<a href='" + e(href("/a", group=group, number=row["number"])) + "'>" +
                    e(row["subject"]) + "</a> <span class='badge " +
                    e(verdict_kind(row.get("verdict"))) + "' title='" +
                    e(row.get("verdict") or "server report unavailable") + "'>" +
                    e(verdict_kind(row.get("verdict"))) + "</span></h2><p class='meta'>" +
                    e(" · ".join(x for x in (row["from"], row["date"],
                                             "local #%s" % row["number"],
                                             "reply to an article outside this window"
                                             if outside else "") if x)) +
                    (" · <a href='" + e(href("/t", group=group, number=row["number"])) +
                     "'>conversation</a>" if row.get("references") or outside else "") +
                    "</p></article>"
                    for row, depth, outside in thread_rows(rows))
                holes = result.data.get("holes") or []
                gaps = ""
                if holes:
                    gaps = ("<details class='holes'" + (" open" if len(holes) <= 8 else "") +
                              "><summary>" + e(len(holes)) + " local number(s) in this "
                              "window serve no article</summary><p class='muted'>The node's "
                              "answer to <code>STAT</code> for each, as it sent it. A "
                              "withdrawn article existed and was cancelled; a number with "
                              "no article was never assigned here or its article was "
                              "released.</p>" + "".join(
                                  "<article class='hole'><span class='badge " +
                                  e(answer_kind(hole["answer"])) + "'>" +
                                  e(answer_kind(hole["answer"])) + "</span> local #" +
                                  e(hole["number"]) + " · <code>" + e(hole["answer"]) +
                                  "</code></article>" for hole in holes) + "</details>")
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
                if high >= low and end > high:
                    frontier += (" · numbers after %s are not assigned yet; follow Newer "
                                 "later for articles that arrive" % high)
                self.page(group, "<nav><a href='/'>Groups</a><a href='" +
                          e(href("/compose", group=group)) + "'>Write a post</a></nav>"
                          "<h2>" + e(group) + "</h2><p class='muted'>" +
                          e(page_window + frontier) + " · viewing does not acknowledge processing</p>" +
                          self.search_form(group) +
                          "<p class='muted'>Threaded by References within this window. "
                          "Unread marks are this client's, not the node's.</p>" +
                          self.marks_note() +
                          "<nav aria-label='Article number windows'>" + older + " " + newer +
                          " " + mark_all + "</nav>" +
                          (cards or "<p>No articles in this number window.</p>") + gaps)
            elif path == "/search":
                self.search_page(values)
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
                    if answer_kind(result.detail) == "withdrawn":
                        self.page("Withdrawn", "<nav><a href='" + e(href(
                            "/g", name=group, start=max(1, number - MAX_RECENT // 2),
                            end=min(MAX_ARTICLE_NUMBER, number + MAX_RECENT // 2 - 1))) +
                            "'>Articles around local #" + e(number) + "</a></nav><article>"
                            "<span class='badge withdrawn'>withdrawn</span><h2>Local #" +
                            e(number) + " in " + e(group) + " was withdrawn</h2><p>" +
                            withdrawn_note(result.detail) + "</p></article>", 410)
                        return
                    self.outcome(result.word, result.detail)
                    return
                one = result.data["articles"][0]
                self.server.marks.mark(group, number, one["message_id"] or "")
                self.page(fn_client.first(one["headers"], "subject") or "Article",
                          self.article_html(group, number, one,
                                            result.data.get("fn_verified_report"), True))
            elif path == "/t":
                self.thread_page(values)
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
                # The identifier is minted once and the browser is sent to a
                # page named by it, so Back, refresh and a restored tab return
                # to the same identifier instead of minting a fresh one (the
                # walk's second finding: Back then Post posted twice).
                submission_id = self.server.submissions.new(group)
                with self.server.submissions.lock:
                    entry = self.server.submissions.entries.get(submission_id)
                    if entry is not None:
                        entry["form"] = {"subject": subject, "sender": sender,
                                         "references": references, "body": body}
                self.redirect(href("/c", id=submission_id))
            elif path == "/c":
                token = values.get("id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                with self.server.submissions.lock:
                    entry = self.server.submissions.entries.get(token)
                    posted = entry is not None and entry["result"] is not None
                    fields = dict(entry.get("form") or {}) if entry else {}
                    group = entry["group"] if entry else ""
                if entry is None:
                    self.page("Form expired", "<p>This form's identifier is no longer held "
                              "by this client (it restarted, or the form was never saved). "
                              "Nothing was sent from it after that. If you posted it, look "
                              "for it in the group or by Message-ID.</p>", 410)
                    return
                if posted:
                    self.page("Already posted", "<nav><a href='" + e(href("/g", name=group)) +
                              "'>" + e(group) + "</a></nav><article><h2>This form was "
                              "already posted</h2><p>Posting it again would send nothing: "
                              "one form sends one exact article.</p><p><a href='" +
                              e(href("/result", id=token)) + "'>See what the node answered"
                              "</a> · <a href='" + e(href("/compose", group=group)) +
                              "'>Write a new post</a></p></article>")
                    return
                form = self.compose_form(token, group, fields.get("subject", ""),
                                         fields.get("sender", ""),
                                         fields.get("references", ""), fields.get("body", ""))
                self.page("Compose", "<nav><a href='" + e(href("/g", name=group)) +
                          "'>" + e(group) + "</a></nav><h2>Write a post</h2>"
                          "<p class='muted'>One form sends one exact article. If the reply "
                          "is uncertain, keep its Message-ID and check it before trying again.</p>" + form)
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
                                            draft["references"], draft["body"]))
            elif path == "/result":
                token = values.get("id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                self.submission_result(token)
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
                    if answer_kind(result.detail) == "withdrawn":
                        self.page("Withdrawn", "<nav><a href='/'>Groups</a></nav><article>"
                                  "<span class='badge withdrawn'>withdrawn</span><h2><code>" +
                                  e(msgid) + "</code> was withdrawn</h2><p>" +
                                  withdrawn_note(result.detail) + "</p></article>", 410)
                        return
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
        if not self.valid_host() or self.path not in ("/post", "/mark", "/settle",
                                                      "/reconcile"):
            self.send_error(400)
            return
        if self.cross_site():
            self.page("Refused", "<p>Requests from another site are not served.</p>", 403)
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
            if self.path == "/reconcile":
                token = values.get("submission_id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                entry = self.server.submissions.reconcile(token)
                if entry is None:
                    self.page("Submission unavailable", "<p>No local record has this "
                              "identifier. Nothing was sent.</p>", 410)
                    return
                self.redirect(href("/result", id=token))
                return
            if self.path == "/settle":
                # A lookup records an observation beside the original answer,
                # so it is a form POST, never a GET a link or image could fire.
                token = values.get("submission_id", "")
                if not token or len(token) > 64:
                    raise ValueError("invalid submission identifier")
                if self.server.submissions.settle(token) is None:
                    self.page("Submission unavailable", "<p>No local record has this "
                              "identifier.</p>", 410)
                    return
                self.redirect(href("/result", id=token))
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
                    submission_id, group, subject, sender, references, body)
            if entry is None:
                self.page("Submission unavailable", "<p>This form's local record "
                          "expired or the web client restarted. No POST was sent.</p>", 410)
                return
            self.redirect(href("/draft" if action == "save"
                               else "/result", id=submission_id))
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
    backend = Backend(args, user, password, args.sender)
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
