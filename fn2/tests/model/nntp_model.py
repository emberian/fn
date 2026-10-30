"""Spec-derived NNTP oracle, independent of the implementation.

Call check(), then update() for each response in wire order. send() may queue
commands: an expectation resolves against the state left by earlier updates.
body is the *wire* dot-stuffed block, including its terminator, or None.
For the third authentication failure status_line contains BOTH 481/400 lines.
After 382, call tls_established() only on successful transport completion.

Fixture configuration and explicit environment seams are documented in SPEC-MAP.
No clock, cryptography, disk, socket, or randomness is consulted by this model.
"""
from __future__ import annotations

import base64
import binascii
import copy
import fnmatch
from dataclasses import dataclass
from datetime import datetime, timezone
import ipaddress
import re
from typing import Callable

from . import framing


@dataclass(frozen=True)
class Verdict:
    ok: bool
    rule: str
    spec: str
    detail: str


class Expect:
    """A predicate plus a validated, idempotent commit, not a generated reply."""

    def __init__(self, codes=(), *, rule="", spec="", pattern=None, content=None,
                 multiline=False, effect=None, tail=(), resolver=None,
                 close_after_reply=False, close_without_reply=False,
                 close_effect=None, close_spec=""):
        self.codes = frozenset(codes)
        self.rule, self.spec = rule, spec
        self.pattern, self.content = pattern, content
        self._multiline, self.effect, self.tail = multiline, effect, tail
        self._resolver, self._resolved, self._updated = resolver, None, False
        self._committed_response = None
        self._close_after_reply, self._close_without_reply = close_after_reply, close_without_reply
        self._close_effect, self._close_spec, self._eof_observed = close_effect, close_spec, False

    @property
    def close_after_reply(self):
        return self._get()._close_after_reply

    @property
    def close_without_reply(self):
        return self._get()._close_without_reply

    @property
    def close_spec(self):
        return self._get()._close_spec

    def observe_eof(self):
        """Commit a permitted, observed transport close after a checked reply."""
        obj = self._get()
        if obj is not self:
            return obj.observe_eof()
        if not self._updated or not (self._close_after_reply if self._committed_response[0]
                                     else self._close_without_reply):
            raise ValueError("EOF is not permitted for this committed response")
        if not self._eof_observed and self._close_effect:
            self._close_effect()
        self._eof_observed = True

    def _get(self):
        if self._resolver is not None:
            if self._resolved is None:
                self._resolved = self._resolver()
            return self._resolved
        return self

    @property
    def multiline(self) -> bool:
        return bool(self._get()._multiline)

    def multiline_for(self, status_line: bytes) -> bool:
        """Resolve conditional extension framing after reading the status code."""
        multi = self._get()._multiline
        return int(status_line[:3]) in multi if isinstance(multi, frozenset) else bool(multi)

    @classmethod
    def none(cls, rule="closed", spec="specs/nntp.md:521-528; RFC 3977 §5.4"):
        return cls(rule=rule, spec=spec, close_without_reply=rule == "closed", close_spec=spec)

    def check(self, status_line: bytes, body: bytes | None, *, eof=False) -> Verdict:
        obj = self._get()
        if obj is not self:
            return obj.check(status_line, body, eof=eof)
        def verdict(ok, detail):
            return Verdict(ok, self.rule, self.spec, detail)
        if eof:
            if not status_line and body is None and self._close_without_reply:
                return Verdict(True, self.rule, self._close_spec, "match: permitted EOF")
            if not self._close_after_reply:
                return verdict(False, "connection closed where a reply or continued session was required")
        if not self.codes:
            return verdict(status_line == b"" and body is None,
                           "match" if status_line == b"" and body is None else
                           "expected no reply and no framing")
        try:
            rows = framing.lines(status_line)
            if len(rows) != 1 + len(self.tail):
                return verdict(False, "wrong number of status lines (including closing 400)")
            for row in rows:
                if len(row) + 2 > 512 or not re.fullmatch(rb"[1-5][0-9]{2}(?: [^\r\n]*)?", row):
                    return verdict(False, "invalid status-line grammar or length")
            code = int(rows[0][:3])
            if code not in self.codes:
                return verdict(False, f"code {code}; permitted {sorted(self.codes)}")
            if tuple(int(r[:3]) for r in rows[1:]) != self.tail:
                return verdict(False, f"expected trailing status codes {self.tail}")
            if self.pattern and not re.fullmatch(self.pattern, rows[0]):
                return verdict(False, "status arguments/text do not match the rule")
            multi = self._multiline
            if isinstance(multi, frozenset):
                multi = code in multi
            if multi:
                if body is None:
                    return verdict(False, "missing multi-line block")
                decoded = framing.decode_block(body)
                if self.content is not None:
                    error = self.content(decoded) if callable(self.content) else (
                        None if decoded == self.content else "content differs from model")
                    if error:
                        return verdict(False, error)
            elif body is not None:
                return verdict(False, "unexpected multi-line block")
        except (ValueError, TypeError) as exc:
            return verdict(False, f"framing: {exc}")
        return verdict(True, "match")

    def update(self, status_line: bytes, body: bytes | None, *, eof=False) -> None:
        obj = self._get()
        if obj is not self:
            obj.update(status_line, body, eof=eof)
            return
        result = self.check(status_line, body, eof=eof)
        if not result.ok:
            raise ValueError(f"{result.rule} ({result.spec}): {result.detail}")
        if self._updated:
            if self._committed_response != (status_line, body):
                raise ValueError("expectation already committed to a different response")
            if eof:
                self.observe_eof()
            return
        if self.effect:
            self.effect(int(status_line[:3]) if status_line else None, status_line, body)
        self._updated = True
        self._committed_response = (status_line, body)
        if eof:
            self.observe_eof()


SPECS = {
    "syntax": "RFC 3977 §§3.1, 3.2.1; specs/nntp.md:512-519",
    "unknown": "specs/nntp.md:51-93; RFC 3977 §3.2.1",
    "greeting": "specs/nntp.md:9-23,1985-2010; RFC 3977 §5.1",
    "CAPABILITIES": "specs/nntp.md:3-23,1698-1736,2480-2507; RFC 3977 §5.2",
    "HELP": "specs/nntp.md:51-93; RFC 3977 §7.2",
    "QUIT": "specs/nntp.md:521-528; RFC 3977 §5.4",
    "MODE": "specs/nntp.md:14-24,2412-2443; RFC 3977 §5.3",
    "DATE": "specs/nntp.md:106-134; RFC 3977 §7.1",
    "GROUP": "specs/nntp.md:419-505; RFC 3977 §6.1.1",
    "LISTGROUP": "specs/nntp.md:419-505; RFC 3977 §6.1.2",
    "NEXT": "specs/nntp.md:419-505; RFC 3977 §6.1.4",
    "LAST": "specs/nntp.md:419-505; RFC 3977 §6.1.3",
    "ARTICLE": "specs/nntp.md:330-362,400-424,979-988; RFC 3977 §6.2.1",
    "HEAD": "specs/nntp.md:400-424; RFC 3977 §6.2.2",
    "BODY": "specs/nntp.md:400-424; RFC 3977 §6.2.3",
    "STAT": "specs/nntp.md:419-424; RFC 3977 §6.2.4",
    "OVER": "specs/nntp.md:319-362; RFC 3977 §8.3",
    "XOVER": "specs/nntp.md:136-159; RFC 2980 §2.8",
    "HDR": "specs/nntp.md:400-416,2771-2806; RFC 3977 §8.5",
    "XHDR": "specs/nntp.md:136-159,400-416; RFC 2980 §2.6",
    "XPAT": "specs/nntp.md:161-180,415-416; RFC 2980 §2.9",
    "LIST": "specs/nntp.md:182-235,364-416,1061-1118; RFC 3977 §7.6; RFC 6048 §2",
    "NEWGROUPS": "specs/nntp.md:106-134,375-389; RFC 3977 §7.3",
    "NEWNEWS": "specs/nntp.md:237-317; RFC 3977 §7.4",
    "POST": "specs/nntp.md:709-1480,1985-2010; RFC 3977 §6.3.1",
    "IHAVE": "specs/nntp.md:530-537,2412-2443; RFC 3977 §6.3.2",
    "CHECK": "specs/nntp.md:2412-2443; RFC 4644 §2.4",
    "TAKETHIS": "specs/nntp.md:530-537,2412-2443; RFC 4644 §2.5",
    "AUTHINFO": "specs/nntp.md:1482-1736; RFC 4643 §§2.3,2.4",
    "STARTTLS": "specs/nntp.md:1482-1509,1620-1696; RFC 4642 §2.2",
    "COMPRESS": "specs/nntp.md:2480-2536; RFC 8054 §2.2",
    "XREDEEM": "specs/nntp.md:1784-1914",
    "XFNCATCHUP": "specs/nntp.md:676; RELEASE-PLAN §1 NNTP: fn's own commands",
    "XFN-ZARTICLE": "specs/nntp.md:2484-2499",
    "capacity": "specs/nntp.md:2301-2384; RFC 3977 §5.1.1",
}
HELP = (b"CAPABILITIES HELP QUIT MODE DATE POST\r\n"
        b"AUTHINFO STARTTLS XREDEEM COMPRESS\r\n"
        b"GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS\r\n"
        b"ARTICLE HEAD BODY STAT\r\nOVER XOVER HDR XHDR XPAT\r\n"
        b"IHAVE CHECK TAKETHIS\r\n")
KEYWORDS = set(HELP.decode().split()) | {"XFNCATCHUP", "XFN-ZARTICLE"}
MSGID = re.compile(r"<[\x21-\x3d\x3f-\x7e]{1,248}>\Z", re.ASCII)


def msgid(value):
    return len(value.encode()) <= 250 and bool(MSGID.fullmatch(value))


def stored_msgid(value):
    atom = r"[A-Za-z0-9!#$%&'*+\-/=?^_`{|}~]+"
    dot_atom = atom + r"(?:\." + atom + r")*"
    literal = r"\[[\x21-\x3d\x3f-\x5a\x5e-\x7e]*\]"
    return len(value.encode()) <= 250 and bool(re.fullmatch(
        "<" + dot_atom + "@(?:" + dot_atom + "|" + literal + ")>", value))


def wildmat(pattern: str, value: str) -> bool:
    """RFC 3977 §4.2: the RIGHTMOST matching alternative wins."""
    result = False
    for i, part in enumerate(pattern.split(",")):
        negative = part.startswith("!")
        token = part[1:] if negative else part
        if not token or (negative and i == 0) or any(c in "![]\\" or ord(c) < 32 for c in token):
            raise ValueError("invalid wildmat")
        if fnmatch.fnmatchcase(value, token):
            result = not negative
    return result


def headers(article: bytes) -> dict[str, bytes]:
    """First field wins; retain folds until the RFC NOV transformation."""
    block = article.partition(b"\r\n\r\n")[0]
    fields, key, value = {}, None, b""
    for row in block.split(b"\r\n") + [b""]:
        if row.startswith((b" ", b"\t")) and key is not None:
            value += b"\r\n" + row
            continue
        if key is not None:
            fields.setdefault(key, value[1:] if value.startswith(b" ") else value)
        key, value = None, b""
        if b":" in row:
            name, value = row.split(b":", 1)
            key = name.decode("ascii", "replace").lower()
    return fields


def scrub(value: bytes) -> bytes:
    return re.sub(rb"[\t\0\r\n]", b" ", value.replace(b"\r\n", b""))


def body_lines(article: bytes) -> int:
    body = article.partition(b"\r\n\r\n")[2]
    try:
        return len(framing.lines(body))
    except framing.FramingError:
        return 0


def number_range(token: str, high: int) -> tuple[int, int]:
    if not re.fullmatch(r"[0-9]{1,16}(?:-[0-9]{0,16})?", token):
        raise ValueError("invalid range")
    low, dash, end = token.partition("-")
    lo, hi = int(low), (int(end) if end else high) if dash else int(low)
    if not 1 <= lo <= 2147483647 or (end and not 1 <= hi <= 2147483647):
        raise ValueError("article number outside RFC 3977 §6 range")
    return lo, hi


def packed(rows) -> bytes:
    return b"".join((r.encode() if isinstance(r, str) else r) + b"\r\n" for r in rows)


def decimal_pattern(number):
    digits = str(number).encode()
    return b"0{0," + str(max(0, 16 - len(digits))).encode() + b"}" + digits


def row_set(expected):
    expected = list(expected)
    def check(data):
        actual = framing.lines(data)
        return None if sorted(actual) == sorted(expected) else "listing rows differ (including multiplicity)"
    return check


class NntpModel:
    def __init__(self, groups: dict[str, dict], articles: list[tuple[str, bytes, list[str]]],
                 accounts: dict, policy: dict, *, limits=None):
        self.flags = copy.deepcopy(groups)
        self.groups = {g: list(f.get("entries", [])) for g, f in groups.items()}
        self.watermarks = {g: max([f.get("watermark", 0)] + [n for n, _ in self.groups[g]])
                           for g, f in groups.items()}
        self.issued = {g: [n for n, _ in self.groups[g]] for g in groups}
        for g, entries in self.groups.items():
            if any(n <= 0 for n, _ in entries) or len(set(self.issued[g])) != len(entries):
                raise ValueError("initial numbers must be positive and unique")
            if len({m for _, m in entries}) != len(entries):
                raise ValueError("one number per article per group")
            if any(a >= b for a, b in zip(self.issued[g], self.issued[g][1:])):
                raise ValueError("initial entries must be in issue order")
        self.articles, self.sources, self.withdrawn = {}, {}, set()
        self.accounts, self.policy = copy.deepcopy(accounts), copy.deepcopy(policy)
        # HW, specs/nntp.md:2307-2337,2352-2376: exposure reads LIVE policy,
        # unlike a connection's pinned authentication/reader configuration.
        self.limits = limits
        # HW observes a single short fresh-owner window, with one login per
        # principal. Rollover and shared-principal aliases are outside its scope.
        self.address_failures, self.principal_posts = {}, {}
        self.connections, self.version = [], 0
        self.stamps = dict(policy.get("stamps", {}))
        self.redemptions = {}
        self.post_outcomes = []
        for ident, data, names in articles:
            self.add_article(ident, data, names)

    def add_article(self, ident: str, data: bytes, groups: list[str], *, stamp=None):
        """Environment input: a completed durable acceptance, never a tentative POST."""
        if not stored_msgid(ident):
            raise ValueError("invalid Message-ID")
        if ident in self.articles:
            if self.articles[ident] != data:
                raise ValueError("conflicting identity")
            return
        if any(g not in self.groups for g in groups):
            raise ValueError("unconfigured group")
        self.articles[ident] = data
        self.sources[ident] = data
        for group in dict.fromkeys(groups):
            if any(m == ident for _, m in self.groups[group]):
                continue
            self.watermarks[group] += 1
            n = self.watermarks[group]
            self.groups[group].append((n, ident))
            self.issued[group].append(n)
        self.stamps.setdefault(ident, stamp)
        self.version += 1

    def withdraw(self, ident: str):
        """Publish withdrawal; older pins remain visible until a refresh boundary."""
        if ident not in self.articles:
            raise ValueError("unknown identity")
        self.withdrawn.add(ident)
        self.version += 1

    def retire_group(self, name: str):
        self.flags[name]["retired"] = True
        self.version += 1

    def connect(self, *, tls: bool, implicit_tls: bool, address: str = "127.0.0.1") -> Conn:
        conn = Conn(self, tls=tls or implicit_tls, implicit_tls=implicit_tls, address=address)
        live = [c for c in self.connections if not c.quit]
        public = self.limits.public if self.limits is not None else not ipaddress.ip_address(address).is_loopback
        trusted = any(ipaddress.ip_address(address) in ipaddress.ip_network(n, strict=False)
                      for n in self.policy.get("trusted", []))
        total = self.limits.get('exposure-connections') if self.limits is not None else self.policy.get("connections", 31)
        per_address = self.limits.get('exposure-per-address') if self.limits is not None else self.policy.get("per_address", 8 if public else total)
        if self.limits is not None:
            trusted = self.limits.trusted(address)
        if len(live) >= total:
            conn.refused = "too many connections"
        elif not trusted and sum(c.address == address for c in live) >= per_address:
            conn.refused = "too many connections from this address"
        elif self.limits is not None and self.limits.get('exposure-auth-failures') and self.address_failures.get(address, 0) >= self.limits.get('exposure-auth-failures'):
            # specs/nntp.md:2320: next accept after the address budget is spent.
            conn.refused = "too many authentication failures from this address"
        self.connections.append(conn)
        return conn


class Conn:
    def __init__(self, model, *, tls, implicit_tls, address):
        self.model, self.tls, self.implicit_tls, self.address = model, tls, implicit_tls, address
        self.authenticated_as, self.current_group, self.current_article_number = None, None, None
        self.compressed = self.quit = self.mode_reader_seen = self.streaming = False
        self.failed_auth_count, self.handshaking = 0, False
        self.username, self.sasl, self.sasl_identity, self.redeem = None, None, None, None
        self.pending, self.refused, self.inflight = None, None, []
        self._issued_expectations, self._committed_expectations = 0, 0
        self.credentials = copy.deepcopy(model.accounts)
        self.policy = copy.deepcopy(model.policy)
        if model.limits is not None:
            # HW, specs/nntp.md:2322-2336: the new session reads the current
            # anonymous policy; explicit auth.required still cannot be weakened.
            self.policy['anonymous'] = model.limits.get('anonymous')
        self.peer = self.policy.get("peer", False) or address in self.policy.get("peers", [])
        self._pin()

    def _snapshot(self):
        return (self.model.version, copy.deepcopy(self.model.groups), dict(self.model.articles),
                set(self.model.withdrawn), dict(self.model.watermarks),
                copy.deepcopy(self.model.flags), dict(self.model.stamps))

    def _pin(self, snapshot=None):
        (self.pinned_version, self.view_groups, self.view_articles, self.view_withdrawn,
         self.view_watermarks, self.view_flags, self.view_stamps) = snapshot or self._snapshot()

    def _account(self):
        account = self.credentials.get(self.authenticated_as, {})
        return {"password": account} if isinstance(account, str) else account

    def _access(self, group, kind="read"):
        account = self._account() if self.authenticated_as else self.policy.get("anonymous_access", {})
        patterns = account.get(kind, account.get(kind + "_wildmats", "*"))
        if isinstance(patterns, list):
            patterns = ",".join(patterns)
        try:
            return wildmat(patterns, group)
        except ValueError:
            return False

    def _visible(self, group, live=False):
        flags = self.model.flags if live else self.view_flags
        if group not in flags or flags[group].get("retired") or not self._access(group):
            return False
        owners = [f for f in flags.values() if f.get("queue") == group]
        return not owners or any(self.authenticated_as in f.get("moderators", []) for f in owners)

    def _available(self, group, live=False):
        groups = self.model.groups if live else self.view_groups
        articles = self.model.articles if live else self.view_articles
        withdrawn = self.model.withdrawn if live else self.view_withdrawn
        return sorted((n, m) for n, m in groups.get(group, [])
                      if m in articles and m not in withdrawn) if self._visible(group, live) else []

    def _summary(self, group, live=False):
        rows = self._available(group, live)
        wm = (self.model.watermarks if live else self.view_watermarks)[group]
        return (len(rows), rows[0][0], rows[-1][0]) if rows else (0, wm + 1, wm)

    def _requires_auth(self):
        public = not ipaddress.ip_address(self.address).is_loopback
        return self.policy.get("required", False) or self.policy.get("anonymous", "none" if public else "open") == "none"

    def _posting(self):
        return self.policy.get("posting", True) and (
            self._account().get("posting", True) if self.authenticated_as else not self._requires_auth())

    def _reply(self, rule, codes, **kwargs):
        return Expect((codes,) if isinstance(codes, int) else codes,
                      rule=rule, spec=SPECS[rule], **kwargs)

    def _error(self, code=501):
        return self._reply("syntax", code)

    def _malformed(self, *, overlong=False):
        # Structural rejection may drain to a boundary or close. This is not
        # permission to silently close on an ordinary argument/count error.
        # RFC 3977 section 3.2.1 expressly requires 501 for overlength.
        return self._reply("syntax", 501, close_after_reply=True, close_without_reply=not overlong,
                           close_effect=lambda: setattr(self, "quit", True),
                           close_spec="specs/nntp.md:513-518; RFC 3977 §§3.1,12.5")

    def _queue(self, action):
        ticket = self._issued_expectations
        self._issued_expectations += 1
        def resolve():
            if ticket != self._committed_expectations:
                raise RuntimeError("check/update earlier replies before resolving this pipelined reply")
            result = action()
            effect = result.effect
            def commit(code, status, body):
                if effect:
                    effect(code, status, body)
                self._committed_expectations += 1
            result.effect = commit
            return result
        return Expect(resolver=resolve)

    def greeting(self) -> Expect:
        if self.refused:
            pattern = rb"400 " + re.escape(self.refused.encode()) + rb".*"
            if self.model.limits is not None:
                # HW exact public lines, specs/nntp.md:2315-2320,2358-2362.
                # A total-capacity prefix must not also accept an address refusal.
                suffix = '; try again later' if self.refused in (
                    'too many connections', 'too many connections from this address') else ''
                pattern = re.escape(('400 ' + self.refused + suffix).encode())
            return self._reply("capacity", 400, pattern=pattern,
                               effect=lambda *_: setattr(self, "quit", True),
                               close_after_reply=True, close_spec=SPECS["capacity"])
        return self._reply("greeting", 200 if self._posting() else 201)

    def send(self, line: bytes) -> Expect:
        return self._queue(lambda: self._dispatch(line))

    def _dispatch(self, line):
        if self.quit or self.handshaking:
            return Expect.none()
        if self.pending:
            raise ValueError("article body owed: use send_block, not send")
        if self.sasl:
            return self._sasl_response(line)
        try:
            raw = framing.command_line(line)
            # Streaming has no command reply: consume the article even when
            # the offered identifier is malformed (RFC 4644 section 2.5.2).
            # Preserve raw token octets, including invalid UTF-8, for echo checks.
            streaming = re.split(rb"[ \t]+", raw)
            if self.peer and streaming[0].upper() == b"TAKETHIS":
                offered = streaming[1] if len(streaming) > 1 else b"-"
                try:
                    valid = len(streaming) == 2 and msgid(offered.decode("utf-8"))
                except UnicodeError:
                    valid = False
                if not valid:
                    result = Expect.none("TAKETHIS", SPECS["TAKETHIS"])
                    result.malformed_takethis = True  # Optional bounded diagnostic.
                    result.effect = lambda *_: setattr(self, "pending", ("TAKETHIS", offered))
                    return result
            # H6 pin (specs/nntp.md:513-518, adjudicated with layer D): the line must decode
            # before its words exist, so invalid UTF-8 is malformed (501, close) even when the
            # line also has surrounding whitespace; whitespace alone is a plain 501.
            text = raw.decode("utf-8")
            if raw[:1] in b" \t" or raw[-1:] in b" \t":
                return self._error()
            words = re.split(r"[ \t]+", text)
            command, args = words[0].upper(), words[1:]
            if any(ord(c) < 32 or ord(c) == 127 for w in words for c in w):
                return self._error()
            if args and len(re.split(rb"[ \t]+", raw, maxsplit=1)[1]) > 497:
                return self._error()
        except (ValueError, UnicodeError):
            return self._malformed(overlong=len(line) > 512)
        if command not in KEYWORDS:
            return self._reply("unknown", 500)
        public = {"CAPABILITIES", "HELP", "QUIT", "MODE", "AUTHINFO", "STARTTLS", "COMPRESS", "XREDEEM",
                  "IHAVE", "CHECK", "TAKETHIS"}
        if self.peer:
            public |= {"IHAVE", "CHECK", "TAKETHIS", "XFNCATCHUP", "XFN-ZARTICLE"}
        if self._requires_auth() and not self.authenticated_as and command not in public:
            return self._reply(command, 480)
        try:
            return getattr(self, "_cmd_" + command.lower().replace("-", "_"))(args)
        except (ValueError, UnicodeError):
            return self._error()

    def exposure_wait(self, kind, *, steps=0):
        """HW short observation within one window; no pending command consumed.

        specs/nntp.md:2317,2321: no reply while paced. The workload supplies
        observed host-read steps; TCP writes are NOT equated to host reads.
        A caller checks EOF separately: waiting must retain the connection.
        """
        if self.model.limits is None:
            raise ValueError('live limits required')
        if kind == 'posts':
            count = self.model.principal_posts.get(self.authenticated_as, 0)
            limit = self.model.limits.get('exposure-posts-per-minute')
        elif kind == 'steps':
            count, limit = steps, self.model.limits.get('exposure-steps-per-second')
        else:
            raise ValueError('unknown exposure wait')
        if not limit or count < limit:
            raise ValueError('pacing antecedent not established')
        return Expect.none('exposure-wait', 'specs/nntp.md:2317,2321')

    def exposure_deadline(self, *, elapsed, first):
        """HW, specs/nntp.md:2318-2326: no progress, then silent close.

        elapsed is the externally observed interval since greeting/last reply;
        the model never sleeps or reads a clock. Zero disables this deadline.
        """
        key = 'exposure-first-seconds' if first else 'exposure-idle-seconds'
        limit = self.model.limits.get(key) if self.model.limits is not None else 0
        if not limit or elapsed < limit:
            raise ValueError('deadline antecedent not established')
        return Expect(rule='exposure-deadline', spec='specs/nntp.md:2318-2326',
                      close_without_reply=True, close_spec='specs/nntp.md:2318-2326',
                      close_effect=lambda: setattr(self, 'quit', True))

    def _cmd_quit(self, args):
        return self._error() if args else self._reply("QUIT", 205, effect=lambda *_: setattr(self, "quit", True),
                                                     close_after_reply=True, close_spec=SPECS["QUIT"])

    def _cmd_help(self, args):
        if args:
            return self._error()
        # Extension headings are inconsistent with the old six-line table: see A1.
        def content(data):
            words = data.decode("ascii").split()
            return None if set(words) in (set(HELP.decode().split()), KEYWORDS) and len(words) == len(set(words)) else "HELP keyword set differs"
        return self._reply("HELP", 100, multiline=True, content=content)

    def _sasl_offers(self):
        """Required and observationally optional offers (spec1705-1709)."""
        if "sasl_mechanisms" in self.policy:
            return set(self.policy["sasl_mechanisms"]), set()
        required = {"SCRAM-SHA-256"} | ({"PLAIN"} if self.tls else set())
        optional = set()
        plus_available = self.tls and self.policy.get("tls_version") in (None, "TLSv1.3")
        if plus_available:
            exporter = self.policy.get("tls_exporter", False)
            if exporter is True:
                required.add("SCRAM-SHA-256-PLUS")
            elif exporter is None:
                optional.add("SCRAM-SHA-256-PLUS")
        return required, optional

    def _cmd_capabilities(self, args):
        if len(args) > 1 or (args and not re.fullmatch(r"[A-Za-z][A-Za-z0-9.-]{2,}", args[0])):
            return self._error()
        required = {b"VERSION 2", b"READER", b"OVER MSGID", b"HDR", b"XPAT", b"NEWNEWS"}
        if self._posting():
            required.add(b"POST")
        if self.peer:
            required |= {b"IHAVE", b"STREAMING"}
        if not (self.tls or self.authenticated_as or self.compressed) and self.policy.get("starttls", True):
            required.add(b"STARTTLS")
        if not self.compressed and self.authenticated_as:
            # NNT-054 (specs/nntp.md:2482): compression after authentication; before
            # it RFC 8054 §2.1 still permits the label, fn1 omits it: either is admitted.
            required.add(b"COMPRESS DEFLATE")
        def content(data):
            rows = framing.lines(data)
            labels = [r.split(b" ", 1)[0].upper() for r in rows]
            if not rows or rows[0] != b"VERSION 2" or len(labels) != len(set(labels)) or not required <= set(rows):
                return "missing or duplicate capability"
            for label, allowed in ((b"POST", self._posting()), (b"STARTTLS", b"STARTTLS" in required),
                                   (b"COMPRESS", not self.compressed), (b"IHAVE", self.peer),
                                   (b"STREAMING", self.peer), (b"AUTHINFO", not (self.authenticated_as or self.compressed))):
                if not allowed and label in labels:
                    return f"forbidden capability {label!r}"
            if b"MODE-READER" in labels or b"XOVER" in labels or b"XHDR" in labels:
                return "unadvertised legacy/mode capability"
            listing = next((r.split()[1:] for r in rows if r.startswith(b"LIST ")), [])
            if not set(b"ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT".split()) <= set(listing):
                return "missing LIST variant"
            if not any(r.startswith(b"IMPLEMENTATION ") for r in rows):
                return "missing IMPLEMENTATION"
            mechanisms = next((r.split()[1:] for r in rows if r.startswith(b"SASL ")), [])
            if (b"DIGEST-MD5" in mechanisms or (not self.tls and b"PLAIN" in mechanisms)
                    or (b"SCRAM-SHA-256-PLUS" in mechanisms and
                        (not self.tls or self.policy.get("tls_version") not in (None, "TLSv1.3")))):
                return "SASL mechanism unavailable on this connection"
            required_mechs, optional_mechs = self._sasl_offers()
            offered = {m.encode() for m in required_mechs}
            optional = {m.encode() for m in optional_mechs}
            if not offered <= set(mechanisms) <= offered | optional or len(mechanisms) != len(set(mechanisms)):
                return "SASL mechanism list differs from configured connection context"
            if not (self.authenticated_as or self.compressed):
                auth = next((r.split()[1:] for r in rows if r.startswith(b"AUTHINFO ")), [])
                wanted = {b"SASL"} | ({b"USER"} if self.tls or not self.policy.get("protected_only") else set())
                if set(auth) != wanted:
                    return "AUTHINFO mechanisms differ from current policy"
            return None
        return self._reply("CAPABILITIES", 101, multiline=True, content=content)

    def _cmd_mode(self, args):
        if len(args) != 1:
            return self._error()
        if args[0].upper() == "READER":
            return self._reply("MODE", 200 if self._posting() else 201,
                               effect=lambda *_: setattr(self, "mode_reader_seen", True))
        if args[0].upper() == "STREAM":
            return self._reply("MODE", 203 if self.peer else 501,
                               effect=lambda code, *_: setattr(self, "streaming", code == 203))
        return self._error()

    def _cmd_date(self, args):
        if args:
            return self._error()
        clock = self.model.policy.get("clock", "unknown")
        if clock is None:
            return self._reply("DATE", 503)
        pattern = rb"(?:111 [0-9]{14}(?: .*)?|503(?: .*)?)" if clock == "unknown" else rb"111 " + str(clock).encode() + rb"(?: .*)?"
        return self._reply("DATE", {111, 503} if clock == "unknown" else 111, pattern=pattern)

    def _select_group(self, args, listing):
        rule = "LISTGROUP" if listing else "GROUP"
        if len(args) > (2 if listing else 1) or (not listing and not args):
            return self._error()
        group = args[0] if args else self.current_group
        if group is None:
            return self._reply(rule, 412)
        bounds = number_range(args[1], self.model.watermarks.get(group, 0)) if len(args) == 2 else None
        if not self._visible(group, live=True):
            return self._reply(rule, 411)
        rows = self._available(group, live=True)
        count, low, high = self._summary(group, live=True)
        prefix = b"211 " + b" ".join(decimal_pattern(n) for n in (count, low, high)) + b" " + re.escape(group.encode())
        selected = rows if bounds is None else [(n, m) for n, m in rows if bounds[0] <= n <= bounds[1]]
        snapshot = self._snapshot()
        def effect(*_):
            self._pin(snapshot)
            self.current_group = group
            self.current_article_number = rows[0][0] if rows else None
        def content(data):
            actual = framing.lines(data)
            if any(not re.fullmatch(rb"[0-9]{1,16}", row) for row in actual):
                return "invalid LISTGROUP number"
            return None if [int(row) for row in actual] == [n for n, _ in selected] else "LISTGROUP numbers differ"
        return self._reply(rule, 211, pattern=prefix + rb"(?: .*)?",
                           multiline=listing, content=content if listing else None,
                           effect=effect)

    def _cmd_group(self, args):
        return self._select_group(args, False)

    def _cmd_listgroup(self, args):
        return self._select_group(args, True)

    def _move(self, args, forward):
        rule = "NEXT" if forward else "LAST"
        if args:
            return self._error()
        if not self.current_group:
            return self._reply(rule, 412)
        rows = self._available(self.current_group)
        if self.current_article_number not in dict(rows):
            return self._reply(rule, 420)
        candidates = [(n, m) for n, m in rows if (n > self.current_article_number if forward else n < self.current_article_number)]
        if not candidates:
            return self._reply(rule, 421 if forward else 422)
        n, ident = candidates[0] if forward else candidates[-1]
        return self._reply(rule, 223, pattern=b"223 " + decimal_pattern(n) + b" " + re.escape(ident.encode()) + rb"(?: .*)?",
                           effect=lambda *_: setattr(self, "current_article_number", n))

    def _cmd_next(self, args):
        return self._move(args, True)

    def _cmd_last(self, args):
        return self._move(args, False)

    def _lookup(self, args, rule, ranges=False):
        if len(args) > 1:
            return self._error()
        if args and args[0].startswith("<"):
            ident = args[0]
            if not msgid(ident) or rule == "XOVER":
                return self._error()
            readable = any(self._visible(g) and any(m == ident for _, m in entries)
                           for g, entries in self.view_groups.items())
            if not readable or ident not in self.view_articles:
                return self._reply(rule, 430)
            if ident in self.view_withdrawn:
                return self._reply(rule, 430, pattern=rb"430 withdrawn(?: .*)?")
            n = next((n for n, m in self._available(self.current_group) if m == ident), 0)
            return [(n, ident)]
        bounds = number_range(args[0], self.view_watermarks.get(self.current_group, 0)) if args else None
        if args and not ranges and "-" in args[0]:
            return self._error()
        if not self.current_group:
            return self._reply(rule, 412)
        if not args and self.current_article_number is None:
            return self._reply(rule, 420)
        lo, hi = bounds or (self.current_article_number, self.current_article_number)
        rows = [(n, m) for n, m in self._available(self.current_group) if lo <= n <= hi]
        if not rows:
            if rule == "XPAT":
                return []
            code = (420 if rule in {"XOVER", "XHDR"} else 423) if args else 420
            return self._reply(rule, code)
        return rows

    def _xref(self, ident):
        server = self.policy.get("server", ".invalid")
        pairs = [f"{g}:{n}" for g in self.view_groups if self._visible(g)
                 for n, m in self.view_groups[g] if m == ident]
        return (str(server) + " " + " ".join(pairs)).encode() if server and pairs else b""

    def _retrieve(self, args, rule):
        selected = self._lookup(args, rule)
        if isinstance(selected, Expect):
            return selected
        n, ident = selected[0]
        code = {"ARTICLE": 220, "HEAD": 221, "BODY": 222, "STAT": 223}[rule]
        by_id = bool(args and args[0].startswith("<"))
        nums = b"(?:0{1,16}|" + decimal_pattern(n) + b")" if by_id else decimal_pattern(n)
        pattern = str(code).encode() + b" " + nums + b" " + re.escape(ident.encode()) + rb"(?: .*)?"
        data = self.view_articles[ident]
        head, sep, body = data.partition(b"\r\n\r\n")
        if rule != "STAT":
            try:
                framing.lines(data)
                if not sep:
                    raise ValueError("no header separator")
            except ValueError:
                return self._reply(rule, 503)
        xref = self._xref(ident)
        prefix = b"Xref: " + xref + b"\r\n" if xref else b""
        content = {"ARTICLE": prefix + data, "HEAD": prefix + head + b"\r\n", "BODY": body, "STAT": None}[rule]
        def effect(*_):
            if not by_id:
                self.current_article_number = n
        return self._reply(rule, code, pattern=pattern, multiline=rule != "STAT", content=content, effect=effect)

    def _cmd_article(self, args):
        return self._retrieve(args, "ARTICLE")

    def _cmd_head(self, args):
        return self._retrieve(args, "HEAD")

    def _cmd_body(self, args):
        return self._retrieve(args, "BODY")

    def _cmd_stat(self, args):
        return self._retrieve(args, "STAT")

    def _nov(self, n, ident):
        data = self.view_articles[ident]
        fields = headers(data)
        result = [str(n).encode()] + [scrub(fields.get(f, b"")) for f in
                   ("subject", "from", "date", "message-id", "references")]
        result += [str(len(data)).encode(), str(body_lines(data)).encode()]
        if self._xref(ident):
            result.append(b"Xref: " + self._xref(ident))
        return result

    def _over(self, args, rule):
        selected = self._lookup(args, rule, ranges=True)
        if isinstance(selected, Expect):
            return selected
        expected = [self._nov(n, m) for n, m in selected]
        by_id = bool(args and args[0].startswith("<"))
        def content(data):
            rows = framing.lines(data)
            if len(rows) != len(expected):
                return "wrong number of overview rows"
            for row, want in zip(rows, expected):
                fields = row.split(b"\t")
                if by_id and fields[0] == b"0":
                    fields[0] = want[0]
                if fields != want:
                    return "NOV fields differ from retained article (including Xref)"
            return None
        return self._reply(rule, 224, multiline=True, content=content)

    def _cmd_over(self, args):
        return self._over(args, "OVER")

    def _cmd_xover(self, args):
        return self._over(args, "XOVER")

    def _header_value(self, ident, field, xpat=False):
        data = self.view_articles[ident]
        if field == ":bytes":
            return str(len(data)).encode()
        if field == ":lines":
            return str(body_lines(data)).encode()
        if field == "xref" and not xpat:
            return self._xref(ident)
        if field.startswith(":fn-"):
            value = self.policy.get("metadata", {}).get(ident, {}).get(field)
            return value.encode() if isinstance(value, str) else value
        return scrub(headers(data).get(field, b""))

    def _hdr(self, args, rule):
        xpat = rule == "XPAT"
        if (len(args) < 3 if xpat else not 1 <= len(args) <= 2):
            return self._error()
        field = args[0].lower()
        if not re.fullmatch(r":?[!-9;-~]+", field):
            return self._error()
        if field.startswith(":") and field not in {":bytes", ":lines", ":fn-verified", ":fn-control", ":fn-enrollment"}:
            return self._reply(rule, 503)
        pattern = " ".join(args[2:]) if xpat else None
        if pattern is not None:
            wildmat(pattern, "")
        selected = self._lookup(args[1:2], rule, ranges=True)
        if isinstance(selected, Expect):
            return selected
        by_id = len(args) > 1 and args[1].startswith("<")
        expected = []
        for n, ident in selected:
            val = self._header_value(ident, field, xpat)
            if xpat and not wildmat(pattern, (val or b"").decode("utf-8", "replace")):
                continue
            label = ident.encode() if by_id and rule in {"XHDR", "XPAT"} else str(n).encode()
            expected.append((label, val))
        def content(data):
            rows = framing.lines(data)
            if len(rows) != len(expected):
                return "header row count differs"
            for row, (label, val) in zip(rows, expected):
                got, sep, value = row.partition(b" ")
                if got != label and not (by_id and rule == "HDR" and got == b"0"):
                    return "header article label differs"
                if val is not None and value != val:
                    return "header value differs"
                if val and not sep:
                    return "missing header separator"
            return None
        return self._reply(rule, 225 if rule == "HDR" else 221, multiline=True, content=content)

    def _cmd_hdr(self, args):
        return self._hdr(args, "HDR")

    def _cmd_xhdr(self, args):
        return self._hdr(args, "XHDR")

    def _cmd_xpat(self, args):
        return self._hdr(args, "XPAT")

    def _status(self, group):
        flags = self.view_flags[group]
        if flags.get("read_only") or flags.get("posting") == "n" or not self._access(group, "post"):
            return "n"
        return "m" if flags.get("moderated") or flags.get("posting") == "m" else "y"

    def _active_row(self, group, counts=False):
        count, low, high = self._summary(group)
        return f"{group} {high} {low} " + (f"{count} " if counts else "") + self._status(group)

    def _cmd_list(self, args):
        variant, rest = (args[0].upper(), args[1:]) if args else ("ACTIVE", [])
        if variant in {"DISTRIB.PATS", "DISTRIBUTIONS"}:
            return self._reply("LIST", 503) if not rest else self._error()
        if variant == "OVERVIEW.FMT":
            if rest:
                return self._error()
            rows = b"Subject: From: Date: Message-ID: References: Bytes: Lines:".split()
            if self.policy.get("server", ".invalid"):
                rows += [b"Xref:full"]
            return self._reply("LIST", 215, multiline=True, content=packed(rows))
        if variant == "HEADERS":
            if len(rest) > 1 or (rest and rest[0].upper() not in {"MSGID", "RANGE"}):
                return self._error()
            def content(data):
                rows = framing.lines(data)
                required = {b":", b":bytes", b":lines"}
                allowed = required | {b":fn-verified", b":fn-control", b":fn-enrollment"}
                return None if required <= set(rows) <= allowed and len(rows) == len(set(rows)) else "LIST HEADERS does not describe supported fields"
            return self._reply("LIST", 215, multiline=True, content=content)
        if variant == "MOTD":
            return self._error() if rest else self._reply("LIST", 215, multiline=True,
                                                         content=packed(self.policy.get("motd", [])))
        if variant not in {"ACTIVE", "COUNTS", "ACTIVE.TIMES", "NEWSGROUPS", "SUBSCRIPTIONS"}:
            return self._reply("LIST", 501)
        if len(rest) > 1:
            return self._error()
        pattern = rest[0] if rest else "*"
        wildmat(pattern, "")
        names = [g for g in self.view_groups if self._visible(g) and wildmat(pattern, g)]
        if variant == "SUBSCRIPTIONS":
            configured = self.policy.get("subscriptions") or list(self.view_groups)
            return self._reply("LIST", 215, multiline=True, content=packed(g for g in configured if g in names))
        if variant in {"ACTIVE", "COUNTS"}:
            expected = {g: self._active_row(g, variant == "COUNTS").split() for g in names}
            def content(data):
                rows = framing.lines(data)
                if len(rows) != len(expected):
                    return "wrong listing size"
                seen = set()
                for row in rows:
                    if b"\t" in row:
                        return "TAB not permitted in ACTIVE/COUNTS"
                    parts = row.decode("ascii").split(" ")
                    parts = [p for p in parts if p]
                    if not parts or parts[0] not in expected or parts[0] in seen:
                        return "wrong or repeated group"
                    want = expected[parts[0]]
                    if len(parts) != len(want) or parts[-1] != want[-1]:
                        return "wrong listing fields/status"
                    if any(not p.isdecimal() or int(p) != int(w) for p, w in zip(parts[1:-1], want[1:-1])):
                        return "wrong group numbers/count (leading zeroes permitted)"
                    seen.add(parts[0])
                return None
        elif variant == "NEWSGROUPS":
            expected = {g: self.view_flags[g].get("description", "(no description)").encode() for g in names}
            def content(data):
                rows = framing.lines(data)
                found = {}
                for row in rows:
                    parts = re.split(rb"[ \t]+", row, maxsplit=1)
                    if len(parts) != 2 or parts[0] in found:
                        return "invalid/repeated description row"
                    found[parts[0]] = parts[1]
                return None if found == {g.encode(): v for g, v in expected.items()} else "group descriptions differ"
        else:
            window = self.policy.get("group_creation_window")
            if window is not None:
                # Fixture groups were created during this externally observed
                # setup interval; the response never supplies its own oracle.
                lo, hi = window
                def content(data):
                    found = set()
                    for row in framing.lines(data):
                        parts = row.split()
                        if len(parts) != 3 or parts[2] != b"unattributed" or not parts[1].isdigit():
                            return "invalid ACTIVE.TIMES row"
                        name = parts[0].decode("ascii")
                        if name not in names or name in found:
                            return "ACTIVE.TIMES group differs from fixture"
                        exact = self.view_flags[name].get("created_at")
                        if exact is not None:
                            if int(parts[1]) != exact:
                                return "ACTIVE.TIMES creation time differs from retained fact"
                        elif not lo <= int(parts[1]) <= hi:
                            return "ACTIVE.TIMES creation time differs from fixture window"
                        found.add(name)
                    return None if found == set(names) else "ACTIVE.TIMES group set differs from fixture"
            else:
                rows = [f"{g} {self.view_flags[g]['created_at']} unattributed".encode()
                        for g in names if self.view_flags[g].get("created_at") is not None]
                content = row_set(rows)
        return self._reply("LIST", 215, multiline=True, content=content)

    def _instant(self, date, time):
        if not re.fullmatch(r"(?:[0-9]{6}|[0-9]{8})", date) or not re.fullmatch(r"[0-9]{6}", time):
            raise ValueError("bad date/time")
        if len(date) == 6:
            clock = self.policy.get("clock", "unknown")
            if clock is None or clock == "unknown":
                return None
            year = int(str(clock)[:4])
            yy = int(date[:2])
            year = year // 100 * 100 + yy - (100 if yy > year % 100 else 0)
            date = str(year) + date[2:]
        if int(date[:4]) < 1900 or int(time[-2:]) > 60:
            raise ValueError("date/time out of range")
        leap = time[-2:] == "60"
        dt = datetime.strptime(date + time[:-2] + ("59" if leap else time[-2:]), "%Y%m%d%H%M%S")
        return int(dt.replace(tzinfo=timezone.utc).timestamp()) + int(leap)

    def _new(self, args, news):
        rule = "NEWNEWS" if news else "NEWGROUPS"
        offset = int(news)
        if len(args) not in {2 + offset, 3 + offset} or (len(args) == 3 + offset and args[-1].upper() != "GMT"):
            return self._error()
        pattern = args[0] if news else "*"
        wildmat(pattern, "")
        if not news:
            old = self.policy.get("clock", "unknown")
            self.policy["clock"] = self.model.policy.get("clock", "unknown")
            try:
                instant = self._instant(args[offset], args[offset + 1])
            finally:
                self.policy["clock"] = old
        else:
            instant = self._instant(args[offset], args[offset + 1])
        if instant is None:
            # Unknown current year is an input seam: 503 or a correctly framed result.
            if self.policy.get("clock", "unknown") == "unknown":
                return self._reply(rule, {503, 230 if news else 231}, multiline=frozenset({230 if news else 231}))
            return self._reply(rule, 503)
        names = [g for g in self.view_groups if self._visible(g) and wildmat(pattern, g)]
        if not news:
            if self.policy.get("group_creation_window") is None:
                rows = [self._active_row(g).encode() for g in names
                        if self.view_flags[g].get("created_at") is not None
                        and self.view_flags[g]["created_at"] >= instant]
                return self._reply(rule, 231, multiline=True, content=row_set(rows))
            required, optional = set(), set()
            window = self.policy.get("group_creation_window")
            for g in names:
                exact = self.view_flags[g].get("created_at")
                row = self._active_row(g).encode()
                if exact is not None:
                    if exact >= instant:
                        required.add(row)
                elif window is not None:
                    lo, hi = window
                    if lo >= instant:
                        required.add(row)
                    elif hi >= instant:
                        optional.add(row)
            def content(data):
                rows = framing.lines(data)
                actual = set(rows)
                return (None if len(rows) == len(actual) and required <= actual <= required | optional
                        else "NEWGROUPS rows differ from creation facts")
            return self._reply(rule, 231, multiline=True, content=content)
        else:
            ordered = list(self.view_articles)
            rows = []
            clock = self.policy.get("clock")
            horizon = self._instant(str(clock)[:8], str(clock)[8:]) if clock and clock != "unknown" else None
            for i, ident in enumerate(ordered):
                stamp = self.view_stamps.get(ident)
                if stamp is None:
                    stamp = next((self.view_stamps[m] for m in ordered[i + 1:]
                                  if self.view_stamps.get(m) is not None), horizon)
                if (stamp is None or stamp >= instant) and any(ident == m for g in names for _, m in self._available(g)):
                    rows.append(ident.encode())
        return self._reply(rule, 230 if news else 231, multiline=True, content=row_set(rows))

    def _cmd_newgroups(self, args):
        return self._new(args, False)

    def _cmd_newnews(self, args):
        return self._new(args, True)

    def _cmd_post(self, args):
        if args:
            return self._error()
        if not self._posting():
            return self._reply("POST", 440)
        return self._reply("POST", 340, effect=lambda *_: setattr(self, "pending", ("POST", None)))

    def _transit(self, args, rule):
        if not self.peer:
            return self._reply(rule, 502)
        if len(args) != 1 or not msgid(args[0]):
            return self._error()
        ident = args[0]
        if rule == "TAKETHIS":
            result = Expect.none(rule, SPECS[rule])
            result.effect = lambda *_: setattr(self, "pending", (rule, ident))
            return result
        held = ident in self.model.articles
        if rule == "CHECK" and not held and len(self.inflight) >= self.policy.get("max_inflight", 16):
            codes = {431}
        else:
            codes = ({438} if held else {238, 431, 438}) if rule == "CHECK" else ({435} if held else {335, 435, 436})
        def effect(code, *_):
            if code == 335:
                self.pending = (rule, ident)
            if code == 238:
                self.inflight.append(ident)
        pattern = rb"(?:238|431|438) " + re.escape(ident.encode()) + rb"(?: .*)?" if rule == "CHECK" else None
        return self._reply(rule, codes, pattern=pattern, effect=effect)

    def _cmd_ihave(self, args):
        return self._transit(args, "IHAVE")

    def _cmd_check(self, args):
        return self._transit(args, "CHECK")

    def _cmd_takethis(self, args):
        return self._transit(args, "TAKETHIS")

    def send_block(self, block: bytes) -> Expect:
        return self._queue(lambda: self._article_block(block))

    def _article_block(self, block):
        if self.quit or self.handshaking:
            return Expect.none()
        if not self.pending:
            raise ValueError("no POST/IHAVE/TAKETHIS body requested")
        rule, offered = self.pending
        transit = rule != "POST"
        if rule == "TAKETHIS" and isinstance(offered, bytes):
            # Invalid/missing ID binding is unspecified: retain the sent token
            # or the conventional absent-ID marker, never permit success.
            terminated = block == b".\r\n" or block.endswith(b"\r\n.\r\n")
            try:
                valid_id = msgid(offered.decode("utf-8"))
            except UnicodeError:
                valid_id = False
            echo = re.escape(offered) if valid_id else rb"(?:" + re.escape(offered) + rb"|-)"
            pattern = rb"439 " + echo + rb"(?: .*)?"
            return self._reply(rule, 439, pattern=pattern,
                               effect=lambda *_: self._finish_body(close=not terminated),
                               close_after_reply=not terminated,
                               close_effect=lambda: self._finish_body(close=True))
        try:
            data = framing.decode_block(block)
        except framing.FramingError:
            code = 439 if rule == "TAKETHIS" else 437 if transit else 441
            pattern = b"439 " + re.escape(offered.encode()) + rb"(?: .*)?" if rule == "TAKETHIS" else None
            # A rejected but terminated block can be drained without closing.
            # EOF is a transport observation, never implied by a 4xx reply.
            terminated = block == b".\r\n" or block.endswith(b"\r\n.\r\n")
            return self._reply(rule, code, pattern=pattern,
                               effect=lambda *_: self._finish_body(close=not terminated),
                               close_after_reply=True, close_without_reply=True,
                               close_effect=lambda: self._finish_body(close=True),
                               close_spec="specs/nntp.md:513-518; RFC 3977 §3.1.1")
        fields = headers(data)
        ident = fields.get("message-id", b"").decode("ascii", "replace").strip()
        groups = fields.get("newsgroups", b"").decode("ascii", "replace").replace(" ", "").split(",")
        limit = min(self.policy.get("article_limit", float("inf")), self.policy.get("inbound_max_octets", float("inf"))) if transit else self.policy.get("article_limit", float("inf"))
        # Peering S, specs/peering.md:146-153,756-765: a transfer's local
        # memberships are its Newsgroups names that match the peer record's
        # accept-groups and are live; none in scope is :out-of-scope (437).
        accept = self.policy.get("peer_accept") if transit else None
        def in_scope(g):
            return (g in self.model.groups and not self.model.flags[g].get("retired")
                    and (accept is None or wildmat(accept, g)))
        reason, definite = None, False
        if len(data) > limit:
            reason, definite = "too large|bound|limit|size", True
        elif not b"\r\n\r\n" in data or any(not fields.get(f) for f in ("from", "subject", "newsgroups")):
            reason, definite = "malformed|missing|required|syntax", True
        elif transit and any(not fields.get(f) for f in ("message-id", "date", "path")):
            reason, definite = "malformed|missing|required|syntax", True
        elif any(len(re.findall(rb"(?im)^" + f + rb":", data.partition(b"\r\n\r\n")[0])) > 1
                 for f in (b"from", b"subject", b"newsgroups", b"message-id", b"date", b"path")):
            reason, definite = "duplicat|malformed|field|Path", True
        elif not transit and "path" in fields and (b"POSTED" in fields["path"].upper() or
                not re.fullmatch(rb"[^\s!]+(?:![^\s!]+)*", fields["path"])):
            reason, definite = "Path|path", True
        elif offered and ident != offered:
            reason, definite = "Message-ID|message-id|mismatch", True
        elif ident and not stored_msgid(ident):
            reason, definite = "Message-ID|message-id|malformed", True
        elif not transit and self.model.policy.get("clock", "unknown") is None:
            reason, definite = "no usable clock reading", True
        elif ident in self.model.articles:
            reason, definite = ("this article is already stored here" if self.model.sources[ident] == data else
                                "a different article with this Message-ID is stored here"), True
        elif not any(in_scope(g) for g in groups):
            reason, definite = "group|newsgroup", True
        elif not transit and any(not self._access(g, "post") or self._status(g) == "n"
                                 for g in groups if g in self.view_flags):
            reason, definite = "read-only|group|newsgroup", True
        elif not transit and any(f in fields for f in ("xref", "injection-date", "injection-info")):
            reason, definite = "Xref|Injection|injection|xref", True
        moderated = [g for g in groups if g in self.view_flags and
                     (self.view_flags[g].get("moderated") or self.view_flags[g].get("posting") == "m")]
        if not definite and moderated and (transit and "approved" not in fields or
                not transit and "approved" in fields and any(self.authenticated_as not in self.view_flags[g].get("moderators", []) for g in moderated)):
            reason, definite = "Approved|moderator|moderated|approval", True
        success = 235 if rule == "IHAVE" else 239 if rule == "TAKETHIS" else 240
        failure = 437 if rule == "IHAVE" else 439 if rule == "TAKETHIS" else 441
        codes = {failure} if definite else {success, failure, 436} if transit else {240, 441}
        if transit and ident in self.model.articles:
            codes = {failure}
        if rule == "TAKETHIS":
            pattern = rb"(?:239|439|436) " + re.escape(offered.encode()) + rb"(?: .*)?"
        elif definite and not transit:
            pattern = rb"441 .*?(?:" + reason.encode() + rb").*"
        elif not transit:
            pattern = rb"(?:240(?: .*)?|441 .*?(?:malformed|unaffordable|history-exhausted|storage-failed|control-not-filed|control-malformed|refused|read-only|moderat|login-unsigned|login-not-bound|uncertain|clock|bound|limit|size|group|field|Path|Xref|Injection|mpx-saturated).*)"
        else:
            pattern = None
        def effect(code, status, _):
            if code == success:
                accepted_id = ident
                if not accepted_id:
                    found = re.search(rb"<[^<>\s]+@[^<>\s]+>", status)
                    accepted_id = found[0].decode() if found else self.policy.get("generated_id")
                    if not accepted_id:
                        raise ValueError("accepted POST omitted Message-ID: supply policy.generated_id for read-back")
                target = [g for g in groups if in_scope(g)]
                if not transit and moderated and "approved" not in fields:
                    target = [self.view_flags[moderated[0]].get("queue", moderated[0] + ".moderation")]
                    accepted_id = "<fn-moderate." + accepted_id[1:]
                stored = self.policy.get("stored_articles", {}).get(accepted_id)
                if stored is None:
                    if transit:
                        agent = self.policy.get("server", ".invalid")
                        stored = re.sub(rb"(?im)^Xref:[^\r\n]*\r\n(?:[ \t][^\r\n]*\r\n)*", b"", data)
                        stored = re.sub(rb"(?im)^(Path: )", lambda m: m[0] + str(agent).encode() + b"!", stored, count=1)
                    elif self.authenticated_as or not fields.get("date") or not ident or (moderated and "approved" not in fields):
                        raise ValueError("accepted generated/authenticated/moderated POST needs policy.stored_articles[Message-ID] for exact read-back")
                    else:
                        agent = self.policy.get("server", ".invalid")
                        path = b"" if "path" in fields else f"Path: {agent}!not-for-mail\r\n".encode()
                        source = re.sub(rb"(?im)^(Path: )", lambda m: m[0] + str(agent).encode() + b"!", data, count=1)
                        stored = path + f"Injection-Info: {agent}\r\n".encode() + source
                self.model.add_article(accepted_id, stored, target, stamp=self.policy.get("acceptance_stamp"))
                self.model.sources[accepted_id] = data
                self._pin()
            if offered in self.inflight:
                self.inflight.remove(offered)
            self._finish_body(close=transit and len(data) > limit)
            outcome = "accepted" if code == success else "uncertain" if b"uncertain" in status.lower() else "refused"
            self.model.post_outcomes.append((rule, ident or offered, outcome, status))
            # HW, specs/nntp.md:2321: an accepted authenticated submission
            # witnesses a principal charge. Refused malformed input may never
            # reach submission, so this short workload makes no charge claim.
            if self.model.limits is not None and code == success and not transit and self.authenticated_as:
                posts = self.model.principal_posts
                posts[self.authenticated_as] = posts.get(self.authenticated_as, 0) + 1
        return self._reply(rule, codes, pattern=pattern, effect=effect,
                           close_after_reply=transit and len(data) > limit,
                           close_spec="specs/nntp.md:530-534")

    def _finish_body(self, close=False):
        self.pending = None
        self.quit = self.quit or close

    def _authenticate(self, name):
        self.authenticated_as = name
        self._pend()
        if self.current_group and not self._visible(self.current_group):
            self.current_group = self.current_article_number = None

    def _pend(self, username=None, sasl=None, redeem=None):
        # One pending slot per connection (fn1 books/nntp-auth.lisp "The pending slot"; specs/nntp.md
        # states each exchange alone): AUTHINFO USER's name, a SASL exchange, or XREDEEM's code and login.
        # Starting one exchange replaces whatever another left (H6: USER, XREDEEM CODE NAME, AUTHINFO PASS
        # answers 482 out of sequence on fn1).
        self.username, self.sasl, self.redeem = username, sasl, redeem

    def _failed_auth(self, *, cancelled=False):
        # HW, specs/nntp.md:2320,2327-2331: count observed 481s per address,
        # independently of the RFC 4643 three-failure SESSION rule.
        limit = self.model.limits.get('exposure-auth-failures') if self.model.limits is not None else 0
        failures = self.model.address_failures.get(self.address, 0)
        closing = (not cancelled and self.failed_auth_count == 2) or bool(limit and failures + 1 >= limit)
        def effect(*_):
            self._pend()
            if self.model.limits is not None:
                self.model.address_failures[self.address] = failures + 1
            if not cancelled:
                self.failed_auth_count += 1
            self.quit = closing
        return self._reply("AUTHINFO", 481, tail=(400,) if closing else (), effect=effect,
                           close_after_reply=closing, close_spec="specs/nntp.md:1661-1696; RFC 4643 §6")

    def _cmd_authinfo(self, args):
        if self.authenticated_as or self.compressed:
            return self._reply("AUTHINFO", 502)
        if not args:
            return self._error()
        form = args[0].upper()
        if form == "SASL":
            return self._begin_sasl(args[1:])
        if form not in {"USER", "PASS"}:
            return self._reply("AUTHINFO", 501)
        if self.policy.get("protected_only") and not self.tls:
            return self._reply("AUTHINFO", 483)
        if len(args) != 2:
            return self._error()
        if form == "USER":
            return self._reply("AUTHINFO", 381, effect=lambda *_: self._pend(username=args[1]))
        if self.username is None:
            return self._reply("AUTHINFO", 482)
        name = self.username
        account = self.credentials.get(name)
        password = account.get("password") if isinstance(account, dict) else account
        if account is None or args[1] != password:
            return self._failed_auth()
        return self._reply("AUTHINFO", 281, effect=lambda *_: self._authenticate(name))

    @staticmethod
    def _base64(value):
        if value == "=":
            return b""
        raw = base64.b64decode(value, validate=True)
        if base64.b64encode(raw).decode() != value:
            raise ValueError("noncanonical base64")
        return raw

    def _begin_sasl(self, args):
        if len(args) not in {1, 2}:
            return self._error()
        mech = args[0].upper()
        if (self.policy.get("protected_only") or mech == "PLAIN") and not self.tls:
            return self._reply("AUTHINFO", 483)
        offered, optional = self._sasl_offers()
        if mech in optional:
            raise RuntimeError("AUTHINFO SASL PLUS needs observed exporter or explicit sasl_mechanisms (E5)")
        if mech not in offered:
            return self._reply("AUTHINFO", 503)
        if len(args) == 2:
            try:
                initial = self._base64(args[1])
            except (ValueError, binascii.Error):
                return self._reply("AUTHINFO", 504)
            return self._sasl_outcome(mech, self._sasl_name(mech, initial))
        return self._reply("AUTHINFO", 383, pattern=rb"383 =",
                           effect=lambda *_: self._pend(sasl=mech))

    def _sasl_name(self, mech, value):
        # Identity syntax only: proof, password and channel binding are H2b inputs.
        if mech == "PLAIN" and len(value.split(b"\0")) == 3:
            return value.split(b"\0")[1].decode("utf-8", "replace")
        elif mech.startswith("SCRAM"):
            found = re.search(rb"(?:^|,)n=([^,]+)", value)
            if found:
                return found[1].decode().replace("=2C", ",").replace("=3D", "=")
        return self.sasl_identity

    def _sasl_outcome(self, mech, identity=None):
        accepted = 281 if mech == "PLAIN" else 283
        failure = self._failed_auth()
        # A third failed exchange has an extra status; predicate selects that branch.
        def effect(code, status, body):
            if code == 383:
                self._pend(sasl=mech)
                self.sasl_identity = identity or self.sasl_identity
            elif code == accepted:
                name = identity or self.sasl_identity or self.policy.get("sasl_identity")
                if name is None:
                    raise ValueError("set Conn.sasl_identity before committing abstract SASL success")
                self._authenticate(name)
            else:
                failure.update(status, body)
                result._close_after_reply = failure.close_after_reply
                result._close_spec = failure.close_spec
        result = self._reply("AUTHINFO", {383, accepted, 481}, effect=effect)
        base_check = result.check
        def check(status, body, *, eof=False):
            if status.startswith(b"481"):
                return failure.check(status, body, eof=eof)
            v = base_check(status, body, eof=eof)
            if v.ok and status.startswith((b"383", b"283")):
                try:
                    self._base64(status[4:-2].decode())
                except (ValueError, UnicodeError):
                    return Verdict(False, "AUTHINFO", SPECS["AUTHINFO"], "noncanonical SASL challenge/final")
            return v
        result.check = check
        return result

    def _sasl_response(self, line):
        # P-SASL-LINE (H7, adjudicated with fn1's replies): a response is a line before it is base64. A line past
        # 512 octets, or one carrying a bare CR or LF, is malformed, 501 as any such line is (specs/nntp.md:513-518).
        # Any other line, empty or with control octets included, that is not canonical base64 is 504
        # (specs/nntp.md:1724-1725). Either ends the exchange.
        body = line[:-2] if line.endswith(b"\r\n") else line
        if len(line) > framing.COMMAND_LIMIT or b"\r" in body or b"\n" in body:
            result = self._malformed(overlong=len(line) > framing.COMMAND_LIMIT)
            result.effect = lambda *_: setattr(self, "sasl", None)
            return result
        try:
            value = framing.command_line(line).decode("ascii")
            if value == "*":
                return self._failed_auth(cancelled=True)
            raw = self._base64(value)
        except (ValueError, UnicodeError):
            return self._reply("AUTHINFO", 504, effect=lambda *_: setattr(self, "sasl", None))
        return self._sasl_outcome(self.sasl, self._sasl_name(self.sasl, raw))

    def _cmd_starttls(self, args):
        if args:
            return self._error()
        if self.tls or self.authenticated_as or self.compressed:
            return self._reply("STARTTLS", 502)
        if not self.policy.get("starttls", True):
            return self._reply("STARTTLS", 580)
        def effect(code, *_):
            if code == 382:
                self.handshaking = True
                self._pend()
                self.sasl_identity = None
        return self._reply("STARTTLS", {382, 580}, effect=effect)

    def tls_established(self):
        if not self.handshaking:
            raise ValueError("no TLS handshake owed")
        self.handshaking, self.tls = False, True
        self.current_group = self.current_article_number = None

    def _cmd_compress(self, args):
        if self.compressed:
            return self._reply("COMPRESS", 502)
        if not self.authenticated_as:
            # NNT-054: "a client may compress its session after authentication".
            # Neither spec orders that gate against the argument checks, so an
            # unauthenticated bad argument admits either refusal (HV-01).
            extra = {501} if len(args) != 1 else {503} if args[0].upper() != "DEFLATE" else set()
            return self._reply("COMPRESS", {480} | extra)
        if len(args) != 1:
            return self._error()
        if args[0].upper() != "DEFLATE":
            return self._reply("COMPRESS", 503)
        return self._reply("COMPRESS", 206, effect=lambda *_: setattr(self, "compressed", True))

    def _cmd_xredeem(self, args):
        if self.authenticated_as or self.compressed:
            return self._reply("XREDEEM", 502)
        if self.policy.get("protected_only") and not self.tls:
            return self._reply("XREDEEM", 483)
        if len(args) != 2:
            return self._error()
        if args[0].upper() != "PASS":
            # specs/nntp.md:1843,1860: `XREDEEM CODE NAME -> 381` caches whatever CODE says; a code that is
            # not the operator's 32 hex characters is refused at PASS (482), never at this line (H7: fn1
            # agrees; the model's former 501 here had no spec line).
            return self._reply("XREDEEM", 381, effect=lambda *_: self._pend(redeem=tuple(args)))
        if self.redeem is None:
            return self._reply("XREDEEM", 482)
        code, name = self.redeem
        prior = self.model.redemptions.get(code)
        codes = {482} if prior and prior != (name, args[1]) else {281, 482}
        def effect(answer, *_):
            self.redeem = None
            if answer == 281:
                self.model.redemptions[code] = (name, args[1])
                self.model.accounts[name] = {"password": args[1]}
        return self._reply("XREDEEM", codes, effect=effect)

    def _cmd_xfncatchup(self, args):
        if not self.peer:
            return self._reply("XFNCATCHUP", 502)
        if len(args) != 4 or not args[1].isdigit() or not args[3].isdigit() or int(args[3]) < 1:
            return self._error()
        wildmat(args[0], "")
        return self._reply("XFNCATCHUP", {291, 423, 501}, multiline=frozenset({291}))

    def _cmd_xfn_zarticle(self, args):
        if len(args) < 2 or not msgid(args[0]) or any(not re.fullmatch(r"[0-9a-f]{64}", d) for d in args[1:]):
            return self._error()
        plain = self._retrieve(args[:1], "ARTICLE")
        if 220 not in plain.codes:
            return plain
        compressed = self._reply("XFN-ZARTICLE", 229, multiline=True,
            pattern=rb"229 (?:" + b"|".join(d.encode() for d in args[1:]) + rb") [0-9]+ [0-9]+(?: .*)?",
            content=lambda data: "encoded line exceeds 128 octets" if any(len(r) > 128 for r in framing.lines(data)) else None)
        result = self._reply("XFN-ZARTICLE", {220, 229}, multiline=True)
        result.check = lambda status, body, eof=False: (compressed if status.startswith(b"229") else plain).check(status, body, eof=eof)
        return result
