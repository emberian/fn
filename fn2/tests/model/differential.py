"""Seeded wire differential: fn1 Gen supplies syntax; H2a alone judges replies.

Fake fixtures deliberately include a withdrawn predecessor and a dot body.
The live Node initializes EMPTY groups (PRESENT_IDS is only a generator pool).
See DIFFERENCES.md for seams, cut semantics, replay format and classification.
"""
from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager, ExitStack
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
from re import _parser as regex_parser  # Python 3.11; fake witness renderer only
import signal
import socket
import ssl
import shutil
import subprocess
import tempfile
import time
import tomllib
from unittest.mock import patch
import zlib

from tests import fuzz_nntp as fz
from . import framing
from .nntp_model import Expect, HELP, NntpModel, Verdict, msgid, packed, wildmat

PLANTS = ('reuse-number', '423-for-420', 'frame-after-quit',
          'wrong-over-field', 'dot-unstuffed',
          # H7c: one plant per focus (tls_auth's auth, peering's feed).
          'auth-wrong-accepted', 'feed-wrong-id')
CUTS = ('whole', 'per-item', 'bytewise')
BARRIERS = {b'POST', b'IHAVE', b'TAKETHIS', b'STARTTLS', b'COMPRESS', b'AUTHINFO'}
ROOT = Path(__file__).resolve().parents[3]


class FocusGen(fz.Gen):
    """fn1's Gen with its step distribution narrowed to one surface family's commands (H7c).

    The productions are Gen's own (the protocol table's :fuzz grammar through Gen.cmd and its AUTHINFO
    cases); only the weights change. `auth` is tls_auth's F (AUTHINFO USER/PASS/SASL arguments, XREDEEM,
    STARTTLS, with reads between them to observe the authentication state); `feed` is peering's F
    (IHAVE/CHECK/TAKETHIS offers and articles, and XFNCATCHUP, which fn1's Gen leaves unfuzzed).
    """
    FOCUS = ('auth', 'feed')

    def __init__(self, seed, mode, ids=None, focus='auth'):
        super().__init__(seed, mode, ids)
        if focus not in self.FOCUS:
            raise ValueError('unknown focus ' + focus)
        self.focus = focus

    def step(self):
        r = self.rng.random()
        if self.focus == 'auth':
            if r < 0.55:
                kind = self.rng.randrange(5)
                cases = fz.PROTOCOL["AUTHINFO"]["fuzz"][0][1:]
                # A *-PLUS mechanism needs the connection's TLS exporter, which the model is not given
                # (nntp_model raises: E5); the focus sends its plain sibling instead.
                return [self.command([b"AUTHINFO"] + self.words(words)).replace(b"-PLUS", b"")
                        for words in cases[kind]]
            if r < 0.70:
                return [self.cmd("XREDEEM")]
            if r < 0.78:
                return [self.cmd("STARTTLS")] if self.mode != "tls" else [self.cmd("HELP")]
            if r < 0.92:
                return [self.cmd(self.family("GROUP", "ARTICLE", "STAT", "LIST", "CAPABILITIES"))]
            return [self.choice(fz.GARBAGE_LINES)]
        if r < 0.25:
            mid = self.msgid()
            items = [self.cmd("IHAVE", {"mid": (mid,)})]
            if self.chance(0.8):
                items.append(self.article(mid if self.chance(0.9) else None, transit=True))
            return items
        if r < 0.45:
            return [self.cmd("CHECK")]
        if r < 0.65:
            mid = self.msgid()
            return [self.cmd("TAKETHIS", {"mid": (mid,)}),
                    self.article(mid if self.chance(0.9) else None, transit=True)]
        if r < 0.90:
            return [self.cmd("XFNCATCHUP")]
        if r < 0.95:
            return [self.cmd("MODE")]
        return [self.choice(fz.GARBAGE_LINES)]


def generator(seed, mode, focus=None):
    return FocusGen(seed, mode, fz.PRESENT_IDS, focus) if focus else fz.Gen(seed, mode, fz.PRESENT_IDS)


def fixture(fake=True, config=None):
    # article_limit: fz.Node makes its store with `store init`, the development profile, whose
    # max-article-octets is 32768 (`operator CONFIG status`, H7 probe on image c14e9e8e). A transit article past
    # it is refused by name and the connection closed (specs/nntp.md:530-534; H7-OPEN-1).
    policy = dict(required=False, protected_only=False, posting=True,
                  peers=['127.0.0.1'], server='.invalid', starttls=True, article_limit=32768)
    if config:
        cfg = tomllib.loads(Path(config).read_text())
        policy.update(required=cfg['auth']['required'],
                      protected_only=cfg['auth']['protected_only'],
                      posting=cfg['posting']['enabled'])
    model = NntpModel({'fn.test': {}, 'fn.letters': {}}, [],
                      {'fuzz': {'password': 'fuzz-password', 'posting': True}}, policy)
    if fake:
        old = '<withdrawn@fixture.invalid>'
        mid = fz.PRESENT_IDS[0].decode()
        data = (f'From: author@example.invalid\r\nSubject: fixture\r\n'
                f'Date: Mon, 21 Sep 2026 12:00:00 +0000\r\nMessage-ID: {mid}\r\n'
                'Newsgroups: fn.test,fn.letters\r\n\r\n.dot\r\nbody\r\n').encode()
        model.add_article(old, data, ['fn.test', 'fn.letters'])
        model.withdraw(old)
        model.add_article(mid, data, ['fn.test', 'fn.letters'])
    return model


def connection(model, mode, transport):
    return model.connect(tls=False, implicit_tls=transport == 'implicit',
                         address='127.0.0.1' if mode == 'peer' else '127.0.0.2')


def witness(pattern):
    """A shortest regex witness, never used by the oracle or live target."""
    def render(nodes):
        out = bytearray()
        for op, arg in nodes:
            name = str(op)
            if name == 'LITERAL':
                out.append(arg)
            elif name == 'ANY':
                out.extend(b'x')
            elif name == 'SUBPATTERN':
                out.extend(render(arg[-1]))
            elif name == 'BRANCH':
                out.extend(render(arg[1][0]))
            elif name in ('MAX_REPEAT', 'MIN_REPEAT'):
                out.extend(render(arg[2]) * arg[0])
            elif name == 'IN':
                kind, value = arg[0]
                out.append(value if str(kind) == 'LITERAL' else value[0])
            elif name != 'AT':
                raise ValueError(f'unsupported fake regex opcode {name}')
        return bytes(out)
    return render(regex_parser.parse(pattern, 0))


def fake_content(c, command, exp):
    """Render one permitted body from the fake's separate model state."""
    if isinstance(exp.content, bytes):
        return exp.content
    words = command.decode('utf-8', 'replace').strip().split()
    verb, args = words[0].upper(), words[1:]
    if verb == 'HELP':
        return HELP
    if verb == 'CAPABILITIES':
        rows = [b'VERSION 2', b'READER', b'OVER MSGID', b'HDR', b'XPAT', b'NEWNEWS',
                b'LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT',
                b'IMPLEMENTATION H2b-fake']
        rows += [b'POST'] if c._posting() else []
        rows += [b'IHAVE', b'STREAMING'] if c.peer else []
        if not (c.tls or c.authenticated_as or c.compressed):
            rows += [b'STARTTLS']
        if c.authenticated_as and not c.compressed:
            rows += [b'COMPRESS DEFLATE']
        rows += [b'SASL SCRAM-SHA-256' + (b' PLAIN' if c.tls else b'')]
        if not (c.authenticated_as or c.compressed):
            rows += [b'AUTHINFO USER SASL']
        return packed(rows)
    if verb == 'LISTGROUP':
        group = args[0] if args else c.current_group
        rows = c._available(group, live=True)
        if len(args) == 2:
            from .nntp_model import number_range
            lo, hi = number_range(args[1], c.model.watermarks[group])
            rows = [(n, m) for n, m in rows if lo <= n <= hi]
        return packed(str(n) for n, _ in rows)
    if verb in ('OVER', 'XOVER'):
        return packed(b'\t'.join(c._nov(n, m)) for n, m in c._lookup(args, verb, True))
    if verb in ('HDR', 'XHDR', 'XPAT'):
        rows = []
        for n, mid in c._lookup(args[1:2], verb, True):
            val = c._header_value(mid, args[0].lower(), verb == 'XPAT') or b''
            if verb == 'XPAT' and not wildmat(' '.join(args[2:]), val.decode('utf-8', 'replace')):
                continue
            label = mid if len(args) > 1 and args[1].startswith('<') and verb != 'HDR' else str(n)
            rows.append(label.encode() + b' ' + val)
        return packed(rows)
    if verb == 'LIST':
        variant = args[0].upper() if args else 'ACTIVE'
        pattern = args[1] if len(args) > 1 else '*'
        names = [g for g in c.view_groups if c._visible(g) and wildmat(pattern, g)]
        if variant in ('ACTIVE', 'COUNTS'):
            return packed(c._active_row(g, variant == 'COUNTS') for g in names)
        if variant == 'HEADERS':
            return b':\r\n:bytes\r\n:lines\r\n'
        if variant == 'NEWSGROUPS':
            return packed(g + ' ' + c.view_flags[g].get('description', '(no description)') for g in names)
        if variant == 'ACTIVE.TIMES':
            return packed(f"{g} {c.view_flags[g]['created_at']} unattributed"
                          for g in names if c.view_flags[g].get('created_at') is not None)
    if verb in ('NEWNEWS', 'NEWGROUPS'):
        # These model predicates capture the independently computed row set.
        # Only the fake renderer reads it; the driver uses check/update only.
        cells = dict(zip(exp.content.__code__.co_freevars,
                         (x.cell_contents for x in exp.content.__closure__ or ())))
        return packed(sorted(cells['required']) if 'required' in cells else cells['expected'])
    return b''


def fake_reply(c, command, exp):
    e = exp._get()
    if e.rule == 'XFN-ZARTICLE':
        e = c._retrieve(command.decode().split()[1:2], 'ARTICLE')
    if not e.codes:
        status, body = b'', None
    else:
        # Refuse nondeterministic POSTs: generated stored projections are E3 inputs.
        code = next((x for x in (441, 437, 439, 503, 482, 383) if x in e.codes), min(e.codes))
        status = witness(e.pattern) if e.pattern else str(code).encode() + b' fake'
        # Regex alternatives may start with another permitted code (POST success).
        if e.pattern and int(status[:3]) != code:
            for candidate in (str(code).encode() + status[3:],
                              str(code).encode() + b' refused', str(code).encode() + b' ='):
                if re.fullmatch(e.pattern, candidate):
                    status = candidate
                    break
        if status.startswith((b'383', b'283')) and not e.pattern:
            status = status[:3] + b' ='
        status += b'\r\n' + packed(str(x) + ' closing' for x in e.tail)
        if status.startswith(b'481') and c.failed_auth_count == 2 and not e.tail:
            status += b'400 closing\r\n'
        body = framing.encode_block(fake_content(c, command, e)) if e.multiline_for(status) else None
    exp.update(status, body)
    return status, body


def take(data, body=False, start=0):
    """Extract a wire command/body; incomplete suffix remains an EOF input."""
    if body:
        end = 3 if data.startswith(b'.\r\n') else data.find(b'\r\n.\r\n', start) + 5
        return end if end >= 5 or data.startswith(b'.\r\n') else 0
    at = data.find(b'\r\n', start)
    return at + 2 if at >= 0 else 0


class Fake:
    def __init__(self, mode, transport, plants=()):
        self.conn = connection(fixture(), mode, transport)
        self.plants, self.input, self.output = set(plants), bytearray(), bytearray()
        self.closed = False
        self.quitted = False
        self.scan = 0
        self.enc = self.dec = None
        status, body = fake_reply(self.conn, b'', self.conn.greeting())
        self.output.extend(status)

    def sendall(self, data):
        self.input.extend(self.dec.decompress(data) if self.dec else data)
        while not self.conn.handshaking:
            end = take(self.input, bool(self.conn.pending), self.scan)
            if not end:
                self.scan = max(0, len(self.input) - 4)
                break
            command = bytes(self.input[:end])
            del self.input[:end]
            self.scan = 0
            exp = self.conn.send_block(command) if self.conn.pending else self.conn.send(command)
            status, body = fake_reply(self.conn, command, exp)
            rule = exp._get().rule
            self.quitted = self.quitted or (rule == 'QUIT' and status.startswith(b'205'))
            if 'reuse-number' in self.plants and rule == 'GROUP' and status.startswith(b'211'):
                # Reassign the replacement to its withdrawn predecessor's number.
                g = self.conn.current_group
                self.conn.model.groups[g][-1] = (1, self.conn.model.groups[g][-1][1])
                self.conn.model.watermarks[g] = 1
                self.conn._pin()
                status = f'211 1 1 1 {g}\r\n'.encode()
            if '423-for-420' in self.plants and rule == 'XOVER' and status.startswith(b'420'):
                status = b'423' + status[3:]
            if 'frame-after-quit' in self.plants and rule == 'closed' and self.quitted:
                status = b'500 after quit\r\n'
            if 'wrong-over-field' in self.plants and rule in ('OVER', 'XOVER') and body:
                fields = body.split(b'\t')
                if len(fields) > 1:
                    fields[1] = b'wrong subject'
                    body = b'\t'.join(fields)
            if 'dot-unstuffed' in self.plants and body:
                body = framing.unstuff(body)
            if 'auth-wrong-accepted' in self.plants and rule == 'AUTHINFO' and status.startswith(b'481'):
                status = b'281 planted\r\n'
            if 'feed-wrong-id' in self.plants and rule in ('CHECK', 'TAKETHIS') and re.match(rb'^(238|239|431|438|439) <', status):
                status = status[:4] + b'<planted@fixture.invalid>\r\n'
            payload = status + (body or b'')
            self.output.extend(self.enc.compress(payload) + self.enc.flush(zlib.Z_SYNC_FLUSH)
                               if self.enc else payload)
            if status.startswith(b'206'):
                self.compress()
                break

    def recv(self, size):
        result = bytes(self.output[:size])
        del self.output[:size]
        if not result and not (self.closed or self.conn.quit):
            raise socket.timeout('fake needs more input')
        return result

    def shutdown(self, _):
        if self.conn.pending and not self.closed:
            status, body = fake_reply(self.conn, bytes(self.input),
                                      self.conn.send_block(bytes(self.input)))
            self.input.clear()
            payload = status + (body or b'')
            self.output.extend(self.enc.compress(payload) + self.enc.flush(zlib.Z_SYNC_FLUSH)
                               if self.enc else payload)
        self.closed = True

    def close(self):
        self.closed = True

    def tls(self):
        self.conn.tls_established()

    def compress(self):
        self.enc, self.dec = zlib.compressobj(wbits=-15), zlib.decompressobj(wbits=-15)


class TLS:
    """TLS half-close with application reads between the two close_notify alerts.

    SSLSocket.unwrap waits for BOTH alerts and can discard a final application
    reply as APPLICATION_DATA_AFTER_CLOSE_NOTIFY. MemoryBIO lets unwrap send our
    alert first, then read the reply before completing the peer's shutdown.
    """
    def __init__(self, sock, context, timeout):
        self.sock, self.timeout = sock, timeout
        self.incoming, self.outgoing = ssl.MemoryBIO(), ssl.MemoryBIO()
        self.session = context.wrap_bio(self.incoming, self.outgoing,
                                        server_hostname='localhost')
        self.buffer = bytearray()
        self.client_close_notify = self.server_close_notify = False
        self._call(self.session.do_handshake)

    def _flush(self):
        while self.outgoing.pending:
            self.sock.sendall(self.outgoing.read())

    def _call(self, operation):
        deadline = time.monotonic() + self.timeout
        while True:
            try:
                result = operation()
                self._flush()
                return result
            except ssl.SSLWantReadError:
                self._flush()
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    raise socket.timeout('TLS operation deadline')
                self.sock.settimeout(remaining)
                data = self.sock.recv(65536)
                if data:
                    self.incoming.write(data)
                else:
                    self.incoming.write_eof()

    def settimeout(self, timeout):
        self.timeout = timeout
        self.sock.settimeout(timeout)

    def sendall(self, data):
        while data:
            used = self._call(lambda: self.session.write(data))
            data = data[used:]

    def recv(self, size):
        if self.buffer:
            data = bytes(self.buffer[:size])
            del self.buffer[:size]
            return data
        try:
            data = self._call(lambda: self.session.read(size))
        except ssl.SSLZeroReturnError:
            data = b''
        if not data:
            self.server_close_notify = True
            self.close_write()  # Respond only after observing the peer's alert.
        return data

    def close_write(self):
        if self.client_close_notify:
            return
        # A socket read can have supplied several records. Preserve already
        # buffered application records before asking SSL_shutdown to inspect
        # them; SSL_shutdown itself rejects those as post-close application data.
        while True:
            try:
                data = self.session.read(65536)
                if not data:
                    self.server_close_notify = True
                    break
                self.buffer.extend(data)
            except ssl.SSLWantReadError:
                break
            except ssl.SSLZeroReturnError:
                self.server_close_notify = True
                break
        # No network read here: leave final application records for recv().
        try:
            self.session.unwrap()
            self.server_close_notify = True
        except ssl.SSLWantReadError:
            pass
        self._flush()
        self.client_close_notify = True

    def version(self):
        return self.session.version()

    def close(self):
        self.sock.close()


class Wire:
    def __init__(self, sock, node=None, timeout=3):
        self.sock, self.node, self.timeout = sock, node, timeout
        self.buffer, self.received = bytearray(), bytearray()
        self.eof = self.timed_out = False
        self.reset = None
        self.client_half_closed = False
        self.enc = self.dec = None
        self.deadline = float('inf')

    # A reply can only follow the server's consumption of what was sent before it: the bytewise cut sends one
    # segment per octet, and over TLS one record per octet, which a node consumes for seconds (H7-08: a 100 KB
    # TAKETHIS article's 439 arrived after the flat 3 s window). Each segment since the last reply extends that
    # reply's window by SEGMENT_SECONDS, at most SEGMENT_CAP_SECONDS.
    SEGMENT_SECONDS, SEGMENT_CAP_SECONDS = 1e-4, 60.0

    def reply_window(self):
        window = self.timeout + min(self.SEGMENT_CAP_SECONDS, self.SEGMENT_SECONDS * getattr(self, 'segments', 0))
        self.segments = 0
        return window

    def send(self, pieces):
        pieces = list(pieces)
        self.segments = getattr(self, 'segments', 0) + len(pieces)
        for piece in pieces:
            payload = self.enc.compress(piece) + self.enc.flush(zlib.Z_SYNC_FLUSH) if self.enc else piece
            try:
                self.sock.sendall(payload)
            except (BrokenPipeError, ConnectionResetError):
                return  # The read side still determines whether closure was permitted.

    def read(self):
        try:
            if not isinstance(self.sock, Fake):
                self.sock.settimeout(max(0.001, min(self.timeout, self.deadline - time.monotonic())))
            data = self.sock.recv(65536)
            if not data:
                self.eof = True
            if self.dec:
                data = self.dec.decompress(data)
            self.buffer.extend(data)
            self.received.extend(data)
        except socket.timeout:
            self.timed_out = True
        except OSError as exc:
            self.reset, self.eof = repr(exc), True

    def line(self):
        deadline = min(self.deadline, time.monotonic() + max(self.timeout, getattr(self, 'line_window', 0)))
        while b'\r\n' not in self.buffer and not (self.eof or self.timed_out):
            if time.monotonic() >= deadline:
                self.timed_out = True
                break
            self.read()
        end = take(self.buffer) or len(self.buffer)
        line = bytes(self.buffer[:end])
        del self.buffer[:end]
        return line

    def reply(self, exp):
        self.line_window = self.reply_window()
        self.deadline = time.monotonic() + self.line_window
        e = exp._get()
        if not e.codes:
            # TAKETHIS has no immediate reply; closed connections must reach EOF.
            return (self.line(), None) if e.rule == 'closed' else (b'', None)
        status = self.line()
        for _ in e.tail:
            status += self.line()
        if status.startswith(b'481') and not e.tail and 383 in e.codes:
            # H2a's conditional third SASL failure tail.
            if getattr(self, 'failed_auth', 0) == 2:
                status += self.line()
        body = None
        if status[:3].isdigit() and int(status[:3]) in e.codes and e.multiline_for(status):
            parts = []
            while True:
                row = self.line()
                parts.append(row)
                if row == b'.\r\n' or not row or self.timed_out:
                    break
            body = b''.join(parts)
        return status, body

    def tls(self):
        if isinstance(self.sock, Fake):
            self.sock.tls()
        else:
            self.sock = TLS(self.sock, self.node.tls_context(), self.timeout)

    def compress(self):
        self.enc, self.dec = zlib.compressobj(wbits=-15), zlib.decompressobj(wbits=-15)

    def half_close(self):
        try:
            if isinstance(self.sock, TLS):
                self.sock.settimeout(self.timeout)
                self.sock.close_write()
                return
            self.client_half_closed = True
            if isinstance(self.sock, Fake):
                self.sock.shutdown(socket.SHUT_WR)
            else:
                socket.socket.shutdown(self.sock, socket.SHUT_WR)
        except OSError as exc:
            if isinstance(self.sock, TLS):
                self.reset, self.eof = repr(exc), True

    def finish(self, *, half_close=True):
        if half_close:
            self.half_close()
        self.timed_out = False
        deadline = time.monotonic() + self.timeout
        self.deadline = deadline
        while not (self.eof or self.timed_out):
            if time.monotonic() >= deadline:
                self.timed_out = True
                break
            self.read()


@dataclass
class Result:
    compared: int = 0
    matches: int = 0
    rows: list = field(default_factory=list)
    commands: list = field(default_factory=list)
    exchanges: list = field(default_factory=list)
    reusable: bool = False
    wire: dict = field(default_factory=dict)
    closure: dict | None = None


def preceding_close(previous, status, body, *, eof):
    """Attribute observed EOF to its permitting response, not the next command.

    TCP EOF has no command tag. A complete, model-authorized closing reply
    followed by no octets is the evidence for this attribution. Otherwise the
    expectation for the unanswered command must judge the empty reply itself.
    Timeout, reset, and EOF obtained only after our SHUT_WR are not this evidence.
    """
    if not (eof and not status and body is None and previous):
        return None
    exp, exchange = previous
    if not exchange['status_hex'] or not exp.close_after_reply:
        return None
    exp.observe_eof()
    exchange['wire_eof'] = True
    return dict(command_index=exchange['command_index'],
                command_hex=exchange['command_hex'], rule=exchange['rule'],
                spec=exp.close_spec, evidence='reply-then-eof')


def reply_verdict(exp, status, body, *, eof=False, reset=None, timeout=False,
                  client_half_closed=False, tls=False, client_close_notify=False):
    eof = eof and not (timeout or reset)
    if reset and client_close_notify:
        return Verdict(False, 'tls-close', 'SPEC-MAP.md:E1',
                       'reset after client TLS close_notify; no orderly server TLS EOF')
    if reset and client_half_closed and tls:
        return Verdict(False, 'driver-environment', 'SPEC-MAP.md:E1',
                       'TLS incomplete-body EOF: reset after client TCP half-close')
    if exp._get().rule == 'closed' and not status and not eof:
        return Verdict(False, 'closed', exp._get().spec,
                       'expected server EOF after closing reply; no clean EOF observed')
    return exp.check(status, body, eof=eof)


def pieces(items, start, end, cut):
    if cut == 'bytewise':
        return (bytes([x]) for x in b''.join(items)[start:end])
    if cut == 'whole':
        return [b''.join(items)[start:end]]
    result, offset = [], 0
    for item in items:
        lo, hi = max(0, start - offset), min(len(item), end - offset)
        if lo < hi:
            result.append(item[lo:hi])
        offset += len(item)
    return result


def probe_verdict(c, command, status, response, evidence):
    """Check the recorded command/body phases against the same model as live I/O."""
    diagnostic = connection(c.model, 'peer', 'plain')
    initial = diagnostic.send(command)
    original = evidence.get('command_reply', {})
    initial_status = bytes.fromhex(original.get('status_hex', ''))
    initial_body = original.get('body_hex')
    initial_body = None if initial_body is None else bytes.fromhex(initial_body)
    verdict = initial.check(initial_status, initial_body)
    if not verdict.ok:
        return verdict
    initial.update(initial_status, initial_body)
    if not diagnostic.pending:
        return Verdict(False, 'TAKETHIS', initial.spec, 'probe command did not enter article mode')
    offered = diagnostic.pending[1]
    evidence['offered_id'] = (offered.decode('utf-8', 'replace')
                              if isinstance(offered, bytes) else offered)
    article = diagnostic.send_block(bytes.fromhex(evidence['body_hex']))
    verdict = reply_verdict(article, status, response, eof=evidence['wire_eof'],
                            reset=evidence['wire_reset'], timeout=evidence['wire_timeout'])
    evidence['article_verdict'] = dict(ok=verdict.ok, rule=verdict.rule, detail=verdict.detail,
                                     echo_binding='specified' if msgid(evidence['offered_id']) else 'token-or-dash')
    return verdict


def probe_takethis(wire, command, c):
    """Complete a malformed TAKETHIS diagnostic with a bounded article body."""
    body = b'\r\n.\r\n'  # Five octets; missing required article fields => 439.
    wire.timed_out = False
    wire.send([body])
    status, response = wire.reply(Expect([439], rule='TAKETHIS'))
    observation = 'awaited-body' if status else 'no-reply-after-body'
    evidence = dict(observation=observation, body_hex=body.hex(),
                    status_hex=status.hex(), body_response_hex=None if response is None else response.hex(),
                    wire_timeout=wire.timed_out, wire_eof=wire.eof,
                    wire_reset=wire.reset, initial_reply_timeout=False)
    verdict = probe_verdict(c, command, status, response, evidence)
    return status, response, verdict, evidence


def compare(items, *, seed=0, mode='reader', cut='whole', transport='plain',
            plants=(), node=None, timeout=3, takethis_probe=False):
    result = Result()
    model = fixture(node is None, node.config if node else None)
    if node:
        model.policy['tls_exporter'] = None  # exporter installation is not observable here
        if hasattr(node, 'creation_window'):
            model.policy['group_creation_window'] = node.creation_window
    c = connection(model, mode, transport)
    wire = None
    previous = None
    def observe_tls():
        # The negotiated protocol is observable; exporter installation is not.
        version = getattr(wire.sock, 'version', None)
        if version is not None:
            c.policy['tls_version'] = c.model.policy['tls_version'] = version()

    def record(command, status, body, verdict, index):
        result.exchanges.append(dict(command_index=index, command_hex=command.hex(),
            status_hex=status.hex(), body_hex=None if body is None else body.hex(),
            rule=verdict.rule, detail=verdict.detail, ok=verdict.ok,
            wire_eof=bool(wire and wire.eof),
            wire_timeout=bool(wire and wire.timed_out),
            wire_reset=wire.reset if wire else None,
            client_half_closed=bool(wire and wire.client_half_closed),
            client_close_notify=bool(wire and getattr(wire.sock, 'client_close_notify', False)),
            server_close_notify=bool(wire and getattr(wire.sock, 'server_close_notify', False))))
        result.compared += int(index >= 0)
        if verdict.ok:
            result.matches += int(index >= 0)
        else:
            result.rows.append(dict(seed=seed, mode=mode, cut=cut, transport=transport,
                command_index=index, command_hex=command.hex(),
                reply_hex=(status + (body or b''))[:1024].hex(), rule=verdict.rule,
                spec=verdict.spec, detail=verdict.detail, **{'class': 'unclassified'}))
    try:
        sock = Fake(mode, transport, plants) if node is None else socket.create_connection(
            ('127.0.0.1', node.tls_port if transport == 'implicit' else node.port),
            timeout=timeout, source_address=(c.address, 0))
        wire = Wire(sock, node, timeout)
        if node:
            sock.settimeout(timeout)
            if getattr(sock, 'family', socket.AF_INET) in (socket.AF_INET, socket.AF_INET6):
                sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            if transport == 'implicit':
                if isinstance(sock, Fake):
                    wire.sock = node.tls_context().wrap_socket(sock, server_hostname='localhost')
                else:
                    wire.tls()
                observe_tls()
        def exchange(command, exp, index):
            nonlocal previous
            wire.failed_auth = c.failed_auth_count
            status, body = wire.reply(exp)
            if (takethis_probe and not status and not wire.eof
                    and command.split() and command.split()[0].upper() == b'TAKETHIS'
                    and getattr(exp._get(), 'malformed_takethis', False)):
                original = exp.check(status, body)
                command_reply = dict(status_hex=status.hex(), body_hex=None if body is None else body.hex())
                status, body, verdict, evidence = probe_takethis(wire, command, c)
                evidence['command_verdict'] = dict(ok=original.ok, rule=original.rule, detail=original.detail)
                evidence['command_reply'] = command_reply
                record(command, status, body, verdict, index)
                result.exchanges[-1]['takethis_probe'] = evidence
                if result.rows:
                    result.rows[-1]['takethis_probe'] = evidence
                return False
            clean_eof = wire.eof and not (wire.timed_out or wire.reset)
            closure = preceding_close(previous, status, body,
                                      eof=clean_eof and not wire.client_half_closed)
            if closure:
                result.closure = dict(closure, observed_at_index=index)
                # The command was sent in the pipeline, but never answered or
                # consumed. It is not a separate failed comparison.
                return False
            v = reply_verdict(exp, status, body, eof=clean_eof,
                              reset=wire.reset, timeout=wire.timed_out,
                              client_half_closed=wire.client_half_closed,
                              tls=c.tls, client_close_notify=getattr(wire.sock, 'client_close_notify', False))
            if v.ok:
                try:
                    exp.update(status, body, eof=clean_eof)
                except ValueError as exc:
                    v = Verdict(False, 'driver-environment', 'SPEC-MAP.md:E1-E6',
                                'environment-update: ' + str(exc))
            record(command, status, body, v, index)
            previous = exp, result.exchanges[-1]
            if not v.ok:
                return False
            if clean_eof:
                result.closure = dict(command_index=index, command_hex=command.hex(),
                    rule=v.rule, spec=exp.close_spec or v.spec,
                    evidence='reply-then-eof' if status else 'eof-without-reply',
                    observed_at_index=index)
                return False
            if status.startswith(b'382'):
                wire.tls()
                c.tls_established()
                observe_tls()
            if status.startswith(b'206'):
                wire.compress()
            return True
        if not exchange(b'', c.greeting(), -1):
            return result
        if transport == 'starttls':
            wire.send([b'STARTTLS\r\n'])
            if not exchange(b'STARTTLS\r\n', c.send(b'STARTTLS\r\n'), -1):
                return result
        data, at, index = b''.join(items), 0, 0
        while at < len(data):
            batch, end = [], at
            # Queue ordinary commands together; resolve replies in order.
            while end < len(data):
                n = take(data[end:], bool(c.pending))
                if not n:
                    break
                cmd = data[end:end + n]
                verb = cmd.split(None, 1)[0].upper() if cmd.split() else b''
                if batch and verb in BARRIERS:
                    break
                batch.append((cmd, c.send_block(cmd) if c.pending else c.send(cmd)))
                end += n
                if c.pending or verb in BARRIERS or c.sasl:
                    break
            if not batch:
                wire.send(pieces(items, at, len(data), cut))
                result.commands.append(data[at:])
                if c.pending:
                    # EOF is an article framing event, not unsolicited output.
                    # Check the model's incomplete-body refusal before draining.
                    wire.half_close()
                    exchange(data[at:], c.send_block(data[at:]), index)
                break
            wire.send(pieces(items, at, end, cut))
            for cmd, exp in batch:
                result.commands.append(cmd)
                if not exchange(cmd, exp, index):
                    return result
                index += 1
            at = end
        else:
            if c.pending:
                wire.half_close()
                exchange(b'', c.send_block(b''), index)
    except (OSError, ValueError, RuntimeError, zlib.error) as exc:
        record(b'', b'', None, Verdict(False, 'driver-environment',
               'SPEC-MAP.md:E1-E6', repr(exc)), len(result.commands))
    finally:
        if wire:
            try:
                reply_eof, reply_timeout, reply_reset = wire.eof, wire.timed_out, wire.reset
                reply_client_half_closed = wire.client_half_closed
                # QUIT and the third auth failure owe server EOF independently
                # of a client SHUT_WR. Do not make a missing close look valid.
                wire.finish(half_close=not c.quit)
                session = dict(received=bytes(wire.received), eof=wire.eof, reset=wire.reset,
                               timeout=wire.timed_out, connect_error=None, elapsed=timeout)
                owner = node or type('Alive', (), {'alive': lambda self: True})()
                # XFNCATCHUP's 291 is one multi-line response (specs/peering.md:381); fn1's fuzzer never sent
                # XFNCATCHUP, so its shape table lacks it (H7c: the feed focus does send it).
                with patch.object(fz, 'MULTILINE', fz.MULTILINE | {291}):
                    fault = fz.node_verdict(owner, session, False)  # EOF bound also on TLS.
                if wire.reset and getattr(wire.sock, 'client_close_notify', False):
                    fault = ('tls-close', 'reset after client TLS close_notify; no orderly server TLS EOF')
                if c.quit and wire.timed_out:
                    fault = ('hang', 'missing required server EOF after closing reply')
                if fault or wire.buffer:
                    detail = ': '.join(fault) if fault else 'unconsumed reply octets after transcript'
                    if result.rows:
                        result.rows[0]['liveness'] = detail
                    else:
                        record(b'', bytes(wire.buffer), None, Verdict(False,
                               'tls-close' if fault and fault[0] == 'tls-close' else 'liveness',
                               'RFC 3977 §§3.1,5.1,5.4; specs/nntp.md:521-528', detail), len(result.commands))
                result.reusable = (wire.eof and not wire.reset and not (reply_timeout or wire.timed_out)
                                   and not wire.buffer and read_only(items)
                                   and not any(r['rule'] == 'driver-environment' for r in result.rows))
                result.wire = dict(received_hex=bytes(wire.received).hex(),
                                   unconsumed_hex=bytes(wire.buffer).hex(), eof=wire.eof,
                                   timeout=reply_timeout or wire.timed_out, reset=wire.reset,
                                   reply_eof=reply_eof, reply_timeout=reply_timeout, reply_reset=reply_reset,
                                   reply_client_half_closed=reply_client_half_closed,
                                   client_close_notify=getattr(wire.sock, 'client_close_notify', False),
                                   server_close_notify=getattr(wire.sock, 'server_close_notify', False),
                                   tls_version=c.policy.get('tls_version'),
                                   group_creation_window=c.policy.get('group_creation_window'))
                for row in result.rows:
                    row['wire_eof'] = wire.eof
                    row['wire_timeout'] = reply_timeout or wire.timed_out
                    row['wire_reset'] = wire.reset
            finally:
                wire.sock.close()
    return result


@contextmanager
def owner(image, directory, ports=None):
    """Reuse Node verbatim; journal every child PID before its caller can wait."""
    directory.mkdir(parents=True, exist_ok=True)
    popen = subprocess.Popen
    def recorded(*args, **kwargs):
        child = popen(*args, **kwargs)
        (directory / f'child-{child.pid}.pid').write_text(str(child.pid) + '\n')
        return child
    node = fz.Node.__new__(fz.Node)
    # The node's control socket is <its directory>/store/control.sock, and fn1 refuses a socket path
    # past 103 octets (CONTROL-PATH-TOO-LONG): a deep --out (a surface run's OUT/<family>/fuzz) puts the
    # node in a short scratch directory instead, linked from DIRECTORY (H7c).
    root, scratch = directory, None
    if len(str(directory / 'store' / 'control.sock')) > 100:
        scratch = Path(tempfile.mkdtemp(prefix='fn2d-'))
        root = scratch / 'n'
        (directory / 'node').symlink_to(root)
    try:
        before = int(time.time())
        with ExitStack() as setup:
            setup.enter_context(patch.object(fz.subprocess, 'Popen', recorded))
            if ports:
                setup.enter_context(patch.object(fz, 'free_port', ports))
            node.__init__(image, root)
        node.creation_window = (before, int(time.time()))
        if not node.login_ok:
            raise RuntimeError('Node login setup failed: ' + node.login_detail)
        yield node
    finally:
        if hasattr(node, 'process'):
            node.stop()
        if scratch is not None:
            shutil.rmtree(scratch, ignore_errors=True)   # this run's own scratch node, after its stop


def read_only(items):
    """Conservative reuse: exclude any possible ingestion/auth/reservation token.

    Inspect the entire transcript, including unsent/uncompared pipelined suffixes.
    A false positive costs a restart; no acceptance/refusal inference is needed.
    Auth/redeem and CHECK are excluded for owner-level counters/reservations.
    Every compare opens a new socket and constructs a fresh fixture/model/pin;
    no session-local GROUP, TLS, compression or cursor state crosses candidates.
    """
    return re.search(rb'POST|IHAVE|TAKETHIS|AUTHINFO|XREDEEM|CHECK|XFN',
                     b''.join(items).upper()) is None


class Ports:
    """Fresh ports per attempt, optionally confined to a shard's disjoint range.

    A bind probe cannot reserve across Node's bind. SessionRunner retries that
    residual EADDRINUSE race once, constructing a new scratch Node and ports.
    """
    def __init__(self, low=None, high=None):
        self.low, self.high, self.next = low, high, low
        self.seen = set()

    def __call__(self):
        for _ in range(100 if self.low is None else self.high - self.low + 1):
            with socket.socket() as probe:
                port = 0 if self.low is None else self.next
                if self.low is not None:
                    self.next = self.low if self.next == self.high else self.next + 1
                try:
                    probe.bind(('127.0.0.1', port))
                except OSError:
                    continue
                port = probe.getsockname()[1]
                if port not in self.seen:
                    self.seen.add(port)
                    return port
        raise OSError('no unused port available in shard allocation')


class SessionRunner:
    """Own a Node for one (seed, mode), including its cuts and ddmin runs."""
    def __init__(self, image, directory, plants=(), ports=None):
        self.image, self.directory, self.plants = image, directory, plants
        self.ports = ports or Ports()
        self.serial = 0
        self.stack, self.node = ExitStack(), None

    def close(self):
        self.node = None
        self.stack.close()
        self.stack = ExitStack()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def __call__(self, items, **kw):
        if self.image is None:
            return compare(items, plants=self.plants, **kw)
        diagnostics, last_error = [], None
        def environment(exc, attempt):
            return dict(seed=kw.get('seed', 0), mode=kw.get('mode', 'reader'),
                        cut=kw.get('cut', 'whole'), transport=kw.get('transport', 'plain'),
                        command_index=-1, command_hex='', reply_hex='',
                        rule='driver-environment', spec='SPEC-MAP.md:E1-E6',
                        detail=f'setup attempt {attempt}: {exc!r}',
                        retry_attempt=attempt, recovered=False, **{'class': 'driver-environment'})
        if not read_only(items):
            self.close()
        try:
            if self.node is None:
                for attempt in range(2):
                    self.serial += 1
                    try:
                        self.node = self.stack.enter_context(owner(
                            self.image, self.directory / f'owner-{self.serial:06d}', self.ports))
                        break
                    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
                        last_error = exc
                        diagnostics.append(environment(exc, attempt + 1))
                        self.close()
                        collision = (getattr(exc, 'errno', None) == 98 or
                                     'EADDRINUSE' in str(exc) or
                                     'address already in use' in str(exc).lower())
                        if attempt or not collision:
                            raise
            result = compare(items, node=self.node, **kw)
            for row in diagnostics:
                row['recovered'] = True
                row['detail'] += '; recovered by fresh-port retry'
            result.rows.extend(diagnostics)
            if not result.reusable:
                self.close()
            return result
        except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
            self.close()
            if exc is not last_error:
                diagnostics.append(environment(exc, 1))
            return Result(rows=diagnostics)


def minimize(items, failing, run, seconds=30):
    # Preserve body exchanges as single commands; never split an article into headers.
    deadline = time.monotonic() + seconds
    if seconds <= 0:
        return list(items)
    initial = run(items)
    units = initial.commands or list(items)
    key = failing['rule']
    def predicate(xs):
        # An in-flight session may finish after its budget; never start another.
        return time.monotonic() < deadline and any(
            r['rule'] == key and r['detail'] == failing['detail'] for r in run(xs).rows)
    if not predicate(units):
        units = list(items)
    return fz.ddmin(units, predicate, deadline)


def replay_fixture(path, **kwargs):
    record = json.loads(Path(path).read_text())
    chunks = record.get('minimized_hex') or record.get('chunks_hex')
    if chunks is None:
        return dict(file=Path(path).name, verdict='unsupported-' + record['campaign'],
                    detail='No NNTP command transcript; requires disk or streaming-budget oracle.')
    options = dict(seed=record.get('seed', 0), mode=record.get('role', 'reader'),
                   cut=record.get('cut', 'whole'), plants=record.get('plants', ()),
                   takethis_probe=bool(record.get('takethis_probe')),
                   transport=record.get('transport', 'implicit' if record.get('tls') else 'plain'))
    options.update(kwargs)
    result = compare([bytes.fromhex(x) for x in chunks], **options)
    return dict(file=Path(path).name, verdict='mismatch' if result.rows else 'match',
                compared=result.compared, rows=result.rows)


def replay_recorded(source):
    """Judge original recorded exchanges, without starting or simulating a Node.

    Older H2c records have reply-phase wire evidence only at the final exchange;
    final drain EOF is deliberately ignored. Stop at the first remaining
    mismatch, because its state transition cannot legitimately be committed.
    Drain bytes after that diagnostic are preserved in the source but cannot
    be called unsolicited: commands already sent in its batch may own them.
    """
    record = json.loads(Path(source).read_text()) if isinstance(source, (str, Path)) else source
    model = fixture(False)
    evidence = record.get('wire', {})
    model.policy['tls_exporter'] = None
    for key in ('tls_version', 'group_creation_window'):
        if evidence.get(key) is not None:
            model.policy[key] = evidence[key]
    c = connection(model, record.get('mode', record.get('role', 'reader')),
                   record.get('transport', 'implicit' if record.get('tls') else 'plain'))
    result = dict(matched=True, rows=[], exchanges=[], closure=None,
                  original_rule=record.get('rule'), original_detail=record.get('detail'))
    previous = None
    original = record.get('exchanges', [])
    if not original:
        result['matched'] = False
        result['rows'].append(dict(rule='driver-environment', spec='SPEC-MAP.md:E1-E6',
                                   detail='recorded session has no exchanges'))
        return result
    for position, old in enumerate(original):
        cmd = bytes.fromhex(old['command_hex'])
        status = bytes.fromhex(old['status_hex'])
        body = None if old['body_hex'] is None else bytes.fromhex(old['body_hex'])
        last = position == len(original) - 1
        pending = bool(c.pending)
        exp = c.greeting() if not cmd and old['command_index'] == -1 else (
            c.send_block(cmd) if pending else c.send(cmd))
        if 'takethis_probe' in old:
            probe = dict(old['takethis_probe'])
            verdict = probe_verdict(c, cmd, status, body, probe)
            exchange = dict(old, ok=verdict.ok, rule=verdict.rule, detail=verdict.detail,
                            takethis_probe=probe)
            result['exchanges'].append(exchange)
            result['matched'] = verdict.ok
            if not verdict.ok:
                result['rows'].append(dict(exchange, spec=verdict.spec))
            break  # Live probe also ends the session without a speculative update.
        eof = old.get('wire_eof', evidence.get('reply_eof', False) if last else False)
        timeout = old.get('wire_timeout', evidence.get('reply_timeout', False) if last else False)
        reset = old.get('wire_reset', evidence.get('reply_reset') if last else None)
        # The live driver half-closes only when an article terminator is absent.
        half_closed = old.get('client_half_closed',
                              last and pending and not take(cmd, True))
        clean_eof = eof and not (timeout or reset)
        closure = preceding_close(previous, status, body,
                                  eof=clean_eof and not half_closed)
        if closure:
            result['closure'] = dict(closure, observed_at_index=old['command_index'])
            break
        try:
            verdict = reply_verdict(exp, status, body, eof=clean_eof, reset=reset,
                                    timeout=timeout, client_half_closed=half_closed, tls=c.tls,
                                    client_close_notify=old.get('client_close_notify', False))
            if verdict.ok:
                exp.update(status, body, eof=clean_eof)
        except (ValueError, RuntimeError) as exc:
            verdict = Verdict(False, 'driver-environment', 'SPEC-MAP.md:E1-E6',
                              'environment-update: ' + str(exc))
        exchange = dict(old, rule=verdict.rule, detail=verdict.detail, ok=verdict.ok,
                        wire_eof=eof, wire_timeout=timeout, wire_reset=reset,
                        client_half_closed=half_closed)
        result['exchanges'].append(exchange)
        if not verdict.ok:
            result['matched'] = False
            result['rows'].append(dict(exchange, spec=verdict.spec))
            break
        previous = exp, exchange
        if clean_eof:
            result['closure'] = dict(command_index=old['command_index'], command_hex=cmd.hex(),
                rule=verdict.rule, spec=exp.close_spec or verdict.spec,
                evidence='reply-then-eof' if status else 'eof-without-reply',
                observed_at_index=old['command_index'])
            break
        if status.startswith(b'382'):
            c.tls_established()
    return result


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--target', choices=('fn1', 'fake'), required=True)
    p.add_argument('--seeds', default='0..199')
    p.add_argument('--mode', default='reader,node,peer')
    p.add_argument('--steps', type=int, default=20)
    p.add_argument('--focus', choices=FocusGen.FOCUS, help='narrow the generator to one family (tls_auth: auth, peering: feed)')
    p.add_argument('--cuts', default=','.join(CUTS))
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--pid-file', type=Path)
    p.add_argument('--image', type=Path)
    p.add_argument('--plant', default='')
    p.add_argument('--seconds', type=float, default=float('inf'))
    p.add_argument('--minimize-seconds', type=float, default=30)
    p.add_argument('--port-range', help='inclusive LOW..HIGH, disjoint for each shard')
    p.add_argument('--takethis-probe', action='store_true',
                   help='probe malformed TAKETHIS timeouts with a bounded article body')
    args = p.parse_args(argv)
    modes, cuts, plants = args.mode.split(','), args.cuts.split(','), tuple(filter(None, args.plant.split(',')))
    if set(modes) - {'reader', 'node', 'peer'} or set(cuts) - set(CUTS) or set(plants) - set(PLANTS):
        p.error('unknown mode, cut or plant')
    if args.target == 'fn1' and plants:
        p.error('plants require --target fake')
    try:
        start, end = map(int, args.seeds.split('..'))
    except ValueError:
        p.error('--seeds must be inclusive A..B')
    if end < start or args.steps < 1 or args.seconds <= 0 or args.minimize_seconds < 0:
        p.error('require A <= B, steps >= 1, seconds > 0 and minimize-seconds >= 0')
    ports = Ports()
    if args.port_range:
        try:
            low, high = map(int, args.port_range.split('..'))
            if not 1024 <= low < high <= 65535:
                raise ValueError
            ports = Ports(low, high)
        except ValueError:
            p.error('--port-range requires 1024 <= LOW < HIGH <= 65535')
    args.out.mkdir(parents=True, exist_ok=True)
    (args.pid_file or args.out / 'run.pid').write_text(str(os.getpid()) + '\n')
    image = args.image or Path(os.environ.get('FN_NATIVE_HOST', '/nonexistent/FN_NATIVE_HOST'))
    if args.target == 'fn1' and not image.is_file():
        p.error('fn1 requires --image or FN_NATIVE_HOST; this driver never builds an image')
    stats = dict(seeds_run=0, sessions=0, commands_compared=0, matches=0,
                 mismatches={}, minimized_reproducers=0, target=args.target,
                 seed_range=args.seeds, modes=modes, cuts=cuts, steps=args.steps, focus=args.focus,
                 takethis_probe=args.takethis_probe)
    counts, deadline = Counter(), time.monotonic() + args.seconds
    def dump():
        stats['mismatches'] = dict(counts)
        (args.out / 'summary.json').write_text(json.dumps(stats, indent=2) + '\n')
    old = signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    try:
        for seed in range(start, end + 1):
            if time.monotonic() >= deadline:
                break
            stats['seeds_run'] += 1
            for mode in modes:
                if time.monotonic() >= deadline:
                    break
                items = generator(seed, mode, args.focus).transcript(args.steps)
                transport = ('plain', 'starttls', 'implicit')[seed % 3]
                with SessionRunner(image if args.target == 'fn1' else None,
                                   args.out / f'seed-{seed}-{mode}', plants, ports) as run:
                    for cut in cuts:
                        if time.monotonic() >= deadline:
                            break
                        kw = dict(seed=seed, mode=mode, cut=cut, transport=transport,
                                  takethis_probe=args.takethis_probe)
                        result = run(items, **kw)
                        stats['sessions'] += 1
                        stats['commands_compared'] += result.compared
                        stats['matches'] += result.matches
                        for row in result.rows:
                            counts[row['rule'] + '/' + row['class']] += 1
                            reduced, reduced_result = list(items), result
                            remaining = min(args.minimize_seconds, deadline - time.monotonic())
                            if row['rule'] != 'driver-environment' and remaining > 0:
                                candidate = minimize(items, row, lambda xs: run(xs, **kw), remaining)
                                if time.monotonic() < deadline:
                                    reduced = candidate
                                    reduced_result = run(reduced, **kw)
                            # Keep original evidence when time runs out. Labeling a
                            # candidate with the original exchange would forge a replay.
                            name = f"repro-{seed}-{mode}-{cut}-{stats['minimized_reproducers']:05d}.json"
                            repro = dict(row, campaign='node', role=mode, tls=transport == 'implicit',
                                         node_tls=True, plants=plants, target=args.target,
                                         chunks_hex=[x.hex() for x in items],
                                         exchanges=result.exchanges, wire=result.wire,
                                         closure=result.closure,
                                         minimized_exchanges=reduced_result.exchanges,
                                         minimized_rows=reduced_result.rows,
                                         minimized_wire=reduced_result.wire,
                                         minimized_closure=reduced_result.closure,
                                         minimized_commands_hex=[x.hex() for x in reduced],
                                         minimized_hex=[x.hex() for x in pieces(
                                             reduced, 0, sum(map(len, reduced)), cut)])
                            (args.out / name).write_text(json.dumps(repro, indent=2) + '\n')
                            row['reproducer'] = name
                            with (args.out / 'differences.jsonl').open('a') as out:
                                out.write(json.dumps(row) + '\n')
                            stats['minimized_reproducers'] += 1
                        dump()
            print(json.dumps(stats), flush=True)
    except KeyboardInterrupt:
        stats['interrupted'] = True
    except (OSError, RuntimeError) as exc:
        stats['setup_error'] = repr(exc)
    finally:
        stats['budget_exhausted'] = time.monotonic() >= deadline
        signal.signal(signal.SIGTERM, old)
        dump()
    return int(bool(counts) or bool(stats.get('setup_error')) or stats.get('interrupted', False))


if __name__ == '__main__':
    raise SystemExit(main())
