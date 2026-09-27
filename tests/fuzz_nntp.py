#!/usr/bin/env python3
"""An adversarial NNTP and store-input fuzzer for the native image.

tests/test_native_served_differential.py compares the served bytes to the
ACL2 model on seven fixed transcripts.  This drives a live image with random
and adversarial sessions from a seeded generator (no third-party library;
every case is reproducible from its seed) and checks:

  diff   the developer image's diagnostic listener (`--fn reader 0 0 STORE|-`)
         against the model (`--fn model CHUNKS STORE|-`, one `fn-served-open'
         and one `fn-served-run' over the chunk list): the served bytes equal
         the model's for the same transcript, whatever the cut.  One model
         run per transcript; the socket side serves it under several cuts
         (whole, per item, bytewise, random, and every single cut for a
         short transcript), each of which must equal that one model reply.
  node   a production owner (`--fn operator CONFIG run`) with a login, a
         source-address peer, the STARTTLS pair and an implicit-TLS port:
         random reader, poster and peer sessions (POST, IHAVE, CHECK,
         TAKETHIS, MODE STREAM, AUTHINFO), plain and TLS.  No model covers
         the owner's store-changing path here, so the checks are the shape
         and liveness ones: the node never exits, every session gets a
         greeting and is closed within a bound after the client's EOF, every
         reply line has a code, multi-line blocks are dot-stuffed and
         terminated, and the owner's RSS stays flat over many sessions.
  bounds work bounded before it is consumed: an endless line, an endless
         header and an endless article body streamed at both servers while
         their RSS is sampled.
  store  the store's input paths: mutated export archives through `store
         import', torn tails and garbage in the store's files through
         `store status' / `recover' / the reader.  Every refusal names its
         reason (exit 1 or 3 with a stderr line), nothing crashes (no fault
         exit, no signal, no debugger), and a store that still opens serves
         each article byte-identical to the original or not at all.

Every failure is minimized (ddmin over the transcript's items, then over
octets) and written as a JSON reproducer; tests/test_native_fuzz_nntp.py
replays the committed ones in tests/fixtures/fuzz-nntp/.

    python3 tests/fuzz_nntp.py diff  --seconds 1800 --seed 1 --out DIR
    python3 tests/fuzz_nntp.py node  --seconds 1800 --sessions 10000 --out DIR
    python3 tests/fuzz_nntp.py bounds --out DIR
    python3 tests/fuzz_nntp.py store --seconds 1800 --out DIR
    python3 tests/fuzz_nntp.py replay FILE.json

Images: FN_NATIVE_DEVELOPER_HOST (diff, store) and FN_NATIVE_HOST (node,
bounds; the developer image serves when it is unset).  Run on hbox through
tools/fuzz_nntp_hbox.sh, which bounds memory with systemd-run.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import random
import re
import select
import shutil
import socket
import ssl
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Images and processes


def developer_image():
    return Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


def production_image():
    named = os.environ.get("FN_NATIVE_HOST")
    return Path(named) if named else developer_image()


def image_environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    for name in list(env):
        if name.startswith(("FN_NATIVE_OWNER_TEST", "FN_NATIVE_CONTROL_TEST",
                            "FN_NATIVE_POST_FAULT", "FN_NATIVE_CONTROL_FAULT",
                            "FN_NATIVE_FEED_TEST", "FN_NATIVE_INIT_FAULT")):
            env.pop(name)
    env.pop("FN_HOST", None)
    return env


def run_image(image, words, timeout=300, stdin=None):
    return subprocess.run([str(image), "--fn"] + [str(w) for w in words], cwd=ROOT,
                          env=image_environment(), input=stdin, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=False)


def process_tree_rss_kib(pid):
    """VmRSS of PID and every descendant, in KiB (Linux /proc); None elsewhere."""
    proc = Path("/proc")
    if not proc.is_dir():
        return None
    children = {}
    for entry in proc.iterdir():
        if not entry.name.isdigit():
            continue
        try:
            stat = (entry / "stat").read_text()
        except OSError:
            continue
        ppid = int(stat.rsplit(")", 1)[1].split()[1])
        children.setdefault(ppid, []).append(int(entry.name))
    total, todo = 0, [pid]
    while todo:
        current = todo.pop()
        try:
            for line in (proc / str(current) / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    total += int(line.split()[1])
        except OSError:
            pass
        todo.extend(children.get(current, ()))
    return total


def read_announcement(process, prefix, timeout=180):
    """Read startup lines from the descriptor until one starts with PREFIX
    (or with any of PREFIX, a tuple).  os.read, never the buffered reader:
    select cannot see a second line Python already buffered.  Lines after
    the match are kept on the process for the next call."""
    deadline = time.monotonic() + timeout
    buffered = getattr(process, "_fz_pending", b"")
    seen = b""
    fd = process.stdout.fileno()
    while True:
        while b"\n" in buffered:
            line, buffered = buffered.split(b"\n", 1)
            line += b"\n"
            seen += line
            if line.startswith(prefix):
                process._fz_pending = buffered
                return line, seen
        left = deadline - time.monotonic()
        if left <= 0 or not select.select([fd], [], [], left)[0]:
            break
        chunk = os.read(fd, 4096)
        if not chunk:
            break
        buffered += chunk
    process.kill()
    err = process.stderr.read()[-4000:] if process.stderr else b""
    raise RuntimeError("no {!r} announcement: stdout={!r} stderr={!r}".format(prefix, seen, err))


class StderrDrain(threading.Thread):
    """Keep a long-lived server's stderr drained and its last lines."""

    def __init__(self, stream):
        super().__init__(daemon=True)
        self.stream = stream
        self.lines = []
        self.count = 0

    def run(self):
        for line in iter(self.stream.readline, b""):
            self.count += 1
            self.lines.append(line)
            del self.lines[:-200]


# ---------------------------------------------------------------------------
# The generator.  A transcript is a list of ITEMS (octet strings); the
# minimizer removes items, then octets.

CRLF = b"\r\n"
PRESENT_IDS = [b"<reader@example.invalid>"]
GROUPS = [b"fn.letters", b"fn.test", b"fn.nowhere", b"fn", b"fn.", b".fn", b"FN.LETTERS",
          b"fn..letters", b"fn.\xc3\xb1", b"fn.\xff", b"a" * 300, b"fn.letters\x00x",
          b"fn.letters.sub", b"*", b"control.cancel", b"junk"]
WILDMATS = [b"*", b"fn.*", b"fn.\xc3\xb1*", b"!fn.*", b"fn.*,!fn.test", b"?", b"[", b"\\",
            b"fn.[a-z]*", b"*" * 600, b",", b"fn.*,,", b"\xc3", b"fn.letters"]
RANGES = [b"1", b"1-", b"1-1", b"0", b"0-0", b"2-1", b"-1", b"1--2", b"99999999999999999999",
          b"1-99999999999999999999", b"18446744073709551616", b"2147483648", b"a", b"",
          b"1-2-3", b" 1", b"01", b"1-0x2", b"4294967296-"]
MALFORMED_IDS = [b"<>", b"<a>", b"no-brackets", b"<a b@c>", b"<a@b", b"a@b>", b"<<a@b>>",
                 b"<a\x00@b>", b"<a@b>junk", b"<" + b"x" * 260 + b"@example.invalid>",
                 b"<" + b"x" * 5000 + b"@x>", b"<\xc3\xa9@example.invalid>", b"<@>",
                 b"<a@b@c>", b"<a>@b>", b"<a\t@b>", b"<a@[127.0.0.1]>", b"<a@b\r>",
                 b"<.a@b>", b"<a..b@c>", b"<a@b.>"]
DATES = [(b"20260101", b"000000"), (b"260101", b"000000"), (b"19700101", b"000000"),
         (b"99991231", b"235959"), (b"20261340", b"256161"), (b"2026010", b"00000"),
         (b"abcdefgh", b"000000"), (b"00000000", b"000000"), (b"20260229", b"120000"),
         (b"-2026010", b"000000")]
HEADER_NAMES = [b"Subject", b"From", b"Newsgroups", b"Message-ID", b"Path", b"Date",
                b"References", b"Xref", b"Lines", b"Bytes", b"Control", b"Approved",
                b"Supersedes", b"Distribution", b"Expires", b"Followup-To", b"Organization",
                b"Injection-Info", b"Injection-Date", b"X-Fuzz", b"Keywords", b"Summary"]


class Gen:
    """A seeded generator of adversarial NNTP transcripts."""

    def __init__(self, seed, mode, ids=None):
        self.rng = random.Random(seed)
        self.mode = mode  # "reader", "node" or "peer"
        self.ids = list(ids or PRESENT_IDS)
        self.fresh = 0
        self.seed = seed

    def choice(self, seq):
        return self.rng.choice(seq)

    def chance(self, p):
        return self.rng.random() < p

    def fresh_id(self):
        self.fresh += 1
        return b"<fz%d.%d.%d@fuzz.invalid>" % (self.seed & 0xffffffff, self.fresh,
                                              self.rng.randrange(1 << 30))

    def msgid(self):
        r = self.rng.random()
        if r < 0.35:
            return self.choice(self.ids)
        if r < 0.65:
            return self.fresh_id()
        return self.choice(MALFORMED_IDS)

    def terminator(self):
        r = self.rng.random()
        if r < 0.86:
            return CRLF
        return self.choice([b"\n", b"\r", b"\r\r\n", b"\n\r", b"", b"\r\n\r\n", b"\r\x00\n",
                            b" \r\n", b"\t\r\n"])

    def mutate_line(self, line):
        if not self.chance(0.18):
            return line
        kind = self.rng.randrange(10)
        at = self.rng.randrange(len(line) + 1)
        if kind == 0:
            return line[:at] + b"\x00" + line[at:]
        if kind == 1:
            return line[:at] + self.choice([b"\r", b"\n"]) + line[at:]
        if kind == 2:
            return line[:at] + bytes([self.rng.randrange(128, 256)]) + line[at:]
        if kind == 3:
            target = self.choice([508, 509, 510, 511, 512, 513, 1024, 4096, 70000])
            return (line + b" " + b"x" * target)[:target]
        if kind == 4:
            return line.lower() if self.chance(0.5) else line.swapcase()
        if kind == 5:
            return line.replace(b" ", self.choice([b"  ", b"\t", b" \t "]))
        if kind == 6:
            return self.choice([b" ", b"\t"]) + line
        if kind == 7:
            return line + self.choice([b" ", b"\t", b"  "])
        if kind == 8:
            return line[:at]
        return line + b" " + self.choice([b"extra", b"a b c", b"\xc3\xb1", b"x" * 100])

    def command(self, words):
        return self.mutate_line(b" ".join(w for w in words)) + self.terminator()

    def article(self, message_id=None, transit=False):
        """An article (header, blank line, body, terminating dot line), with
        adversarial headers, stuffing and termination."""
        rng = self.rng
        headers = []
        mid = message_id if message_id is not None else self.fresh_id()
        if transit or self.chance(0.2):
            headers.append(b"Path: " + self.choice([b"src.example.invalid!not-for-mail",
                                                     b"not-for-mail", b"", b"a!" * 200 + b"x"]))
        if transit or self.chance(0.3):
            headers.append(b"Date: " + self.choice([b"Mon, 21 Sep 2026 12:00:00 +0000",
                                                     b"garbage", b"", b"Mon, 31 Feb 2026 12:00:00 +0000"]))
        base = [(b"From", self.choice([b"author@example.invalid", b"", b"<>", b"\xc3\xa9 <a@b>"])),
                (b"Newsgroups", self.choice([b"fn.test", b"fn.letters", b"fn.test,fn.letters",
                                             b"fn.nowhere", b"", b"fn.test,fn.test", b" fn.test",
                                             b"fn.test,", b"fn.*"])),
                (b"Subject", self.choice([b"fuzz", b"", b"\xff\xfe", b"s" * 998, b"s" * 5000])),
                (b"Message-ID", mid)]
        for name, value in base:
            if self.chance(0.93):
                headers.append(name + b": " + value)
        if self.chance(0.05):
            headers.append(b"Message-ID: " + self.msgid())
        extra = self.choice([0, 0, 1, 2, 5, 59, 60, 61, 64, 65, 200, 1000])
        for i in range(extra):
            headers.append(b"X-Fz-%d: %d" % (i, i))
        for _ in range(rng.randrange(3)):
            kind = rng.randrange(9)
            if kind == 0:
                headers.append(b"NoColonHere")
            elif kind == 1:
                headers.append(b": empty name")
            elif kind == 2:
                headers.append(b"X-Long: " + b"v" * self.choice([997, 998, 999, 5000, 100000]))
            elif kind == 3:
                headers.append(b"X-Folded: a\r\n\tb\r\n c")
            elif kind == 4:
                headers.append(b"X-Nul: a\x00b")
            elif kind == 5:
                headers.append(b"X-Eight: \xc3\xa9\xff")
            elif kind == 6:
                headers.append(self.choice(HEADER_NAMES) + b":" + self.choice([b"", b" ", b"x"]))
            elif kind == 7:
                headers.append(b"\tcontinuation-first")
            else:
                headers.append(b"X-Folds: x" + b"\r\n\tx" * self.choice([10, 255, 256, 300]))
        rng.shuffle(headers) if self.chance(0.1) else None
        body = []
        for _ in range(self.choice([0, 1, 2, 5, 20])):
            body.append(self.choice([b"", b"text", b".", b"..", b"...", b". ", b".x", b"x.",
                                     b"\t", b"a" * 997, b"a" * 5000, b"\x00", b"\xc3\xa9",
                                     b"a\rb", b"a\nb", b". \t"]))
        stuff = self.chance(0.85)
        lines = []
        for line in body:
            lines.append(b"." + line if stuff and line.startswith(b".") else line)
        separator = self.choice([CRLF] * 12 + [b"\n", b""])
        text = CRLF.join(headers) + CRLF + separator + CRLF.join(lines)
        if lines:
            text += CRLF
        end = self.choice([b".\r\n"] * 14 + [b"\n.\n", b".\n", b". \r\n", b"", b"..\r\n",
                                             b".\r\n.\r\n"])
        return text + end

    def step(self):
        """One or more items for one protocol step."""
        rng = self.rng
        r = rng.random()
        c = self.command
        if r < 0.04:
            return [c([b"CAPABILITIES"] + ([self.choice([b"x", b"AUTOUPDATE"])] if self.chance(0.2) else []))]
        if r < 0.08:
            return [c([b"MODE", self.choice([b"READER", b"STREAM", b"", b"reader", b"POSTER", b"X"])])]
        if r < 0.16:
            return [c([b"GROUP", self.choice(GROUPS)] + ([b"x"] if self.chance(0.05) else []))]
        if r < 0.20:
            words = [b"LISTGROUP"]
            if self.chance(0.8):
                words.append(self.choice(GROUPS))
                if self.chance(0.5):
                    words.append(self.choice(RANGES))
            return [c(words)]
        if r < 0.24:
            return [c([self.choice([b"LAST", b"NEXT"])])]
        if r < 0.36:
            verb = self.choice([b"ARTICLE", b"HEAD", b"BODY", b"STAT"])
            arg = self.rng.random()
            words = [verb]
            if arg < 0.4:
                words.append(self.msgid())
            elif arg < 0.8:
                words.append(self.choice(RANGES))
            return [c(words)]
        if r < 0.44:
            kw = self.choice([b"", b"ACTIVE", b"NEWSGROUPS", b"OVERVIEW.FMT", b"HEADERS",
                              b"ACTIVE.TIMES", b"DISTRIB.PATS", b"MOTD", b"COUNTS", b"SUBSCRIPTIONS",
                              b"HEADERS MSGID", b"HEADERS RANGE", b"X"])
            words = [b"LIST"] + ([kw] if kw else [])
            if kw and self.chance(0.5):
                words.append(self.choice(WILDMATS))
            return [c(words)]
        if r < 0.50:
            verb = self.choice([b"OVER", b"XOVER"])
            return [c([verb] + ([self.choice(RANGES + [self.msgid()])] if self.chance(0.8) else []))]
        if r < 0.55:
            verb = self.choice([b"HDR", b"XHDR"])
            words = [verb, self.choice(HEADER_NAMES + [b":bytes", b":lines", b"", b"x" * 600])]
            if self.chance(0.7):
                words.append(self.choice(RANGES + [self.msgid()]))
            return [c(words)]
        if r < 0.57:
            words = [b"XPAT", self.choice(HEADER_NAMES), self.choice(RANGES + [self.msgid()]),
                     self.choice(WILDMATS)]
            return [c(words)]
        if r < 0.61:
            d, t = self.choice(DATES)
            if self.chance(0.5):
                words = [b"NEWGROUPS", d, t]
            else:
                words = [b"NEWNEWS", self.choice(WILDMATS), d, t]
            if self.chance(0.4):
                words.append(self.choice([b"GMT", b"UTC", b"gmt", b"X"]))
            return [c(words)]
        if r < 0.63:
            return [c([self.choice([b"HELP", b"DATE"]) if self.mode != "reader" else b"HELP"])]
        if r < 0.70:
            post = c([b"POST"] + ([b"x"] if self.chance(0.05) else []))
            items = [post]
            if self.chance(0.85):
                items.append(self.article())
            return items
        if r < 0.76:
            mid = self.msgid()
            items = [c([b"IHAVE", mid])]
            if self.chance(0.8):
                items.append(self.article(mid if self.chance(0.9) else None, transit=True))
            return items
        if r < 0.80:
            return [c([b"CHECK", self.msgid()])]
        if r < 0.85:
            mid = self.msgid()
            return [c([b"TAKETHIS", mid]), self.article(mid if self.chance(0.9) else None, transit=True)]
        if r < 0.91:
            kind = self.rng.randrange(6)
            if kind == 0:
                return [c([b"AUTHINFO", b"USER", self.choice([b"fuzz", b"nobody", b"", b"u" * 600])]),
                        c([b"AUTHINFO", b"PASS", self.choice([b"fuzz-password", b"wrong", b"", b"p" * 600])])]
            if kind == 1:
                return [c([b"AUTHINFO", b"PASS", b"fuzz-password"])]
            if kind == 2:
                return [c([b"AUTHINFO", b"SASL", self.choice([b"PLAIN", b"PLAIN AGZ1enoAZnV6ei1wYXNzd29yZA==", b"X"])])]
            if kind == 3:
                return [c([b"AUTHINFO", self.choice([b"GENERIC", b"SIMPLE", b"", b"user"])])]
            if kind == 4:
                return [c([b"AUTHINFO", b"USER", b"fuzz"])]
            return [c([b"XREDEEM"] + [self.choice([b"code", b"", b"x" * 600])] * self.rng.randrange(3))]
        if r < 0.93:
            return [c([b"STARTTLS"])] if self.mode != "tls" else [c([b"HELP"])]
        if r < 0.96:
            return [c([self.choice([b"FOO", b"XYZZY", b"SLAVE", b"COMPRESS DEFLATE", b"XFEATURE COMPRESS GZIP",
                                    b"XROVER", b"XGTITLE", b"CHECK", b"IHAVE", b"TAKETHIS", b"ARTICLE <"])])]
        if r < 0.98:
            return [self.choice([CRLF, b"\n", b" \r\n", b"\x00\r\n", b"\r", b"\xff\xfe\r\n",
                                 b"\x16\x03\x01\x00\x05hello\r\n"])]
        return [self.choice([b"QUIT", b"quit", b"QUIT x"]) + self.terminator()]

    def transcript(self, max_steps=None):
        steps = self.choice([1, 1, 2, 3, 4, 6, 8, 12, 20]) if max_steps is None else max_steps
        items = []
        for _ in range(steps):
            items.extend(self.step())
        if self.chance(0.6):
            items.append(b"QUIT\r\n")
            if self.chance(0.1):
                items.append(b"STAT\r\n")
        return [item for item in items if item]

    def chunkings(self, data, budget):
        """Cut lists of DATA: whole, bytewise, random, per-position."""
        cuts = [[data]]
        if len(data) > 1 and budget > 1:
            n = len(data)
            if n <= 256:
                cuts.append([data[i:i + 1] for i in range(n)])
            for _ in range(max(0, budget - len(cuts))):
                k = self.rng.randrange(1, min(n, 12))
                points = sorted(self.rng.sample(range(1, n), k))
                pieces, last = [], 0
                for p in points:
                    pieces.append(data[last:p])
                    last = p
                pieces.append(data[last:])
                cuts.append(pieces)
        return cuts


# ---------------------------------------------------------------------------
# Reply-stream shape (RFC 3977 section 3.1 and 3.1.1)

MULTILINE = {100, 101, 215, 220, 221, 222, 224, 225, 230, 231}
STATUS = re.compile(rb"^[1-5][0-9][0-9](?: |$)")


def shape_problems(data, closed_cleanly=True):
    """Problems with a reply stream: a line without a reply code, an overlong
    status line, an unstuffed or unterminated multi-line block, a partial last
    line.  211 is multi-line only for LISTGROUP; told apart by the next line."""
    problems = []
    lines = data.split(CRLF)
    tail = lines.pop()
    i = 0
    first = True
    closed_after = None
    while i < len(lines):
        line = lines[i]
        if not STATUS.match(line):
            problems.append("line {} has no reply code: {!r}".format(i, line[:80]))
            i += 1
            continue
        if len(line) + 2 > 512:
            problems.append("status line {} is {} octets".format(i, len(line) + 2))
        if first and not line[:3] in (b"200", b"201", b"400", b"502"):
            problems.append("greeting is {!r}".format(line[:80]))
        first = False
        code = int(line[:3])
        if closed_after is not None:
            problems.append("reply after 205 (RFC 3977 5.4): {!r}".format(line[:60]))
        if code == 205:
            closed_after = i
        if code == 382:
            # RFC 4642 2.2.2: the TLS handshake starts after this CRLF; what
            # follows is TLS records (an alert, for a client that sent
            # plaintext), not NNTP.
            return problems
        multi = code in MULTILINE
        if code == 211 and i + 1 < len(lines) and not STATUS.match(lines[i + 1]):
            multi = True
        i += 1
        if multi:
            while i < len(lines) and lines[i] != b".":
                body = lines[i]
                if body.startswith(b".") and not body.startswith(b".."):
                    problems.append("unstuffed block line {}: {!r}".format(i, body[:80]))
                if b"\r" in body or b"\n" in body:
                    problems.append("bare CR/LF inside block line {}".format(i))
                i += 1
            if i >= len(lines):
                problems.append("multi-line {} block not terminated".format(code))
            i += 1
    if tail:
        problems.append("partial last line {!r}".format(tail[:80]))
    return problems


# ---------------------------------------------------------------------------
# Sessions


class Session:
    """One client connection: send CHUNKS (optionally paced), close the
    write side, read until EOF under DEADLINE with a concurrent reader."""

    def __init__(self, host, port, chunks, gap=0.0, deadline=40.0, source=None,
                 tls_context=None, server_hostname="localhost"):
        self.host, self.port, self.chunks = host, port, chunks
        self.gap, self.deadline, self.source = gap, deadline, source
        self.tls_context = tls_context
        self.server_hostname = server_hostname

    def run(self):
        started = time.monotonic()
        result = {"received": b"", "eof": False, "reset": False, "timeout": False,
                  "send_error": None, "connect_error": None}
        try:
            raw = socket.create_connection((self.host, self.port), timeout=self.deadline,
                                           source_address=(self.source, 0) if self.source else None)
        except OSError as e:
            result["connect_error"] = repr(e)
            result["elapsed"] = time.monotonic() - started
            return result
        raw.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock = raw
        try:
            if self.tls_context is not None:
                sock = self.tls_context.wrap_socket(raw, server_hostname=self.server_hostname)
            received = []
            done = threading.Event()

            def reader():
                end = started + self.deadline
                try:
                    while True:
                        left = end - time.monotonic()
                        if left <= 0:
                            result["timeout"] = True
                            break
                        sock.settimeout(left)
                        piece = sock.recv(65536)
                        if not piece:
                            result["eof"] = True
                            break
                        received.append(piece)
                except socket.timeout:
                    result["timeout"] = True
                except (ConnectionResetError, ssl.SSLError, OSError) as e:
                    result["reset"] = repr(e)
                finally:
                    done.set()

            if self.tls_context is not None:
                # An SSL object is not safe to read and write from two
                # threads: send everything, then read (TLS transcripts are
                # kept small, so the server's replies fit its send buffer).
                try:
                    for index, chunk in enumerate(self.chunks):
                        if chunk:
                            sock.sendall(chunk)
                        if self.gap and index + 1 < len(self.chunks):
                            time.sleep(self.gap)
                    # No close_notify: the TCP half-close is the EOF the owner
                    # reads (an "unexpected eof", connection-local), so an
                    # article left open ends the session as plaintext does.
                    socket.socket.shutdown(sock, socket.SHUT_WR)
                except (OSError, ssl.SSLError) as e:
                    result["send_error"] = repr(e)
                reader()
            else:
                thread = threading.Thread(target=reader, daemon=True)
                thread.start()
                try:
                    for index, chunk in enumerate(self.chunks):
                        if chunk:
                            sock.sendall(chunk)
                        if self.gap and index + 1 < len(self.chunks):
                            time.sleep(self.gap)
                    sock.shutdown(socket.SHUT_WR)
                except (OSError, ssl.SSLError) as e:
                    result["send_error"] = repr(e)
                done.wait(self.deadline + 5)
                thread.join(5)
            result["received"] = b"".join(received)
        except (OSError, ssl.SSLError) as e:
            result["connect_error"] = repr(e)
        finally:
            try:
                sock.close()
            except OSError:
                pass
        result["elapsed"] = time.monotonic() - started
        return result


def normalize(data):
    """The one clock-dependent reply: DATE's 111 line."""
    return re.sub(rb"(?m)^111 [0-9]{14}\r$", b"111 YYYYMMDDhhmmss\r", data)


# ---------------------------------------------------------------------------
# The differential campaign


class Reader:
    """A long-lived `--fn reader 0 0 STORE|-' (serves connections one by one)."""

    def __init__(self, image, store):
        self.image, self.store = image, store
        self.start()

    def start(self):
        self.process = subprocess.Popen(
            [str(self.image), "--fn", "reader", "0", "0", str(self.store) if self.store else "-"],
            cwd=ROOT, env=image_environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        line, _ = read_announcement(self.process, b"LISTENING ")
        self.port = int(line.split()[1])
        self.stderr = StderrDrain(self.process.stderr)
        self.stderr.start()

    def alive(self):
        return self.process.poll() is None

    def rss(self):
        return process_tree_rss_kib(self.process.pid)

    def stop(self):
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        return self.process.returncode


def model_reply(image, chunks, store, timeout=300):
    with tempfile.NamedTemporaryFile(prefix="fn-fuzz-chunks-", delete=False) as handle:
        for chunk in chunks:
            handle.write(b"%d\n" % len(chunk))
            handle.write(chunk)
        path = handle.name
    try:
        result = subprocess.run([str(image), "--fn", "model", path, str(store) if store else "-"],
                                cwd=ROOT, env=image_environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=timeout, check=False)
        return result.returncode, result.stdout, result.stderr
    finally:
        os.unlink(path)


def served(reader, chunks, gap):
    session = Session("127.0.0.1", reader.port, chunks, gap=gap).run()
    return session


def line_at(data, at):
    """The line of DATA containing octet AT, or b"EOF"."""
    if at >= len(data):
        return b"EOF"
    start = data.rfind(CRLF, 0, at) + 2 if data.rfind(CRLF, 0, at) >= 0 else 0
    end = data.find(CRLF, at)
    return data[start:end if end >= 0 else len(data)]


def diff_verdict(model, session, reader):
    """(class, signature, detail) of a disagreement, or None."""
    rc, out, err = model
    if rc != 0:
        return ("model-exit", "model-exit/{}".format(rc),
                "model exited {}: {}".format(rc, err[-400:].decode("utf-8", "replace")))
    if session["connect_error"]:
        return ("connect", "connect", session["connect_error"])
    if not reader.alive():
        return ("reader-died", "reader-died/{}".format(reader.process.returncode),
                "exit {}: {}".format(reader.process.returncode, b"".join(reader.stderr.lines[-5:])))
    if session["timeout"]:
        return ("hang", "hang", "no EOF after {:.1f} s, {} octets".format(session["elapsed"], len(session["received"])))
    got = normalize(session["received"])
    want = normalize(out)
    if got != want:
        at = next((i for i in range(min(len(got), len(want))) if got[i] != want[i]), min(len(got), len(want)))
        served_line, model_line = line_at(got, at), line_at(want, at)
        after_quit = b"\r\n205 " in want[:at] or want.startswith(b"205 ")
        sig = "mismatch/model:{}/served:{}{}".format(model_line[:3].decode("ascii", "replace"),
                                                    served_line[:3].decode("ascii", "replace"),
                                                    "/after-205" if after_quit else "")
        return ("mismatch", sig, "first difference at octet {} of served {} / model {}: served {!r} model {!r}{}".format(
            at, len(got), len(want), got[max(0, at - 40):at + 60], want[max(0, at - 40):at + 60],
            " (reset {})".format(session["reset"]) if session["reset"] else ""))
    problems = shape_problems(got)
    if problems:
        return ("shape", "shape/" + re.sub(r"[0-9]+", "N", problems[0].split(":")[0]), "; ".join(problems[:4]))
    return None


def ddmin(items, still_fails, deadline):
    """Zeller's ddmin over a list, bounded by a wall-clock deadline."""
    n = 2
    while len(items) >= 2 and time.monotonic() < deadline:
        size = max(1, len(items) // n)
        subsets = [items[i:i + size] for i in range(0, len(items), size)]
        reduced = False
        for index in range(len(subsets)):
            complement = [x for j, s in enumerate(subsets) if j != index for x in s]
            if complement and still_fails(complement):
                items, n, reduced = complement, max(n - 1, 2), True
                break
            if time.monotonic() > deadline:
                break
        if not reduced:
            if n >= len(items):
                break
            n = min(len(items), n * 2)
    return items


def split_lines(items):
    """Each read cut further at its line ends, keeping the read boundaries."""
    out = []
    for item in items:
        out.extend(x for x in re.split(rb"(?<=\n)", item) if x)
    return out


def minimize_items_then_octets(items, still_fails, seconds=240):
    """ddmin over the lines (each kept as its own read), then over the octets
    of each surviving line.  The read boundaries are part of the case."""
    deadline = time.monotonic() + seconds
    items = list(items)
    lines = split_lines(items)
    if still_fails(lines):
        items = lines
    items = ddmin(items, still_fails, deadline)
    for index in range(len(items)):
        if time.monotonic() > deadline or len(items[index]) > 2048:
            continue
        octets = [bytes([b]) for b in items[index]]
        octets = ddmin(octets, lambda xs: still_fails(items[:index] + [b"".join(xs)] + items[index + 1:]), deadline)
        items[index] = b"".join(octets)
    return [x for x in items if x]


def minimize(items, still_fails, seconds=240):
    return minimize_items_then_octets(items, still_fails, seconds)


def write_reproducer(out, name, record):
    out.mkdir(parents=True, exist_ok=True)
    path = out / (name + ".json")
    path.write_text(json.dumps(record, indent=1, sort_keys=True) + "\n")
    return path


def hexs(chunks):
    return [c.hex() for c in chunks]


class Stats:
    def __init__(self, campaign, seed):
        self.data = {"campaign": campaign, "seed": seed, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                     "transcripts": 0, "sessions": 0, "octets_sent": 0, "findings": {}, "rss": []}
        self.signatures = {}

    def finding(self, cls, signature, detail, record=None):
        key = cls + ":" + signature
        entry = self.data["findings"].setdefault(key, {"class": cls, "count": 0, "detail": detail})
        entry["count"] += 1
        new = key not in self.signatures
        self.signatures.setdefault(key, record)
        return new

    def dump(self, out):
        self.data["ended"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        (out / "stats-{}.json".format(self.data["campaign"])).write_text(json.dumps(self.data, indent=1) + "\n")


def failure_signature(cls, detail):
    """Collapse a finding to its class and first problem's words."""
    return cls + "/" + re.sub(r"[0-9]+", "N", detail.split(":")[0])[:60]


def campaign_diff(args):
    image = developer_image()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    stats = Stats("diff", args.seed)
    store = args.store or None
    ids = list(PRESENT_IDS) + [i.encode() for i in args.ids]
    if args.store_articles:
        # A store-backed reader: several articles in two groups, dot lines.
        built = Path(tempfile.mkdtemp(prefix="d", dir=args.scratch))
        store, _, store_ids = build_base_store(image, built, args.store_articles)
        ids = store_ids + ids
    reader = Reader(image, store)
    deadline = time.monotonic() + args.seconds
    pool = concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs)
    seed = args.seed
    minimized = 0
    rss_first = reader.rss()
    pending = []

    def submit(case_seed):
        gen = Gen(case_seed, "reader", ids)
        items = gen.transcript()
        data = b"".join(items)
        # The model sees the same cut as one socket session, chosen at random.
        cuts = gen.chunkings(data, args.cuts)
        model_cut = gen.choice(cuts)
        return case_seed, gen, items, cuts, model_cut, pool.submit(model_reply, image, model_cut, store)

    try:
        while time.monotonic() < deadline:
            while len(pending) < args.jobs * 2:
                pending.append(submit(seed))
                seed += 1
            case_seed, gen, items, cuts, model_cut, future = pending.pop(0)
            model = future.result()
            stats.data["transcripts"] += 1
            data = b"".join(items)
            if len(data) <= args.every_cut_max:
                for p in range(1, len(data)):
                    cuts.append([data[:p], data[p:]])
            for cut in cuts:
                gap = 0.002 if len(cut) > 1 and len(cut) <= 300 else 0.0
                session = served(reader, cut, gap)
                stats.data["sessions"] += 1
                stats.data["octets_sent"] += len(data)
                verdict = diff_verdict(model, session, reader)
                if verdict is None:
                    continue
                cls, sig, detail = verdict
                record = {"campaign": "diff", "store": str(store) if store else "-", "seed": case_seed,
                          "class": cls, "detail": detail, "chunks_hex": hexs(cut),
                          "model_chunks_hex": hexs(model_cut), "gap": gap}
                if stats.finding(cls, sig, detail, record):
                    print("FINDING {} seed={} {}".format(sig, case_seed, detail[:300]), flush=True)
                    if not reader.alive():
                        reader.stop()
                        reader.start()
                    if minimized < args.minimize_max:
                        minimized += 1
                        record["minimized_hex"] = hexs(minimize_diff(image, store, reader, cut, sig))
                    write_reproducer(out, "diff-{}-{}".format(re.sub(r"[^a-z0-9]+", "-", sig.lower()), case_seed), record)
                if not reader.alive():
                    reader.stop()
                    reader.start()
                break
            if stats.data["transcripts"] % 200 == 0:
                stats.data["rss"].append([stats.data["sessions"], reader.rss()])
                print("diff: {} transcripts, {} sessions, {} findings, reader rss {} KiB".format(
                    stats.data["transcripts"], stats.data["sessions"], len(stats.data["findings"]), reader.rss()), flush=True)
                stats.dump(out)
    finally:
        pool.shutdown(wait=False, cancel_futures=True)
        stats.data["reader_rss_first_kib"] = rss_first
        stats.data["reader_rss_last_kib"] = reader.rss()
        stats.data["reader_exit"] = reader.stop()
        stats.dump(out)
    print(json.dumps({k: v for k, v in stats.data.items() if k != "rss"}, indent=1))
    return 1 if stats.data["findings"] else 0


def minimize_diff(image, store, reader, cut, sig):
    """Keep the items as reads (a cut may be the cause), same signature."""
    def still_fails(items):
        if not reader.alive():
            reader.stop()
            reader.start()
        model = model_reply(image, [b"".join(items)], store)
        verdict = diff_verdict(model, served(reader, items, 0.02 if len(items) > 1 else 0.0), reader)
        return verdict is not None and verdict[1] == sig
    return minimize_items_then_octets(cut, still_fails)


# ---------------------------------------------------------------------------
# The node campaign


class Node:
    """A production owner over a scratch store with a login, a peer (source
    address 127.0.0.1), the TLS pair and an implicit-TLS port."""

    def __init__(self, image, root, tls=True, posting=True):
        self.image, self.root = image, Path(root)
        self.store = self.root / "store"
        self.port = free_port()
        self.tls_port = free_port() if tls else None
        self.config = self.root / "fn.toml"
        self.credentials = self.root / "credentials.toml"
        self.root.mkdir(parents=True, exist_ok=True)
        init = run_image(image, ["store", self.store, "init", "fn.test", "fn.letters"])
        if init.returncode != 0:
            raise RuntimeError("init: " + init.stderr.decode("utf-8", "replace"))
        lines = ['[store]', 'path = "{}"'.format(self.store), '',
                 '[listener]', 'host = "127.0.0.1"', 'port = {}'.format(self.port)]
        self.certificate = None
        if tls:
            self.certificate = self.root / "cert.pem"
            key = self.root / "key.pem"
            subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                            "-out", str(self.certificate), "-sha256", "-days", "2", "-nodes",
                            "-subj", "/CN=localhost"], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, check=True, timeout=60)
            lines += ['tls_cert = "{}"'.format(self.certificate), 'tls_key = "{}"'.format(key),
                      'tls_port = {}'.format(self.tls_port)]
        lines += ['', '[auth]', 'required = false', 'protected_only = false',
                  'path = "{}"'.format(self.credentials), '',
                  '[posting]', 'enabled = {}'.format('true' if posting else 'false'), '']
        self.config.write_text("\n".join(lines), encoding="ascii")
        peer = run_image(image, ["operator", self.config, "peer", "add", "src", "src.example.invalid",
                                 "127.0.0.1", "1", "fn.*", "-", "source-address", "127.0.0.1", "true"])
        if peer.returncode != 0:
            raise RuntimeError("peer add: " + (peer.stdout + peer.stderr).decode("utf-8", "replace"))
        login = run_image(image, ["operator", self.config, "principal", "set-password", "fuzz", "--posting"],
                          stdin=b"fuzz-password\nfuzz-password\n")
        self.login_ok = login.returncode == 0
        self.login_detail = (login.stdout + login.stderr).decode("utf-8", "replace")[-400:]
        self.start()

    def start(self):
        self.process = subprocess.Popen([str(self.image), "--fn", "operator", str(self.config), "run"],
                                        cwd=ROOT, env=image_environment(), stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE)
        read_announcement(self.process, b"LISTENING ")
        if self.tls_port:
            read_announcement(self.process, b"LISTENING-TLS ")
        self.stderr = StderrDrain(self.process.stderr)
        self.stderr.start()
        self.stdout = StderrDrain(self.process.stdout)
        self.stdout.start()

    def alive(self):
        return self.process.poll() is None

    def rss(self):
        return process_tree_rss_kib(self.process.pid)

    def tls_context(self):
        context = ssl.create_default_context(cafile=str(self.certificate))
        context.check_hostname = True
        return context

    def stop(self):
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        return self.process.returncode


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def node_session(node, gen, role, tls, cuts_budget=2):
    items = gen.transcript()
    if tls or role == "peer" and gen.chance(0.5):
        items = items + [b"QUIT\r\n"]
    if role == "peer" and gen.chance(0.5):
        items = [b"MODE STREAM\r\n"] + items
    data = b"".join(items)
    if tls and len(data) > 48 * 1024:
        tls = False
    cut = gen.choice(gen.chunkings(data, cuts_budget))
    source = "127.0.0.1" if role == "peer" else "127.0.0.2"
    port = node.tls_port if tls else node.port
    context = node.tls_context() if tls else None
    session = Session("127.0.0.1", port, cut, gap=0.001 if 1 < len(cut) <= 64 else 0.0,
                      deadline=60.0, source=source, tls_context=context).run()
    return items, cut, session


def node_verdict(node, session, tls):
    if not node.alive():
        return ("node-died", "exit {}: {}".format(node.process.returncode,
                                                  b"".join(node.stderr.lines[-8:])[-1500:]))
    if session["connect_error"]:
        return ("connect", session["connect_error"])
    received = session["received"]
    if session["timeout"]:
        if tls:
            # A TLS client cannot half-close: QUIT closes it, an article left
            # open waits for the idle bound.  Only a missing greeting counts.
            if not received:
                return ("hang", "no greeting in {:.1f} s".format(session["elapsed"]))
        else:
            return ("hang", "no EOF {:.1f} s after the client's EOF ({} octets)".format(
                session["elapsed"], len(received)))
    if not received:
        return ("silent", "closed without a greeting (reset {})".format(session["reset"]))
    problems = shape_problems(received)
    if session["timeout"] or session["reset"]:
        problems = [p for p in problems if not p.startswith(("partial last line", "multi-line"))]
    if problems:
        return ("shape", "; ".join(problems[:4]))
    return None


def campaign_node(args):
    image = production_image()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    stats = Stats("node", args.seed)
    scratch = Path(tempfile.mkdtemp(prefix="n", dir=args.scratch))
    node = Node(image, scratch, tls=not args.no_tls)
    stats.data["login"] = [node.login_ok, node.login_detail]
    rss_start = node.rss()
    stats.data["rss"].append([0, rss_start])
    deadline = time.monotonic() + args.seconds
    seed = args.seed
    minimized = 0
    posted_ids = list(PRESENT_IDS)
    lock = threading.Lock()

    def one(case_seed):
        gen = Gen(case_seed, "node", posted_ids)
        r = gen.rng.random()
        role = "peer" if r < args.peer_share else "reader"
        tls = (not args.no_tls) and gen.chance(args.tls_share)
        if args.read_only:
            gen.mode = "reader"
            # Only commands that change no store state: RSS then measures
            # connections, not data.
            items = [s for s in gen.transcript() if not s.startswith((b"POST", b"IHAVE", b"TAKETHIS"))]
            data = b"".join(items) + b"QUIT\r\n"
            session = Session("127.0.0.1", node.port, [data], deadline=60.0, source="127.0.0.2").run()
            return case_seed, role, False, [data], [data], session
        items, cut, session = node_session(node, gen, role, tls)
        return case_seed, role, tls, items, cut, session

    pool = concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs)
    try:
        futures = []
        while time.monotonic() < deadline and (args.sessions == 0 or stats.data["sessions"] < args.sessions):
            while len(futures) < args.jobs and (args.sessions == 0 or stats.data["sessions"] + len(futures) < args.sessions):
                futures.append(pool.submit(one, seed))
                seed += 1
            if not futures:
                break
            done, _ = concurrent.futures.wait(futures, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                futures.remove(future)
                case_seed, role, tls, items, cut, session = future.result()
                stats.data["sessions"] += 1
                stats.data["octets_sent"] += sum(len(c) for c in cut)
                received = session["received"]
                for m in re.finditer(rb"(?m)^(?:240|235|239) (?:[^\r]*)?(<[^>\r ]+>)?", received):
                    pass
                verdict = node_verdict(node, session, tls)
                if verdict is not None:
                    cls, detail = verdict
                    sig = failure_signature(cls, detail) + ("/tls" if tls else "") + "/" + role
                    record = {"campaign": "node", "seed": case_seed, "role": role, "tls": tls,
                              "class": cls, "detail": detail, "chunks_hex": hexs(cut),
                              "received_tail_hex": received[-600:].hex()}
                    if stats.finding(cls, sig, detail, record):
                        print("FINDING {} seed={} {}".format(sig, case_seed, detail[:300]), flush=True)
                        path = write_reproducer(out, "node-{}-{}".format(re.sub(r"[^a-z0-9]+", "-", sig.lower()), case_seed), record)
                        if node.alive() and minimized < args.minimize_max and cls in ("shape", "hang", "silent"):
                            minimized += 1
                            record["minimized_hex"] = hexs(minimize_node(node, cut, role, tls, cls))
                            write_reproducer(out, path.stem, record)
                    if not node.alive():
                        stats.data.setdefault("restarts", []).append([stats.data["sessions"], node.process.returncode])
                        node.stop()
                        node.start()
            if stats.data["sessions"] % 500 < args.jobs:
                stats.data["rss"].append([stats.data["sessions"], node.rss()])
                print("node: {} sessions, {} findings, owner rss {} KiB".format(
                    stats.data["sessions"], len(stats.data["findings"]), node.rss()), flush=True)
                stats.dump(out)
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
        stats.data["rss"].append([stats.data["sessions"], node.rss()])
        stats.data["owner_stderr_lines"] = node.stderr.count
        stats.data["owner_stderr_tail"] = [l.decode("utf-8", "replace") for l in node.stderr.lines[-20:]]
        stats.data["owner_exit"] = node.stop()
        stats.dump(out)
        if not args.keep:
            shutil.rmtree(scratch, ignore_errors=True)
    print(json.dumps({k: v for k, v in stats.data.items() if k != "rss"}, indent=1))
    print("rss samples (sessions, KiB):", stats.data["rss"][:3], "...", stats.data["rss"][-3:])
    return 1 if stats.data["findings"] else 0


def minimize_node(node, cut, role, tls, cls):
    source = "127.0.0.1" if role == "peer" else "127.0.0.2"

    def still_fails(items):
        if not node.alive():
            return False
        port = node.tls_port if tls else node.port
        session = Session("127.0.0.1", port, items, gap=0.001 if len(items) > 1 else 0.0, deadline=60.0,
                          source=source, tls_context=node.tls_context() if tls else None).run()
        verdict = node_verdict(node, session, tls)
        return verdict is not None and verdict[0] == cls
    return minimize(cut, still_fails, seconds=90)


# ---------------------------------------------------------------------------
# Bounded work: endless inputs against a sampled RSS


def stream_endless(port, prefix, filler, total, source="127.0.0.2", sample=None):
    """Send PREFIX then FILLER repeatedly up to TOTAL octets; report when the
    first reply octets after the greeting came, how much had been sent, and
    the server's RSS samples."""
    sock = socket.create_connection(("127.0.0.1", port), timeout=30, source_address=(source, 0))
    sock.settimeout(30)
    greeting = b""
    while not greeting.endswith(CRLF):
        piece = sock.recv(4096)
        if not piece:
            break
        greeting += piece
    sock.setblocking(False)
    sent, first_reply_at, replies, samples = 0, None, b"", []
    started = time.monotonic()
    block = (filler * (65536 // len(filler) + 1))[:65536]
    pending = prefix
    closed = None
    while sent < total and time.monotonic() - started < 600:
        try:
            piece = sock.recv(65536)
            if piece:
                replies += piece
                if first_reply_at is None:
                    first_reply_at = sent
            else:
                closed = "eof"
                break
        except BlockingIOError:
            pass
        except OSError as e:
            closed = repr(e)
            break
        if not pending:
            pending = block
        try:
            n = sock.send(pending)
            sent += n
            pending = pending[n:]
        except BlockingIOError:
            select.select([sock], [sock], [], 1.0)
        except OSError as e:
            closed = repr(e)
            break
        if sample and (sent // (1 << 24)) != ((sent - 65536) // (1 << 24)):
            samples.append([sent, sample()])
    elapsed = time.monotonic() - started
    try:
        sock.close()
    except OSError:
        pass
    return {"greeting": greeting[:100].decode("ascii", "replace"), "sent": sent, "elapsed": round(elapsed, 2),
            "first_reply_after_octets": first_reply_at, "replies": replies[:400].decode("ascii", "replace"),
            "closed": closed, "rss_samples_kib": samples}


def campaign_bounds(args):
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    report = {"total_octets": args.total}
    scratch = Path(tempfile.mkdtemp(prefix="b", dir=args.scratch))
    node = Node(production_image(), scratch, tls=False)
    cases = [
        ("endless-command-line", b"GROUP ", b"a"),
        ("endless-post-header", b"POST\r\nSubject: ", b"s"),
        ("endless-post-headers", b"POST\r\n", b"X-Many: v\r\n"),
        ("endless-post-body", b"POST\r\nFrom: a@b.invalid\r\nNewsgroups: fn.test\r\nSubject: s\r\n"
                              b"Message-ID: <endless@fuzz.invalid>\r\n\r\n", b"body line\r\n"),
        ("endless-ihave-body", b"IHAVE <endless-ihave@fuzz.invalid>\r\n", b"Path: x\r\n\r\n" + b"b\r\n" * 100),
        ("endless-ihave-valid-body", b"IHAVE <endless-ih@fuzz.invalid>\r\n", None),
        ("endless-takethis-body", b"MODE STREAM\r\nTAKETHIS <endless-tt@fuzz.invalid>\r\nPath: x\r\n"
                                  b"From: a@b.invalid\r\nNewsgroups: fn.test\r\nSubject: s\r\n"
                                  b"Message-ID: <endless-tt@fuzz.invalid>\r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\n\r\n",
         b"body line\r\n"),
        ("endless-blank-lines", b"", b"\r\n"),
        ("endless-nul", b"", b"\x00"),
    ]
    only = set(args.cases or [])
    try:
        for name, prefix, filler in cases:
            if only and name not in only:
                continue
            if filler is None:
                # IHAVE's article starts after the 335; sent at once, the
                # owner reads it as the offer's article (the same octets a
                # pipelining peer sends).
                prefix += (b"Path: x\r\nFrom: a@b.invalid\r\nNewsgroups: fn.test\r\nSubject: s\r\n"
                           b"Message-ID: <endless-ih@fuzz.invalid>\r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\n\r\n")
                filler = b"body line\r\n"
            source = "127.0.0.1" if b"IHAVE" in prefix or b"TAKETHIS" in prefix else "127.0.0.2"
            before = node.rss()
            result = stream_endless(node.port, prefix, filler, args.total, source=source, sample=node.rss)
            result["rss_before_kib"] = before
            result["rss_after_kib"] = node.rss()
            result["alive"] = node.alive()
            report["node:" + name] = result
            print(name, json.dumps(result)[:600], flush=True)
            if not node.alive():
                report["node:" + name]["stderr"] = [l.decode("utf-8", "replace") for l in node.stderr.lines[-10:]]
                node.stop()
                node.start()
        reader = Reader(developer_image(), None)
        try:
            for name, prefix, filler in cases[:3] + cases[7:]:
                if only and name not in only:
                    continue
                before = reader.rss()
                result = stream_endless(reader.port, prefix, filler, args.total, sample=reader.rss)
                result["rss_before_kib"] = before
                result["rss_after_kib"] = reader.rss()
                result["alive"] = reader.alive()
                report["reader:" + name] = result
                print("reader", name, json.dumps(result)[:600], flush=True)
                if not reader.alive():
                    reader.stop()
                    reader.start()
        finally:
            reader.stop()
    finally:
        node.stop()
        shutil.rmtree(scratch, ignore_errors=True)
        (out / "bounds.json").write_text(json.dumps(report, indent=1) + "\n")
    return 0


# ---------------------------------------------------------------------------
# The store campaign

EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_FAULT, EXIT_USAGE = 0, 1, 3, 4, 5
# A message that names the host's own contract, not the input's defect.
INTERNAL = re.compile(r"ACL2 returned|non-natural|\[Errno|internal error|unexpected ACL2|"
                      r"debugger invoked|Unhandled|bridge failed|The value|is not of type")


def classify_exit(result):
    """(class, named) for a store command's CompletedProcess: named means a
    stderr line that names the input's defect, not the host's contract."""
    rc = result.returncode
    err = result.stderr.decode("utf-8", "replace")
    if rc < 0:
        return "crash-signal-{}".format(-rc), False
    if rc == EXIT_OK:
        return "ok", True
    named = bool(err.strip()) and not INTERNAL.search(err)
    word = {EXIT_REFUSED: "refused", EXIT_UNCERTAIN: "fenced", EXIT_FAULT: "fault",
            EXIT_USAGE: "usage"}.get(rc, "exit-{}".format(rc))
    return word, named


def article_bytes(image, store, message_ids):
    """What the reader model serves for ARTICLE <id>, per id, from STORE."""
    transcript = b"".join(b"ARTICLE " + m + CRLF for m in message_ids) + b"QUIT\r\n"
    return model_reply(image, [transcript], store)


def store_article_map(served_bytes, message_ids):
    """Split the model's reply stream into {message-id: 220 block or code}."""
    lines = served_bytes.split(CRLF)
    result, i = {}, 1  # skip the greeting
    for mid in message_ids:
        if i >= len(lines):
            break
        status = lines[i]
        i += 1
        if status.startswith(b"220"):
            block = []
            while i < len(lines) and lines[i] != b".":
                block.append(lines[i])
                i += 1
            i += 1
            result[mid] = CRLF.join(block)
        else:
            result[mid] = status[:3]
    return result


def store_payload(n):
    """Article N of the base store: deterministic, so a reproducer rebuilds it."""
    body = b"line %d\r\n" % n + (b".dot\r\n" if n % 3 == 0 else b"") + b"x" * ((n * 977) % 3000)
    return (b"From: a@b.invalid\r\nNewsgroups: fn.test\r\nSubject: s%d\r\nMessage-ID: <store%d@fuzz.invalid>\r\n\r\n%s\r\n"
            % (n, n, body))


def build_base_store(image, scratch, articles):
    """init + ARTICLES posts + export; (base, archive, ids)."""
    base = scratch / "base"
    init = run_image(image, ["store", base, "init", "fn.test", "fn.letters"])
    if init.returncode != 0:
        raise RuntimeError(init.stderr.decode())
    ids = []
    payload = scratch / "payload"
    for n in range(articles):
        mid = b"<store%d@fuzz.invalid>" % n
        payload.write_bytes(store_payload(n))
        posted = run_image(image, ["store", base, "post", mid.decode(), payload, "-", "-",
                                   "fn.test" if n % 2 else "fn.letters"])
        if posted.returncode != 0:
            raise RuntimeError("post {}: {}".format(n, posted.stderr.decode()))
        ids.append(mid)
    archive = scratch / "archive"
    exported = run_image(image, ["store", base, "export", archive])
    if exported.returncode != 0:
        raise RuntimeError("export: " + exported.stderr.decode())
    return base, archive, ids


def store_case(image, base, archive, ids, baseline, work, mutation):
    """Copy, apply MUTATION, run the steps; (record fields, bad or None)."""
    shutil.rmtree(work, ignore_errors=True)
    importing = mutation["kind"].startswith("import")
    if importing:
        shutil.copytree(archive, work / "archive", symlinks=True)
        victim = work / "archive" / mutation["file"]
    else:
        shutil.copytree(base, work / "store", symlinks=True)
        victim = work / "store" / mutation["file"]
    apply_mutation(victim, mutation)
    target = work / "store"
    if importing:
        steps = [("import", run_image(image, ["store", target, "import", work / "archive"]))]
        if steps[0][1].returncode == 0:
            steps.append(("status", run_image(image, ["store", target, "status"])))
    else:
        steps = [("status", run_image(image, ["store", target, "status"])),
                 ("recover", run_image(image, ["store", target, "recover"])),
                 ("status-after-recover", run_image(image, ["store", target, "status"]))]
    outcomes = [[name, r.returncode, r.stderr.decode("utf-8", "replace")[-300:]] for name, r in steps]
    bad = None
    for name, result in steps:
        cls, named = classify_exit(result)
        if cls.startswith(("crash", "exit-")):
            bad = (cls, name)
        elif cls != "ok" and not named:
            bad = ("unnamed-" + cls, name)
        elif importing and cls == "fault":
            # The archive is external input: a defect in it is a refusal
            # by name (exit 1), not a fault of the host.
            bad = ("import-fault", name)
        if bad:
            bad = (bad[0], "{} exit {}: {}".format(name, result.returncode,
                                                   result.stderr.decode("utf-8", "replace").strip()[-300:]))
            break
    served = None
    if bad is None and steps[-1][1].returncode == 0:
        rc, served_out, err = article_bytes(image, target, ids)
        served = {"model_exit": rc}
        if rc == 0:
            got = store_article_map(served_out, ids)
            changed = [m.decode() for m in ids if len(got.get(m, b"")) > 3 and got[m] != baseline.get(m)]
            missing = [m.decode() for m in ids if len(got.get(m, b"")) <= 3]
            served.update(changed=changed, missing=len(missing))
            if changed:
                bad = ("served-altered", "{} article(s) served differing from the original: {}".format(
                    len(changed), changed[:3]))
            elif missing and not importing and mutation["kind"] != "torn":
                bad = ("served-missing", "{} article(s) missing after an accepted open".format(len(missing)))
        else:
            cls, named = classify_exit(subprocess.CompletedProcess([], rc, served_out, err))
            served["class"] = cls
            if cls.startswith(("crash", "exit-")) or not named:
                bad = ("model-" + cls, err.decode("utf-8", "replace").strip()[-300:])
    return {"steps": outcomes, "served": served}, bad


def choose_mutation(rng, kind, files, root):
    victim = rng.choice(files)
    data = victim.read_bytes()
    n = len(data)
    m = {"kind": kind, "file": str(victim.relative_to(root)), "size": n}
    op = kind.split("-", 1)[-1] if kind.startswith("import") else kind
    m["op"] = op
    if op == "torn":
        m["cut"] = rng.randrange(0, n) if n else 0
    elif op == "flip":
        m["at"], m["bit"] = (rng.randrange(n), 1 << rng.randrange(8)) if n else (0, 0)
    elif op == "garbage":
        m["at"] = rng.randrange(n + 1)
        m["junk"] = bytes(rng.randrange(256) for _ in range(rng.choice([1, 4, 16, 512, 4096]))).hex()
    elif op == "zero":
        m["at"], m["length"] = rng.randrange(n + 1), rng.choice([8, 64, 4096])
    elif op == "extend":
        m["junk"] = rng.choice([b"\x00" * 4096, bytes(rng.randrange(256) for _ in range(100)), data[-64:]]).hex()
    elif op == "dup":
        m["from"] = str(rng.choice(files).relative_to(root))
    return m


def apply_mutation(path, m):
    op = m["op"]
    if op == "drop":
        path.unlink()
        return
    data = path.read_bytes()
    if op == "torn":
        data = data[:m["cut"]]
    elif op == "flip" and data:
        at = m["at"]
        data = data[:at] + bytes([data[at] ^ m["bit"]]) + data[at + 1:]
    elif op == "garbage":
        junk = bytes.fromhex(m["junk"])
        data = data[:m["at"]] + junk + data[m["at"] + len(junk):]
    elif op == "zero":
        at, length = m["at"], m["length"]
        data = data[:at] + b"\x00" * min(length, max(0, len(data) - at)) + data[at + length:]
    elif op == "extend":
        data = data + bytes.fromhex(m["junk"])
    elif op == "dup":
        data = (path.parents[len(Path(m["file"]).parts) - 1] / m["from"]).read_bytes()
    path.write_bytes(data)


STORE_KINDS = ["torn", "flip", "garbage", "zero", "extend", "import-flip", "import-torn",
               "import-garbage", "import-drop", "import-dup", "import-extend", "import-zero"]


def campaign_store(args):
    image = developer_image()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    stats = Stats("store", args.seed)
    rng = random.Random(args.seed)
    scratch = Path(tempfile.mkdtemp(prefix="s", dir=args.scratch))
    base, archive, ids = build_base_store(image, scratch, args.articles)
    rc, baseline_out, err = article_bytes(image, base, ids)
    if rc != 0:
        raise RuntimeError("baseline model: " + err.decode())
    baseline = store_article_map(baseline_out, ids)
    stats.data["articles"] = len(ids)
    stats.data["baseline_served"] = sum(1 for v in baseline.values() if len(v) > 3)
    store_files = sorted(p for p in base.rglob("*") if p.is_file() and not p.is_symlink() and "keys" not in p.parts)
    archive_files = sorted(p for p in archive.rglob("*") if p.is_file())
    stats.data["store_files"] = [str(p.relative_to(base)) for p in store_files]
    stats.data["archive_files"] = [str(p.relative_to(archive)) for p in archive_files]
    deadline = time.monotonic() + args.seconds
    case = 0
    try:
        while time.monotonic() < deadline:
            case += 1
            kind = rng.choice(STORE_KINDS)
            if kind.startswith("import"):
                mutation = choose_mutation(rng, kind, archive_files, archive)
            else:
                mutation = choose_mutation(rng, kind, store_files, base)
            fields, bad = store_case(image, base, archive, ids, baseline, scratch / "case", mutation)
            stats.data["sessions"] += 1
            for name, code, _ in fields["steps"]:
                key = "{}:{}".format(name, code)
                stats.data.setdefault("outcomes", {}).setdefault(key, 0)
                stats.data["outcomes"][key] += 1
            if fields["served"] and fields["served"].get("missing"):
                stats.data.setdefault("missing_after_accepted_open", []).append(
                    [mutation["kind"], mutation["file"], fields["served"]["missing"], [st[:2] for st in fields["steps"]]])
                del stats.data["missing_after_accepted_open"][:-40]
            if fields["served"] is not None:
                key = "served:" + ("altered" if fields["served"].get("changed") else
                                   "missing" if fields["served"].get("missing") else
                                   "all" if fields["served"].get("model_exit") == 0 else
                                   "refused-" + str(fields["served"].get("class")))
                stats.data.setdefault("outcomes", {}).setdefault(key, 0)
                stats.data["outcomes"][key] += 1
            if bad is not None:
                cls, detail = bad
                where = re.sub(r"[0-9]+", "N", mutation["file"])
                message = re.sub(r"/[^ :]*", "PATH", re.sub(r"[0-9]+", "N", detail.split("exit", 1)[-1]))[:70]
                sig = "{}/{}/{}/{}".format(cls, kind, where, message)
                record = {"campaign": "store", "seed": args.seed, "case": case, "articles": args.articles,
                          "mutation": mutation, "class": cls, "detail": detail}
                record.update(fields)
                if stats.finding(cls, sig, detail, record):
                    print("FINDING {} case={} {}".format(sig, case, detail[:300]), flush=True)
                    write_reproducer(out, "store-{}-{}".format(re.sub(r"[^a-z0-9]+", "-", (cls + "-" + kind + "-" + where).lower()), case), record)
            if case % 50 == 0:
                print("store: {} cases, {} findings".format(case, len(stats.data["findings"])), flush=True)
                stats.dump(out)
    finally:
        stats.dump(out)
        if not args.keep:
            shutil.rmtree(scratch, ignore_errors=True)
    print(json.dumps(stats.data, indent=1)[:6000])
    return 1 if stats.data["findings"] else 0


def replay_store(record):
    """Rebuild the base store, apply the recorded mutation, judge again."""
    image = developer_image()
    scratch = Path(tempfile.mkdtemp(prefix="r"))
    try:
        base, archive, ids = build_base_store(image, scratch, record.get("articles", 12))
        rc, baseline_out, err = article_bytes(image, base, ids)
        baseline = store_article_map(baseline_out, ids)
        _, bad = store_case(image, base, archive, ids, baseline, scratch / "case", record["mutation"])
        return bad
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


# ---------------------------------------------------------------------------
# Replay


def replay_bounds(record):
    """Stream the recorded endless input at a scratch owner; a finding when
    the owner's RSS grows past the recorded bound before it answers or
    closes, or when it dies."""
    scratch = Path(tempfile.mkdtemp(prefix="r"))
    node = Node(production_image(), scratch, tls=False)
    try:
        before = node.rss()
        result = stream_endless(node.port, bytes.fromhex(record["prefix_hex"]),
                                bytes.fromhex(record["filler_hex"]), record["total"],
                                source=record.get("source", "127.0.0.2"), sample=node.rss)
        peak = max([before] + [kib for _, kib in result["rss_samples_kib"]])
        if not node.alive():
            return ("node-died", "exit {}".format(node.process.returncode))
        if peak - before > record["max_growth_kib"]:
            return ("unbounded", "owner RSS grew {} KiB over {} octets sent (bound {} KiB); closed={} replies={!r}".format(
                peak - before, result["sent"], record["max_growth_kib"], result["closed"], result["replies"][:120]))
        # A fixed reproducer names what the bound must look like on the wire:
        # the refusal line, and the close before the stream ends.
        expect = record.get("expect_reply")
        if expect and expect not in result["replies"]:
            return ("not-refused", "no {!r} in the replies {!r} after {} octets sent".format(
                expect, result["replies"][:200], result["sent"]))
        if record.get("expect_closed") and not result["closed"]:
            return ("not-closed", "the owner kept reading: {} octets sent, replies {!r}".format(
                result["sent"], result["replies"][:200]))
        return None
    finally:
        node.stop()
        shutil.rmtree(scratch, ignore_errors=True)


def replay(path):
    record = json.loads(Path(path).read_text())
    if record["campaign"] == "store":
        return replay_store(record)
    if record["campaign"] == "bounds":
        return replay_bounds(record)
    chunks = [bytes.fromhex(h) for h in record.get("minimized_hex") or record["chunks_hex"]]
    if record["campaign"] == "diff":
        image = developer_image()
        store = None if record.get("store", "-") == "-" else record["store"]
        reader = Reader(image, store)
        try:
            model = model_reply(image, [b"".join(chunks)], store)
            verdict = diff_verdict(model, served(reader, chunks, 0.02 if len(chunks) > 1 else 0.0), reader)
        finally:
            reader.stop()
        return verdict
    if record["campaign"] == "node":
        scratch = Path(tempfile.mkdtemp(prefix="r"))
        node = Node(production_image(), scratch, tls=record.get("node_tls", record.get("tls", False)))
        try:
            source = "127.0.0.1" if record.get("role") == "peer" else "127.0.0.2"
            port = node.tls_port if record.get("tls") else node.port
            session = Session("127.0.0.1", port, chunks, gap=0.001 if len(chunks) > 1 else 0.0, deadline=60.0,
                              source=source, tls_context=node.tls_context() if record.get("tls") else None).run()
            return node_verdict(node, session, record.get("tls", False))
        finally:
            node.stop()
            shutil.rmtree(scratch, ignore_errors=True)
    raise SystemExit("replay: unknown campaign {}".format(record["campaign"]))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="campaign", required=True)
    for name in ("diff", "node", "bounds", "store"):
        p = sub.add_parser(name)
        p.add_argument("--seconds", type=float, default=600)
        p.add_argument("--seed", type=int, default=1)
        p.add_argument("--out", default="build/fuzz-nntp")
        p.add_argument("--scratch", default=None)
        p.add_argument("--jobs", type=int, default=4)
        p.add_argument("--minimize-max", type=int, default=12)
        p.add_argument("--keep", action="store_true")
        if name == "diff":
            p.add_argument("--store", default=None)
            p.add_argument("--store-articles", type=int, default=0)
            p.add_argument("--ids", nargs="*", default=[])
            p.add_argument("--cuts", type=int, default=4)
            p.add_argument("--every-cut-max", type=int, default=96)
        if name == "node":
            p.add_argument("--sessions", type=int, default=0)
            p.add_argument("--peer-share", type=float, default=0.3)
            p.add_argument("--tls-share", type=float, default=0.1)
            p.add_argument("--no-tls", action="store_true")
            p.add_argument("--read-only", action="store_true")
        if name == "bounds":
            p.add_argument("--total", type=int, default=256 << 20)
            p.add_argument("--cases", nargs="*", default=[])
        if name == "store":
            p.add_argument("--articles", type=int, default=12)
    p = sub.add_parser("replay")
    p.add_argument("file")
    args = parser.parse_args(argv)
    if args.campaign == "replay":
        verdict = replay(args.file)
        print("replay:", verdict or "no finding")
        return 1 if verdict else 0
    return {"diff": campaign_diff, "node": campaign_node, "bounds": campaign_bounds,
            "store": campaign_store}[args.campaign](args)


if __name__ == "__main__":
    sys.exit(main())
