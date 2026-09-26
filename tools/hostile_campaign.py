#!/usr/bin/env python3
"""SCN-146: throw an adversarial network at a running fn node and watch it.

The public-exposure and public-limits lanes proved a reader port answers
strangers within ACL2's limits over well-formed and named-malformed cases.
This driver is the other half the mandate names: adversarial, corrupted,
oversized, slow, half-open and pipelined traffic against a *running* scratch
node, with an oracle after each family that decides whether the node is still
sound.  It changes no books; every finding is a defect packet, and the fixes
are continuation lanes.

    tools/hostile_campaign.py --image build/fn-host-developer \\
        --evidence planning/evidence/hostile-input-2026-09-26 \\
        --report build/hostile-report.json

It launches its own scratch owner (and, with --bp-image, a bp-node) under
`systemd-run --user --scope -p MemoryMax=8G` when systemd-run is present and
--no-scope is not set; otherwise directly (a laptop rehearsal).  It NEVER
touches /tank/fn/node.  Only the standard library is used, so the tool ships
inside a native tree and runs on the box with nothing else.

Families (each bounded and logged):
  malformed     every command with random bytes, overlong lines, NUL, CR-only,
                UTF-8 garbage
  header        thousands of header lines, a 1 MiB single header, folded
                headers to depth, duplicate Message-IDs, a Path loop
  body          dot-stuffing edge cases, no terminator then close, a big body
                fed one octet per second then abandoned
  connection    capacity+50 half-open sockets, slowloris on AUTHINFO,
                garbage on the TLS port, STARTTLS then plain
  pipelining    a thousand commands in one write, a TAKETHIS storm
  transit       CHECK for a million ids, IHAVE with a 2 GiB announced size
  bp            (with --bp-image) raw TCPCL/contact garbage, a never-completing
                contact, a bundle declaring a 4 GiB payload length

The oracle after each family (`Oracle`): a clean authenticated session answers
correctly (the NNTP probe), the owner process is alive with RSS under the
profile's heap figure, no served request took longer than the work-quantum
wall bound, and every refusal is by name -- any "fault" line in the service
log, or a process exit with the fault code, is a defect.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

# The wall bound one served request may take.  The step budget is a wait, not
# a cut, so a *clean* request is what this bounds: an oversized or hostile
# request that makes the node spin past this is the "slow" defect class.
REQUEST_WALL_BOUND_S = 10.0
# How far above the decided heap figure the resident set may sit before we call
# it unbounded memory.  The figure is SBCL's dynamic-space reservation; RSS is
# normally a fraction of it, so crossing it under hostile load is a red flag.
RSS_MARGIN = 1.05

LOGIN, PASSWORD = "legit", "correct-horse-battery"


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def recv_line(sock, timeout):
    """One line, or b'' on a clean close, or a tag for timeout/reset."""
    sock.settimeout(timeout)
    data = bytearray()
    try:
        while not data.endswith(b"\n"):
            chunk = sock.recv(1)
            if not chunk:
                return bytes(data)
            data += chunk
    except socket.timeout:
        return b"<timeout>"
    except (ConnectionResetError, BrokenPipeError, OSError):
        return b"<reset>"
    return bytes(data)


class Node:
    """A scratch owner: its own store, config and process, on loopback."""

    def __init__(self, base: Path, image: Path, use_scope: bool, mem="8G"):
        self.base = base
        self.image = image
        self.use_scope = use_scope
        self.mem = mem
        self.port = free_port()
        self.store = base / "store"
        self.config = base / "fn.toml"
        self.log = base / "fn.log"
        self.stderr = base / "stderr.log"
        self.process = None
        self.pid = None  # the fn owner pid, even under a scope

    def command(self, args, stdin=None, timeout=180, expected=0):
        result = subprocess.run(
            [str(self.image), "--fn", *map(str, args)], cwd=os.getcwd(),
            input=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, check=False)
        if expected is not None and result.returncode != expected:
            raise RuntimeError("command {} -> {}\n{}".format(
                args, result.returncode, result.stderr.decode("utf-8", "replace")))
        return result

    def setup(self, exposure):
        self.command(["store", self.store, "init", "fn.test"])
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'
            '[auth]\nrequired = false\nprotected_only = false\npath = "{}"\n'.format(
                self.store, self.port, self.base / "control.sock", self.log,
                self.base / "auth.toml"), encoding="ascii")
        self.command(["operator", self.config, "principal", "set-password", LOGIN],
                     stdin=(PASSWORD + "\n" + PASSWORD + "\n").encode())
        for slot, value in exposure:
            self.command(["operator", self.config, "policy", "set", slot, value])

    def start(self):
        argv = [str(self.image), "--fn", "operator", str(self.config), "run"]
        if self.use_scope:
            argv = ["systemd-run", "--user", "--scope", "--quiet",
                    "-p", "MemoryMax=" + self.mem, "-p", "MemorySwapMax=0",
                    "--"] + argv
        err = open(self.stderr, "ab")
        self.process = subprocess.Popen(argv, cwd=os.getcwd(),
                                        stdout=subprocess.PIPE, stderr=err)
        # Read the readiness line ("LISTENING <port>").
        deadline = time.monotonic() + 60
        while time.monotonic() < deadline:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError("owner exited before LISTENING: {}".format(
                    self.stderr.read_text(errors="replace")[-2000:]))
            if line.startswith(b"LISTENING "):
                break
        else:
            raise RuntimeError("no LISTENING line")
        self.pid = self._owner_pid()

    def _owner_pid(self):
        """The fn owner pid.  Under a scope the Popen child is systemd-run's
        transient unit; find the fn-host process that opened our port's core."""
        if not self.use_scope:
            return self.process.pid
        want = str(self.config)
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                cmd = (entry / "cmdline").read_bytes().split(b"\0")
            except OSError:
                continue
            words = [w.decode("utf-8", "replace") for w in cmd if w]
            if want in words and "run" in words and "operator" in words:
                return int(entry.name)
        return self.process.pid

    def alive(self):
        if self.pid is None:
            return self.process is None or self.process.poll() is None
        try:
            os.kill(self.pid, 0)
            return True
        except ProcessLookupError:
            return False
        except PermissionError:
            return True

    def rss_bytes(self):
        try:
            for line in (Path("/proc") / str(self.pid) / "status").read_text().splitlines():
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) * 1024
        except OSError:
            return None
        return None

    def heap_figure_bytes(self):
        """The decided heap figure for this store, in octets, from `heap'."""
        result = self.command(["heap", "--", "store", self.store, "status"],
                              expected=None)
        text = (result.stdout + result.stderr).decode("ascii", "replace")
        m = re.search(r"heap=(\d+)\s*MB", text)
        if m:
            return int(m.group(1)) * 1024 * 1024
        m = re.search(r"figure[= ](\d+)", text) or re.search(r"(\d{9,})", text)
        return int(m.group(1)) if m else None

    def connect(self, source="127.0.0.1", timeout=10):
        return socket.create_connection(("127.0.0.1", self.port), timeout=timeout,
                                        source_address=(source, 0))

    def stop(self, evidence: Path):
        if self.process is not None and self.process.poll() is None:
            if self.pid and self.pid != self.process.pid:
                try:
                    os.kill(self.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
            self.process.terminate()
            try:
                self.process.communicate(timeout=30)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.communicate(timeout=30)
        for name in ("fn.log", "stderr.log"):
            src = self.base / name
            if src.exists():
                (evidence / name).write_bytes(src.read_bytes())


class Oracle:
    """After every family: a clean session answers, the owner is alive with
    bounded RSS, no request was slow, and the log holds no fault."""

    def __init__(self, node: Node, evidence: Path):
        self.node = node
        self.evidence = evidence
        self.heap_figure = node.heap_figure_bytes()
        self.log_offset = self._log_len()

    def _log_len(self):
        try:
            return self.node.log.stat().st_size
        except OSError:
            return 0

    def new_log(self):
        try:
            with open(self.node.log, "rb") as handle:
                handle.seek(self.log_offset)
                return handle.read()
        except OSError:
            return b""

    def clean_session(self):
        """An authenticated GROUP/DATE/LIST/ARTICLE round trip; the max wall
        time of any single reply, and every reply's first line."""
        started = time.monotonic()
        replies = {}
        worst = 0.0
        try:
            with self.node.connect() as sock:
                stream = sock.makefile("rwb", buffering=0)
                replies["greeting"] = stream.readline()
                for line, key in (
                        (b"AUTHINFO USER " + LOGIN.encode() + b"\r\n", "user"),
                        (b"AUTHINFO PASS " + PASSWORD.encode() + b"\r\n", "pass"),
                        (b"DATE\r\n", "date"),
                        (b"GROUP fn.test\r\n", "group"),
                        (b"LIST\r\n", "list")):
                    t0 = time.monotonic()
                    stream.write(line)
                    reply = stream.readline()
                    if reply.startswith(b"215") or reply.startswith(b"101"):
                        while True:
                            more = stream.readline()
                            if more in (b".\r\n", b""):
                                break
                    dt = time.monotonic() - t0
                    worst = max(worst, dt)
                    replies[key] = reply
                stream.write(b"QUIT\r\n")
                replies["quit"] = stream.readline()
        except OSError as error:
            replies["error"] = repr(error).encode()
        ok = (replies.get("date", b"").startswith(b"111 ")
              and replies.get("group", b"").startswith(b"211 ")
              and replies.get("quit", b"").startswith(b"205 "))
        return {"ok": ok, "worst_reply_s": round(worst, 3),
                "total_s": round(time.monotonic() - started, 3),
                "replies": {k: v.decode("ascii", "replace").strip()
                            for k, v in replies.items()}}

    def check(self, family, request_wall_s):
        clean = self.clean_session()
        rss = self.node.rss_bytes()
        alive = self.node.alive()
        log = self.new_log()
        self.log_offset = self._log_len()
        faults = [l.decode("ascii", "replace")
                  for l in log.splitlines()
                  if b"fault" in l.lower() or b"uncertain" in l.lower()]
        defects = []
        if not alive:
            defects.append(("owner-death", "the owner process is not alive"))
        elif not clean["ok"]:
            defects.append(("wrong-reply",
                            "a clean session did not answer: " + json.dumps(clean["replies"])))
        if clean["worst_reply_s"] > REQUEST_WALL_BOUND_S:
            defects.append(("slow", "a clean reply took {:.1f}s".format(clean["worst_reply_s"])))
        if request_wall_s is not None and request_wall_s > REQUEST_WALL_BOUND_S:
            defects.append(("slow", "a hostile request took {:.1f}s".format(request_wall_s)))
        if (rss is not None and self.heap_figure
                and rss > self.heap_figure * RSS_MARGIN):
            defects.append(("unbounded-memory",
                            "RSS {} > heap figure {}".format(rss, self.heap_figure)))
        if faults:
            defects.append(("fault", "; ".join(faults[:5])))
        return {"family": family, "alive": alive, "clean": clean,
                "rss_bytes": rss, "heap_figure_bytes": self.heap_figure,
                "request_wall_s": request_wall_s,
                "faults": faults, "defects": defects}


# --------------------------------------------------------------------------
# The families.  Each returns (rows, worst_request_wall_s); a row records the
# stimulus and the first line the node sent, so the record's table is generated.

def _one_command(node, source, payload, read_timeout=8):
    """Send one raw payload on a fresh connection past the greeting; return the
    first reply line and the seconds it took."""
    t0 = time.monotonic()
    try:
        with node.connect(source=source) as sock:
            greeting = recv_line(sock, 10)
            sock.sendall(payload)
            reply = recv_line(sock, read_timeout)
    except OSError as error:
        return "connect-" + type(error).__name__, round(time.monotonic() - t0, 3)
    return reply.decode("ascii", "replace").strip()[:60], round(time.monotonic() - t0, 3)


def family_malformed(node, evidence):
    rows = {}
    worst = 0.0
    verbs = [b"ARTICLE", b"GROUP", b"HEAD", b"BODY", b"STAT", b"LIST", b"OVER",
             b"HDR", b"NEWNEWS", b"NEWGROUPS", b"POST", b"IHAVE", b"CHECK",
             b"TAKETHIS", b"AUTHINFO", b"MODE", b"XOVER", b"LISTGROUP", b"NEXT",
             b"LAST", b"QUIT", b"HELP", b"CAPABILITIES", b"DATE"]
    cases = {}
    for verb in verbs:
        cases[verb.decode() + " random-bytes"] = verb + b" " + bytes(
            (i * 37 + 11) & 0xFF for i in range(40)) + b"\r\n"
    cases["overlong 512"] = b"ARTICLE " + b"A" * 512 + b"\r\n"
    cases["overlong 4096"] = b"ARTICLE " + b"A" * 4096 + b"\r\n"
    cases["overlong 1MiB no-CRLF"] = b"ARTICLE " + b"A" * (1 << 20)
    cases["embedded NUL"] = b"GROUP fn.\x00test\r\n"
    cases["all NUL line"] = b"\x00" * 32 + b"\r\n"
    cases["CR only"] = b"GROUP fn.test\r" + b"MODE READER\r"
    cases["LF only"] = b"GROUP fn.test\nMODE READER\n"
    cases["bare CRLF"] = b"\r\n"
    cases["utf8 garbage"] = "GROUP \U0001f4a3‮� fn.test\r\n".encode("utf-8")
    cases["invalid utf8"] = b"GROUP \xc3\x28\xa0\xa1\xed\xa0\x80 fn\r\n"
    cases["high bytes verb"] = bytes(range(0x80, 0xC0)) + b"\r\n"
    cases["leading spaces"] = b"        \r\n"
    cases["telnet iac"] = b"\xff\xfb\x01\xff\xfe\x01ARTICLE 1\r\n"
    saved = 0
    for name, payload in cases.items():
        reply, dt = _one_command(node, "127.0.0.3", payload)
        worst = max(worst, dt)
        rows[name] = {"reply": reply, "seconds": dt}
        # An empty reply to a malformed line (silent close) or a slow one is
        # worth keeping the exact bytes for.
        if reply in ("", "<timeout>", "<reset>") or dt > REQUEST_WALL_BOUND_S:
            (evidence / "malformed-{}.bytes".format(saved)).write_bytes(payload)
            rows[name]["saved"] = "malformed-{}.bytes".format(saved)
            saved += 1
    return rows, worst


def _post_article(headers: bytes, body: bytes = b"hostile body\r\n"):
    return headers + b"\r\n" + body


def family_header(node, evidence):
    rows = {}
    worst = 0.0
    base_hdr = (b"From: a@b.invalid\r\nNewsgroups: fn.test\r\n"
                b"Subject: hdr\r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\n")

    def post(name, article, source="127.0.0.4"):
        nonlocal worst
        t0 = time.monotonic()
        reply = "<no-340>"
        try:
            with node.connect(source=source, timeout=30) as sock:
                stream = sock.makefile("rwb", buffering=0)
                stream.readline()
                for creds in (b"AUTHINFO USER " + LOGIN.encode() + b"\r\n",
                              b"AUTHINFO PASS " + PASSWORD.encode() + b"\r\n"):
                    stream.write(creds)
                    stream.readline()
                stream.write(b"POST\r\n")
                r340 = stream.readline()
                if r340.startswith(b"340"):
                    sock.settimeout(30)
                    sock.sendall(article + b"\r\n.\r\n")
                    reply = recv_line(sock, 20).decode("ascii", "replace").strip()[:60]
                else:
                    reply = r340.decode("ascii", "replace").strip()[:60]
        except OSError as error:
            reply = "err-" + type(error).__name__
        dt = round(time.monotonic() - t0, 3)
        if reply[:1].isdigit():
            worst = max(worst, dt)
        rows[name] = {"reply": reply, "seconds": dt, "article_octets": len(article)}
        return reply

    # thousands of header lines
    many = base_hdr + b"".join(
        b"X-Filler-%d: v\r\n" % n for n in range(5000)) + b"Message-ID: <hdr-many@x.invalid>\r\n"
    post("5000 header lines", _post_article(many))
    (evidence / "header-5000-lines.article").write_bytes(_post_article(many))
    # a 1 MiB single header
    big = base_hdr + b"X-Huge: " + b"z" * (1 << 20) + b"\r\nMessage-ID: <hdr-huge@x.invalid>\r\n"
    post("1MiB single header", _post_article(big))
    (evidence / "header-1mib.article").write_bytes(_post_article(big))
    # folded headers to depth
    folded = base_hdr + b"X-Folded:" + b"".join(
        b"\r\n more" for _ in range(2000)) + b"\r\nMessage-ID: <hdr-fold@x.invalid>\r\n"
    post("folded to depth 2000", _post_article(folded))
    (evidence / "header-folded.article").write_bytes(_post_article(folded))
    # duplicate Message-IDs within one article
    dup = base_hdr + b"Message-ID: <dup@x.invalid>\r\nMessage-ID: <dup2@x.invalid>\r\n"
    post("duplicate Message-ID header", _post_article(dup))
    # a Path loop (self in Path)
    loop = (base_hdr + b"Path: a!b!a!b!a!b!not-for-mail\r\n"
            b"Message-ID: <path-loop@x.invalid>\r\n")
    post("Path loop", _post_article(loop))
    # many duplicate header fields
    dupfields = base_hdr + b"".join(b"Subject: dup\r\n" for _ in range(500)) + \
        b"Message-ID: <hdr-dupfields@x.invalid>\r\n"
    post("500 Subject fields", _post_article(dupfields))
    return rows, worst


def family_body(node, evidence):
    rows = {}
    worst = 0.0
    base_hdr = (b"From: a@b.invalid\r\nNewsgroups: fn.test\r\nSubject: body\r\n"
                b"Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n")

    def post_raw(name, article_bytes, source="127.0.0.5"):
        nonlocal worst
        t0 = time.monotonic()
        reply = "<no-340>"
        try:
            with node.connect(source=source, timeout=30) as sock:
                stream = sock.makefile("rwb", buffering=0)
                stream.readline()
                for creds in (b"AUTHINFO USER " + LOGIN.encode() + b"\r\n",
                              b"AUTHINFO PASS " + PASSWORD.encode() + b"\r\n"):
                    stream.write(creds)
                    stream.readline()
                stream.write(b"POST\r\n")
                r340 = stream.readline()
                if r340.startswith(b"340"):
                    sock.settimeout(30)
                    sock.sendall(article_bytes)
                    reply = recv_line(sock, 20).decode("ascii", "replace").strip()[:60]
                else:
                    reply = r340.decode("ascii", "replace").strip()[:60]
        except OSError as error:
            reply = "err-" + type(error).__name__
        dt = round(time.monotonic() - t0, 3)
        # Only a genuine status line is a server-processing latency; a timeout
        # here means the client withheld the terminator (a framing case), which
        # is not the server being slow.
        if reply[:1].isdigit():
            worst = max(worst, dt)
        rows[name] = {"reply": reply, "seconds": dt}

    hdr = base_hdr + b"Message-ID: <body-1@x.invalid>\r\n\r\n"
    # dot-stuffing edge cases: a line that is a single dot un-stuffed (ends
    # the article early), a dot-line mid body, leading-dot lines.
    post_raw("bare dot mid-body",
             base_hdr + b"Message-ID: <body-dot@x.invalid>\r\n\r\nabc\r\n.\r\ndef\r\n.\r\n")
    post_raw("leading-dot lines (stuffed)",
             base_hdr + b"Message-ID: <body-stuff@x.invalid>\r\n\r\n..hidden\r\n...more\r\n.\r\n")
    post_raw("dot then no CRLF",
             base_hdr + b"Message-ID: <body-dot2@x.invalid>\r\n\r\nbody\r\n.")
    # no terminator then close: send a partial article, never the ".\r\n"
    t0 = time.monotonic()
    try:
        with node.connect(source="127.0.0.5", timeout=15) as sock:
            stream = sock.makefile("rwb", buffering=0)
            stream.readline()
            for creds in (b"AUTHINFO USER " + LOGIN.encode() + b"\r\n",
                          b"AUTHINFO PASS " + PASSWORD.encode() + b"\r\n"):
                stream.write(creds)
                stream.readline()
            stream.write(b"POST\r\n")
            stream.readline()
            sock.sendall(hdr + b"body with no terminator\r\n")
            # do not send ".\r\n"; just close
    except OSError:
        pass
    rows["no terminator then close"] = {"reply": "closed", "seconds": round(time.monotonic() - t0, 3)}

    # a big body at 1 byte/second then abandon (bounded: 30 s of trickle)
    t0 = time.monotonic()
    trickled = 0
    try:
        with node.connect(source="127.0.0.5", timeout=15) as sock:
            stream = sock.makefile("rwb", buffering=0)
            stream.readline()
            for creds in (b"AUTHINFO USER " + LOGIN.encode() + b"\r\n",
                          b"AUTHINFO PASS " + PASSWORD.encode() + b"\r\n"):
                stream.write(creds)
                stream.readline()
            stream.write(b"POST\r\n")
            r = stream.readline()
            if r.startswith(b"340"):
                sock.sendall(hdr)
                deadline = time.monotonic() + 30
                while time.monotonic() < deadline:
                    try:
                        sock.sendall(b"x")
                        trickled += 1
                    except OSError:
                        break
                    time.sleep(1.0)
                    sock.settimeout(0.05)
                    try:
                        if sock.recv(1) == b"":
                            break
                    except socket.timeout:
                        pass
                    except OSError:
                        break
    except OSError:
        pass
    rows["100MiB body at 1 B/s (abandoned)"] = {
        "reply": "trickled {} octets before close/timeout".format(trickled),
        "seconds": round(time.monotonic() - t0, 3)}
    # `worst' counts only the reply latency of a fully-delivered article (a
    # server-processing time).  The no-terminator and trickle cases are the
    # client withholding data, not the server being slow, so they are not a
    # per-request wall measure; the clean-session probe after the family is the
    # oracle for a wedged node.
    return rows, worst


def family_connection(node, evidence, capacity):
    rows = {}
    worst = 0.0
    # capacity+50 half-open sockets held at once
    held = []
    target = capacity + 50
    classified = {}
    lock = threading.Lock()

    def one(n):
        try:
            sock = node.connect(source="127.0.6.{}".format(1 + (n % 200)), timeout=15)
        except OSError as error:
            with lock:
                classified["connect-" + type(error).__name__] = \
                    classified.get("connect-" + type(error).__name__, 0) + 1
            return
        line = recv_line(sock, 20)
        kind = "admitted" if line[:3] in (b"200", b"201") else \
            (line.decode("ascii", "replace").strip()[:32] or "closed")
        with lock:
            classified[kind] = classified.get(kind, 0) + 1
            held.append(sock)

    threads = [threading.Thread(target=one, args=(n,)) for n in range(target)]
    t0 = time.monotonic()
    for t in threads:
        t.start()
    for t in threads:
        t.join(45)
    # The flood's join time is client-paced (we hold sockets open), not a
    # served-request latency; the clean-session probe is the slow oracle.
    rows["half-open capacity+50"] = {"target": target, "classified": classified}
    for sock in held:
        try:
            sock.close()
        except OSError:
            pass

    # slowloris on AUTHINFO: open, send "AUTHINFO USER l" one byte at a time
    t0 = time.monotonic()
    try:
        with node.connect(source="127.0.6.201", timeout=15) as sock:
            recv_line(sock, 10)
            for ch in b"AUTHINFO USER legit":
                sock.sendall(bytes([ch]))
                time.sleep(1.0)
            final = recv_line(sock, 15)
        rows["slowloris AUTHINFO"] = {
            "reply": final.decode("ascii", "replace").strip()[:40],
            "seconds": round(time.monotonic() - t0, 3)}
    except OSError as error:
        rows["slowloris AUTHINFO"] = {"reply": "err-" + type(error).__name__,
                                      "seconds": round(time.monotonic() - t0, 3)}
    return rows, None


def family_pipelining(node, evidence):
    rows = {}
    worst = 0.0
    # a thousand commands in one write
    t0 = time.monotonic()
    pipe = b"".join(b"DATE\r\n" for _ in range(1000))
    replies = 0
    try:
        with node.connect(source="127.0.7.1", timeout=30) as sock:
            recv_line(sock, 10)
            sock.sendall(pipe)
            sock.settimeout(20)
            buf = b""
            deadline = time.monotonic() + 20
            while time.monotonic() < deadline:
                try:
                    chunk = sock.recv(65536)
                except socket.timeout:
                    break
                if not chunk:
                    break
                buf += chunk
                replies = buf.count(b"111 ")
                if replies >= 1000:
                    break
    except OSError:
        pass
    dt = round(time.monotonic() - t0, 3)
    # dt is the client's read-loop deadline, not a served-request latency
    rows["1000 DATE in one write"] = {"replies_seen": replies, "seconds": dt}
    (evidence / "pipeline-1000-date.bytes").write_bytes(pipe[:4096])

    # a TAKETHIS storm: 200 TAKETHIS with tiny articles in one write to the
    # reader port (no MODE STREAM; the node is not a peer for this source).
    art = (b"From: a@b.invalid\r\nNewsgroups: fn.test\r\nSubject: s\r\n"
           b"Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n")
    storm = b"".join(
        b"TAKETHIS <storm-%d@x.invalid>\r\n" % n + art +
        b"Message-ID: <storm-%d@x.invalid>\r\n\r\nb\r\n.\r\n" % n
        for n in range(200))
    t0 = time.monotonic()
    seen = b""
    try:
        with node.connect(source="127.0.7.2", timeout=30) as sock:
            recv_line(sock, 10)
            sock.sendall(storm)
            sock.settimeout(15)
            deadline = time.monotonic() + 15
            while time.monotonic() < deadline:
                try:
                    chunk = sock.recv(65536)
                except socket.timeout:
                    break
                if not chunk:
                    break
                seen += chunk
    except OSError:
        pass
    dt = round(time.monotonic() - t0, 3)
    # dt is the client's read-loop deadline, not a served-request latency
    rows["TAKETHIS storm x200"] = {
        "bytes_back": len(seen), "first": seen[:40].decode("ascii", "replace").strip(),
        "seconds": dt}
    (evidence / "pipeline-takethis-storm.bytes").write_bytes(storm[:8192])
    return rows, None


def family_transit(node, evidence):
    rows = {}
    worst = 0.0
    # CHECK for a million ids in one write, on the reader port.  Bounded: we
    # stream them so the client memory is bounded too.
    t0 = time.monotonic()
    seen = b""
    count = 200000  # a large offer flood; "a million" is the class, bounded here
    try:
        with node.connect(source="127.0.8.1", timeout=30) as sock:
            recv_line(sock, 10)
            sock.sendall(b"MODE STREAM\r\n")
            recv_line(sock, 10)
            sock.settimeout(20)
            sender_done = threading.Event()

            def send():
                try:
                    for n in range(count):
                        sock.sendall(b"CHECK <flood-%d@x.invalid>\r\n" % n)
                except OSError:
                    pass
                finally:
                    sender_done.set()

            th = threading.Thread(target=send, daemon=True)
            th.start()
            deadline = time.monotonic() + 25
            while time.monotonic() < deadline:
                try:
                    chunk = sock.recv(65536)
                except socket.timeout:
                    if sender_done.is_set():
                        break
                    continue
                if not chunk:
                    break
                seen += chunk
                if len(seen) > (8 << 20):  # 8 MiB of replies is enough evidence
                    break
            th.join(1)
    except OSError:
        pass
    dt = round(time.monotonic() - t0, 3)
    # dt is the client's read-loop deadline, not a served-request latency
    rows["CHECK flood (200k ids)"] = {
        "reply_octets": len(seen), "first": seen[:40].decode("ascii", "replace").strip(),
        "seconds": dt}

    # IHAVE with a 2 GiB announced size: the arg is only a Message-ID in NNTP,
    # so "announced size" is expressed as an article whose declared payload is
    # huge -- we open IHAVE, get 335, then start sending a body but declare (in
    # a header) a 2 GiB length and trickle, then abandon.  The bound-before-
    # consume rule says the node must not preallocate on the header's word.
    t0 = time.monotonic()
    reply = "<none>"
    try:
        with node.connect(source="127.0.8.2", timeout=30) as sock:
            stream = sock.makefile("rwb", buffering=0)
            stream.readline()
            stream.write(b"IHAVE <ihave-2gb@x.invalid>\r\n")
            r335 = stream.readline()
            reply = r335.decode("ascii", "replace").strip()[:40]
            if r335.startswith(b"335"):
                sock.sendall(b"From: a@b.invalid\r\nNewsgroups: fn.test\r\n"
                             b"Subject: s\r\nContent-Length: 2147483648\r\n"
                             b"Message-ID: <ihave-2gb@x.invalid>\r\n\r\n")
                rss_before = node.rss_bytes()
                for _ in range(10):
                    sock.sendall(b"x" * 4096)
                    time.sleep(0.2)
                rss_after = node.rss_bytes()
                rows["IHAVE 2GiB declared: rss delta"] = {
                    "before": rss_before, "after": rss_after}
                # abandon: close without terminator
    except OSError as error:
        reply = "err-" + type(error).__name__
    dt = round(time.monotonic() - t0, 3)
    # dt is the client's read-loop deadline, not a served-request latency
    rows["IHAVE 2GiB announced"] = {"offer_reply": reply, "seconds": dt}
    return rows, None


TCPCL_MAGIC = b"dtn!"


def _tcl_contact(version=4, flags=0):
    return TCPCL_MAGIC + bytes([version, flags])


def _tcl_sess_init(keepalive=10, segment_mru=1024, transfer_mru=1048576,
                   node_id=b"dtn://active/", ext=b""):
    body = (keepalive.to_bytes(2, "big") + segment_mru.to_bytes(8, "big")
            + transfer_mru.to_bytes(8, "big") + len(node_id).to_bytes(2, "big")
            + node_id + len(ext).to_bytes(4, "big") + ext)
    return bytes([7]) + body


def _tcl_xfer_segment(xfer_id, data, start=True, end=False, declared_len=None,
                      ext=b""):
    flags = (2 if start else 0) | (1 if end else 0)
    body = bytearray([flags]) + xfer_id.to_bytes(8, "big")
    if start:
        body += len(ext).to_bytes(4, "big") + ext
    length = declared_len if declared_len is not None else len(data)
    body += length.to_bytes(8, "big") + data
    return bytes([1]) + bytes(body)


def family_bp(image, evidence, use_scope, mem):
    """Raw TCPCL/contact garbage at a bp-node serve listener: a wrong magic, a
    never-completing contact, and an XFER_SEGMENT declaring a 4 GiB payload.
    The node must reject or time out each within its bounds, stay alive, and
    still complete a fresh contact handshake (the clean session for BP).  The
    bounded-work rule (AGENTS.md) says the declared length must not be
    preallocated before the octets arrive."""
    base = Path(tempfile.mkdtemp(prefix="fn-hostile-bp-"))
    rows, defects = {}, []
    store = base / "store"
    journal = base / "fnbs"
    receipts = base / "fnrj"
    workflow = base / "fnwf"
    config = base / "fn.toml"
    port = free_port()

    def invoke(args, timeout=120, expected=0):
        r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=os.getcwd(),
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout, check=False)
        if expected is not None and r.returncode != expected:
            raise RuntimeError("bp setup {} -> {}\n{}".format(
                args, r.returncode, r.stderr.decode("utf-8", "replace")))
        return r

    proc = None
    try:
        invoke(["store", store, "init", "fn.test"])
        config.write_text('[store]\npath = "{}"\n'.format(store), encoding="ascii")
        invoke(["operator", config, "policy", "set", "path-identity",
                "receiver.bp.gate.invalid"])
        invoke(["operator", config, "bp-boundary", "add", "sender-boundary",
                "sender.bp.gate.invalid", "dtn://sender/", port, "fn.test",
                32768, 16])
        argv = [str(image), "--fn", "bp-node", "serve", str(port), str(journal),
                str(store), str(receipts), str(workflow), "dtn://receiver/",
                "dtn://sender/", "dtn://receiver/", "native-policy",
                "dtn://receiver/", "127.0.0.1", "9", "0", "3600000", "2", "32",
                "1048576", "1000", "0"]
        if use_scope:
            argv = ["systemd-run", "--user", "--scope", "--quiet",
                    "-p", "MemoryMax=" + mem, "-p", "MemorySwapMax=0", "--"] + argv
        proc = subprocess.Popen(argv, cwd=os.getcwd(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, bufsize=0)
        deadline = time.monotonic() + 60
        ready = False
        while time.monotonic() < deadline:
            line = proc.stdout.readline()
            if not line:
                break
            if line.startswith(b"BP NODE LISTENING "):
                ready = True
                break
        if not ready:
            defects.append(("owner-death", "bp-node did not announce LISTENING"))
            return rows, defects

        def raw(name, payload, read_timeout, saved=None):
            t0 = time.monotonic()
            back = b""
            try:
                with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
                    sock.sendall(payload)
                    sock.settimeout(read_timeout)
                    try:
                        back = sock.recv(4096)
                    except socket.timeout:
                        back = b"<timeout>"
            except OSError as error:
                back = ("err-" + type(error).__name__).encode()
            rows[name] = {"bytes_back": len(back) if isinstance(back, bytes) and not back.startswith(b"<") and not back.startswith(b"err") else back.decode("ascii", "replace"),
                          "seconds": round(time.monotonic() - t0, 3),
                          "back_hex": back[:32].hex() if isinstance(back, bytes) else ""}
            if saved:
                (evidence / saved).write_bytes(payload[:4096])

        # 1. wrong magic
        raw("wrong magic", b"GET / HTTP/1.1\r\nHost: x\r\n\r\n", 8, "bp-wrong-magic.bytes")
        # 2. valid contact then silence (never-completing)
        t0 = time.monotonic()
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
                sock.sendall(_tcl_contact())
                sock.settimeout(40)
                try:
                    closed = sock.recv(4096)
                except socket.timeout:
                    closed = b"<held-open>"
            rows["contact then silence"] = {
                "outcome": (closed[:16].hex() if isinstance(closed, bytes)
                            and not closed.startswith(b"<") else
                            closed.decode("ascii", "replace")),
                "seconds": round(time.monotonic() - t0, 3)}
        except OSError as error:
            rows["contact then silence"] = {"outcome": "err-" + type(error).__name__,
                                            "seconds": round(time.monotonic() - t0, 3)}
        if rows["contact then silence"]["seconds"] > 35:
            defects.append(("slow", "bp accept-timeout did not close a silent contact"))
        # 3. Establish a proper session (a within-bounds SESS_INIT so the
        # transfer decoder is reached), then an XFER_SEGMENT declaring 4 GiB
        # with tiny data.  The bounded-work rule says the declared length must
        # not be preallocated before its octets arrive: the node must refuse
        # (XFER_REFUSE / MSG_REJECT / close) without RSS growth.
        payload = (_tcl_contact() + _tcl_sess_init(transfer_mru=1048576)
                   + _tcl_xfer_segment(1, b"tiny", start=True, end=False,
                                       declared_len=(4 << 30)))
        rss_before = _proc_rss(proc.pid)
        t0 = time.monotonic()
        back = b""
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
                sock.sendall(payload)
                sock.settimeout(10)
                deadline = time.monotonic() + 8
                while time.monotonic() < deadline:
                    try:
                        chunk = sock.recv(4096)
                    except socket.timeout:
                        break
                    if not chunk:
                        break
                    back += chunk
                    if len(back) > 65536:
                        break
        except OSError as error:
            back = ("err-" + type(error).__name__).encode()
        (evidence / "bp-4gib-xfer.bytes").write_bytes(payload[:4096])
        rss_after = _proc_rss(proc.pid)
        rows["XFER 4GiB declared, tiny data"] = {
            "bytes_back": len(back), "back_hex": back[:48].hex(),
            "seconds": round(time.monotonic() - t0, 3),
            "rss_before": rss_before, "rss_after": rss_after}
        if (rss_before and rss_after and rss_after - rss_before > (256 << 20)):
            defects.append(("unbounded-memory",
                            "bp RSS grew {} on a 4 GiB declared XFER".format(
                                rss_after - rss_before)))
        # oracle: bp-node still alive and completes a fresh contact handshake
        alive = proc.poll() is None
        if not alive:
            defects.append(("owner-death", "bp-node died during the BP family"))
        else:
            t0 = time.monotonic()
            fresh = b""
            try:
                with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
                    sock.sendall(_tcl_contact() + _tcl_sess_init())
                    sock.settimeout(10)
                    fresh = sock.recv(64)
            except OSError:
                pass
            ok = fresh.startswith(TCPCL_MAGIC) or len(fresh) > 0
            rows["clean handshake after abuse"] = {
                "ok": bool(ok), "back_hex": fresh[:16].hex(),
                "seconds": round(time.monotonic() - t0, 3)}
        # faults in the bp-node output
        proc.terminate()
        try:
            out, err = proc.communicate(timeout=30)
        except subprocess.TimeoutExpired:
            proc.kill()
            out, err = proc.communicate(timeout=30)
        combined = (out + err)
        (evidence / "bp-node.log").write_bytes(combined[-16384:])
        faults = [l.decode("ascii", "replace") for l in combined.splitlines()
                  if b"fault" in l.lower()]
        if faults:
            defects.append(("fault", "; ".join(faults[:5])))
    finally:
        if proc is not None and proc.poll() is None:
            proc.kill()
            proc.communicate(timeout=10)
        try:
            shutil.rmtree(base)
        except OSError:
            pass
    return rows, defects


def _proc_rss(pid):
    try:
        for line in (Path("/proc") / str(pid) / "status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1]) * 1024
    except OSError:
        return None
    return None


def run(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--mem", default="8G")
    parser.add_argument("--no-scope", action="store_true",
                        help="do not wrap the owner in systemd-run (a laptop rehearsal)")
    parser.add_argument("--capacity", type=int, default=31)
    parser.add_argument("--families", default="malformed,header,body,connection,"
                        "pipelining,transit,bp")
    args = parser.parse_args(argv)

    args.evidence.mkdir(parents=True, exist_ok=True)
    use_scope = (not args.no_scope) and shutil.which("systemd-run") is not None
    report = {"started": now(), "image": str(args.image), "scope": use_scope,
              "families": {}, "oracle": {}, "defects": []}

    base = Path(tempfile.mkdtemp(prefix="fn-hostile-"))
    node = Node(base, args.image, use_scope, args.mem)
    try:
        node.setup(exposure=[
            ("exposure-connections", str(args.capacity)),
            ("exposure-per-address", "8"),
            ("exposure-steps-per-second", "64"),
            ("exposure-first-seconds", "10"),
            ("exposure-idle-seconds", "20"),
            ("exposure-auth-failures", "10"),
            ("anonymous", "open"),
        ])
        node.start()
        oracle = Oracle(node, args.evidence)
        report["heap_figure_bytes"] = oracle.heap_figure

        families = {
            "malformed": lambda: family_malformed(node, args.evidence),
            "header": lambda: family_header(node, args.evidence),
            "body": lambda: family_body(node, args.evidence),
            "connection": lambda: family_connection(node, args.evidence, args.capacity),
            "pipelining": lambda: family_pipelining(node, args.evidence),
            "transit": lambda: family_transit(node, args.evidence),
        }
        for name in args.families.split(","):
            name = name.strip()
            if name not in families:
                continue
            print("== family {} {}".format(name, now()), flush=True)
            try:
                rows, worst = families[name]()
            except Exception as error:  # a family bug must not lose the run
                rows, worst = {"harness-error": repr(error)}, None
            report["families"][name] = rows
            verdict = oracle.check(name, worst)
            report["oracle"][name] = verdict
            for kind, detail in verdict["defects"]:
                report["defects"].append({"family": name, "class": kind, "detail": detail})
            print("   {} -> {}".format(name, "OK" if not verdict["defects"]
                                       else [d[0] for d in verdict["defects"]]), flush=True)
        # BP runs its own bp-node process and oracle (a separate listener).
        if "bp" in [n.strip() for n in args.families.split(",")]:
            print("== family bp {}".format(now()), flush=True)
            try:
                rows, bp_defects = family_bp(args.image, args.evidence, use_scope, args.mem)
            except Exception as error:
                rows, bp_defects = {"harness-error": repr(error)}, \
                    [("harness", repr(error))]
            report["families"]["bp"] = rows
            report["oracle"]["bp"] = {"family": "bp", "defects": bp_defects}
            for kind, detail in bp_defects:
                report["defects"].append({"family": "bp", "class": kind, "detail": detail})
            print("   bp -> {}".format("OK" if not bp_defects
                                       else [d[0] for d in bp_defects]), flush=True)
    finally:
        node.stop(args.evidence)
        report["finished"] = now()
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=1, sort_keys=True), encoding="ascii")
        try:
            shutil.rmtree(base)
        except OSError:
            pass
    severity = {"owner-death": 0, "fault": 1, "unbounded-memory": 2,
                "wrong-reply": 3, "slow": 4}
    report["defects"].sort(key=lambda d: severity.get(d["class"], 9))
    print("HOSTILE-REPORT " + json.dumps({"defects": report["defects"]}, sort_keys=True))
    return 1 if report["defects"] else 0


if __name__ == "__main__":
    sys.exit(run())
