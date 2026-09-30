#!/usr/bin/env python3
"""Fitness under real use: soak, chaos, two nodes, memory (lane fitness, 2026-09-28).

    python3 tools/fitness.py soak   --image IMG --fixture DIR --work DIR [--minutes 120]
                                    [--posters 8] [--readers 8] [--sample-minutes 15]
                                    [--client-minutes 10] [--chaos] [--developer IMG]
    python3 tools/fitness.py pair   --image IMG --work DIR [--per-side 2000] [--minutes 60]
    python3 tools/fitness.py memory --image IMG --fixture DIR --work DIR

Run ON hbox, from a tree tools/hbox_native.sh shipped, inside swarm-build
(or a systemd-run scope with MemoryMax): it starts native owners with
`IMAGE --fn operator CONFIG run`, drives them over real sockets (implicit
TLS, AUTHINFO after an `account invite` + XREDEEM, as the public node is
configured) and records what a real peer or reader would see.  The unit of
evidence is one JSON line per event in WORK/events.jsonl and one summary
in WORK/summary.json; nothing here decides what fn should have answered
beyond the fail conditions below, each of which is a finding, not an
exception:

  * a 5xx reply outside the command's RFC 3977 row (FIVE_XX_ALLOWED);
  * an uncertain answer (a POST with no final reply) with no disk event
    (a kill, a stall or a full disk) in the window around it;
  * an acknowledged (240) article that a later GROUP-refreshed STAT does
    not find, unless this run cancelled or superseded it;
  * a refused article that is served;
  * RSS that grows at every sample after the first hour (reported with the
    slope, never judged on one sample);
  * a reply sampled live that differs from the same command's reply after a
    restart, and `store digest` of the checkpointed open differing from a
    full replay of the same log.

--chaos (soak only; needs --developer, the image honouring
FN_NATIVE_TEST_DISK_STALL_FILE) mixes in: SIGKILL of the owner at random
instants (--kills, default 10), 60 s disk stalls (--stalls), one full disk
(a size-limited tmpfs the store lives on, mounted with sudo; --disk-full)
and one torn write at the log tail after a kill (--torn).  After each: the
restart's time to LISTENING, every acknowledged article present, nothing
refused served, and the `health` verb's words.

Only PIDs this process started are signalled.  Nothing under /tank/fn/node
is read or written.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import secrets
import select
import shutil
import signal
import socket
import ssl
import statistics
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parent.parent

# RFC 3977 section 3.2.1's 5xx replies a command may legitimately draw
# here: 500/501 for a command this node does not know or a malformed one,
# 502 for a permission refusal, 503 for a feature not supported.  Any other
# 5xx, or one of these to a command the node advertises, is recorded.
FIVE_XX_ALLOWED = {
    "XPAT": {"500", "501", "503"},
    "HDR": {"503"},
}


def now():
    return time.time()


def pct(values, q):
    if not values:
        return None
    ordered = sorted(values)
    at = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return round(ordered[at] * 1000.0, 2)          # milliseconds


class Events:
    """One JSON line per event; thread-safe."""

    def __init__(self, path: Path):
        self.path = path
        self.lock = threading.Lock()
        self.out = open(path, "a", encoding="utf-8")

    def emit(self, kind, **fields):
        row = dict(t=round(now(), 3), kind=kind, **fields)
        with self.lock:
            self.out.write(json.dumps(row, sort_keys=True, default=str) + "\n")
            self.out.flush()
        return row

    def close(self):
        self.out.close()


# --------------------------------------------------------------------------
# a client: one socket, buffered, TLS optional

class Gone(RuntimeError):
    """The connection closed or timed out: the answer is not known."""


class Client:
    def __init__(self, port, context=None, timeout=60.0, host="127.0.0.1"):
        raw = socket.create_connection((host, port), timeout=timeout)
        self.sock = context.wrap_socket(raw, server_hostname=host) if context else raw
        self.sock.settimeout(timeout)
        self.buf = b""
        self.greeting = self.line()

    def line(self):
        while b"\r\n" not in self.buf:
            try:
                chunk = self.sock.recv(65536)
            except (socket.timeout, OSError, ssl.SSLError) as error:
                raise Gone(str(error)) from error
            if not chunk:
                raise Gone("closed")
            self.buf += chunk
        out, self.buf = self.buf.split(b"\r\n", 1)
        return out.decode("utf-8", "replace")

    def send(self, text):
        data = text if isinstance(text, bytes) else text.encode()
        try:
            self.sock.sendall(data + b"\r\n")
        except (OSError, ssl.SSLError) as error:
            raise Gone(str(error)) from error

    def block(self):
        lines = []
        while True:
            one = self.line()
            if one == ".":
                return lines
            lines.append(one[1:] if one.startswith("..") else one)

    def cmd(self, text, multiline=False):
        self.send(text)
        status = self.line()
        body = self.block() if multiline and status[:1] in "12" else []
        return status, body

    def login(self, user, password):
        a, _ = self.cmd("AUTHINFO USER " + user)
        b, _ = self.cmd("AUTHINFO PASS " + password) if a.startswith("381") else (a, [])
        return b

    def post(self, octets: bytes):
        """(first, final): final None when the answer never came."""
        first, _ = self.cmd("POST")
        if not first.startswith("340"):
            return first, None
        stuffed = b"\r\n".join((b"." + l if l.startswith(b".") else l)
                               for l in octets.split(b"\r\n"))
        if not stuffed.endswith(b"\r\n"):
            stuffed += b"\r\n"
        try:
            self.sock.sendall(stuffed + b".\r\n")
        except (OSError, ssl.SSLError) as error:
            raise Gone(str(error)) from error
        return first, self.line()

    def close(self):
        try:
            self.send("QUIT")
            self.line()
        except Exception:                               # noqa: BLE001
            pass
        try:
            self.sock.close()
        except OSError:
            pass


# --------------------------------------------------------------------------
# a node

def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def scratch_ca(work: Path):
    """tools/reader_clients_phase.py's CA and server certificate for 127.0.0.1."""
    sys.path.insert(0, str(ROOT / "tools"))
    import reader_clients_phase                          # noqa: E402
    return reader_clients_phase.scratch_ca(work)


def proc_status(pid):
    out = {}
    try:
        for line in Path("/proc/{}/status".format(pid)).read_text().splitlines():
            key, _, value = line.partition(":")
            if key in ("VmRSS", "VmHWM", "VmSize", "Threads", "RssAnon", "RssFile"):
                out[key] = int(value.split()[0])
        out["fds"] = len(os.listdir("/proc/{}/fd".format(pid)))
        io = Path("/proc/{}/io".format(pid)).read_text().splitlines()
        for line in io:
            key, _, value = line.partition(":")
            if key in ("write_bytes", "syscw"):
                out[key] = int(value)
    except OSError as error:
        out["error"] = str(error)
    return out


class Node:
    """One native owner: its directory, config, store and process."""

    def __init__(self, image, work: Path, name, events: Events, tls=True, auth=True,
                 identity=None):
        self.image, self.name, self.events = Path(image), name, events
        self.dir = work / name
        self.dir.mkdir(parents=True, exist_ok=True)
        self.store = self.dir / "store"
        self.port, self.tls_port = free_port(), (free_port() if tls else 0)
        # sun_path is at most 108 octets: the control socket in a short dir.
        self.control = Path(tempfile.mkdtemp(prefix="fnfit-", dir="/tmp")) / "control.sock"
        self.config = self.dir / "fn.toml"
        self.log = self.dir / "fn.log"
        self.identity = identity or "{}.fitness.example.invalid".format(name)
        self.tls, self.auth = tls, auth
        self.ca = self.cert = self.key = None
        if tls:
            self.ca, self.cert, self.key = scratch_ca(self.dir)
        self.process = None
        self.stderr = None
        sys.path.insert(0, str(ROOT / "tools"))
        import native_env                                # noqa: E402
        # init sizes the profile against a budget; the harness stores name
        # hbox's at init (tools/native_env.py HARNESS_INIT_WORDS).
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.extra_env = {}
        self.write_config()

    def write_config(self, store=None):
        text = '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'.format(
            store or self.store, self.port)
        if self.tls:
            text += 'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n'.format(
                self.tls_port, self.cert, self.key)
        text += '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(self.control, self.log)
        if self.auth:
            text += '[auth]\nrequired = true\nprotected_only = true\n'
        self.config.write_text(text, encoding="ascii")

    def context(self):
        if not self.tls:
            return None
        ctx = ssl.create_default_context(cafile=str(self.ca))
        return ctx

    def op(self, *words, timeout=600, image=None):
        started = now()
        result = subprocess.run([str(image or self.image), "--fn", "operator", str(self.config),
                                 *map(str, words)], cwd=str(ROOT), env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        result.seconds = now() - started
        return result

    def fn(self, *words, timeout=3600):
        started = now()
        result = subprocess.run([str(self.image), "--fn", *map(str, words)], cwd=str(ROOT),
                                env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        result.seconds = now() - started
        return result

    def start(self, image=None, extra_env=None, timeout=1800):
        env = dict(self.env)
        env.update(self.extra_env)
        env.update(extra_env or {})
        self.stderr = open(self.dir / "owner.stderr", "ab")
        started = now()
        self.process = subprocess.Popen(
            [str(image or self.image), "--fn", "operator", str(self.config), "run"],
            cwd=str(ROOT), env=env, stdout=subprocess.PIPE, stderr=self.stderr, bufsize=0)
        want = 2 if self.tls else 1
        seen, buf = 0, b""
        deadline = now() + timeout
        fd = self.process.stdout.fileno()
        while seen < want and now() < deadline:
            if self.process.poll() is not None:
                break
            if select.select([fd], [], [], 5)[0]:
                chunk = os.read(fd, 4096)
                if not chunk:
                    break
                buf += chunk
                seen = buf.count(b"LISTENING")
        ready = now() - started
        if seen < want:
            code = self.process.poll()
            tail = (self.dir / "owner.stderr").read_bytes()[-1500:].decode("utf-8", "replace")
            self.events.emit("start-failed", node=self.name, exit=code, stdout=buf.decode(
                "utf-8", "replace")[-500:], stderr=tail, seconds=round(ready, 2))
            raise RuntimeError("{}: owner did not listen (exit {}): {}".format(
                self.name, code, tail[-400:]))
        # Drain stdout from here on, so the owner never blocks on a full pipe.
        threading.Thread(target=self._drain, args=(self.process,), daemon=True).start()
        self.events.emit("started", node=self.name, pid=self.process.pid,
                         seconds=round(ready, 2))
        return ready

    @staticmethod
    def _drain(process):
        try:
            while process.stdout.read(4096):
                pass
        except (OSError, ValueError):
            pass

    def pid(self):
        return self.process.pid if self.process and self.process.poll() is None else None

    def kill9(self):
        if self.pid():
            self.process.send_signal(signal.SIGKILL)
            self.process.wait(timeout=60)
            self.events.emit("killed", node=self.name, signal="KILL")

    def stop(self, timeout=300):
        if self.pid():
            self.process.send_signal(signal.SIGTERM)
            try:
                self.process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                self.events.emit("finding", node=self.name, what="SIGTERM did not stop the owner",
                                 seconds=timeout)
                self.process.kill()
                self.process.wait(timeout=60)
        code = self.process.returncode if self.process else None
        if self.stderr:
            self.stderr.close()
            self.stderr = None
        return code

    def account(self):
        """An invite redeemed over TLS: (login, password)."""
        invite = self.op("account", "invite", "--expires", "86400")
        codes = re.findall(rb"^[0-9a-f]{32}$", invite.stdout, re.M)
        if invite.returncode or len(codes) != 1:
            raise RuntimeError("account invite exited {}: {}".format(
                invite.returncode, (invite.stdout + invite.stderr)[-300:]))
        login, password = "fit-" + secrets.token_hex(4), secrets.token_hex(12)
        conn = Client(self.tls_port, self.context())
        first, _ = conn.cmd("XREDEEM {} {}".format(codes[0].decode(), login))
        second, _ = conn.cmd("XREDEEM PASS " + password)
        conn.close()
        if not second.startswith("2"):
            raise RuntimeError("XREDEEM: {} / {}".format(first, second))
        return login, password

    def session(self, creds=None, timeout=60.0):
        conn = Client(self.tls_port if self.tls else self.port, self.context(), timeout)
        if creds:
            reply = conn.login(*creds)
            if not reply.startswith("281"):
                conn.close()
                raise RuntimeError("AUTHINFO: " + reply)
        return conn


# --------------------------------------------------------------------------
# articles

WORDS = ("store news core acl2 bundle carry peer group reader poster octet journal "
         "barrier replay digest feed history article number cancel supersede path").split()


def rfc5322_now():
    return time.strftime("%a, %d %b %Y %H:%M:%S +0000", time.gmtime())


def make_article(msgid, groups, subject, body_octets, references=None, extra=()):
    rng = random.Random(msgid)
    lines = []
    while sum(len(l) + 2 for l in lines) < body_octets:
        # at most 72 columns: a reader quoting it (slrn's "> ") stays under
        # 80, which slrn refuses to post past (found by its reply here)
        line = ""
        for _ in range(rng.randint(6, 14)):
            word = rng.choice(WORDS)
            if len(line) + len(word) + 1 > 72:
                break
            line = (line + " " + word).strip()
        lines.append(line)
    if rng.random() < 0.2:
        lines.insert(rng.randint(0, len(lines)), ".a line that begins with a dot")
    head = ["From: fitness <fit@fitness.example.invalid>",
            "Newsgroups: " + ",".join(groups), "Subject: " + subject,
            "Date: " + rfc5322_now(), "Message-ID: " + msgid]
    if references:
        head.append("References: " + " ".join(references))
    head.extend(extra)
    return ("\r\n".join(head) + "\r\n\r\n" + "\r\n".join(lines) + "\r\n").encode()


# --------------------------------------------------------------------------
# shared state of a load run

class Ledger:
    """What the node told the posters, and the chaos windows."""

    def __init__(self):
        self.lock = threading.Lock()
        self.accepted = {}       # msgid -> (t, groups)
        self.refused = {}        # msgid -> (t, reply)
        self.uncertain = {}      # msgid -> (t, why)
        self.retracted = set()   # cancelled or superseded by this run
        self.windows = []        # (start, end, what): a disk event or a kill
        self.lat = {}            # command -> [seconds]
        self.codes = {}          # command -> {code: n}
        self.five = []           # unexpected 5xx rows
        self.told_uncertain = set()  # the node answered uncertain (not a lost reply)

    def note(self, command, seconds, status):
        with self.lock:
            self.lat.setdefault(command, []).append(seconds)
            code = (status or "none")[:3]
            self.codes.setdefault(command, {}).setdefault(code, 0)
            self.codes[command][code] += 1

    def in_window(self, t, slack=5.0):
        with self.lock:
            return any(a - slack <= t <= (b if b else now()) + slack for a, b, _ in self.windows)

    def open_window(self, what):
        with self.lock:
            self.windows.append([now(), None, what])
            return len(self.windows) - 1

    def close_window(self, index):
        with self.lock:
            self.windows[index][1] = now()


class Load:
    """POSTers and readers against one node, until stopped."""

    def __init__(self, node: Node, events: Events, ledger: Ledger, groups, posters, readers,
                 creds, seed=1):
        self.node, self.events, self.ledger = node, events, ledger
        self.groups, self.creds = groups, creds
        self.stop = threading.Event()
        self.paused = threading.Event()        # set while the node is down on purpose
        self.threads = []
        self.posters, self.readers = posters, readers
        self.rng = random.Random(seed)
        self.post_count = 0

    def start(self):
        for i in range(self.posters):
            t = threading.Thread(target=self.poster, args=(i,), daemon=True)
            t.start()
            self.threads.append(t)
        for i in range(self.readers):
            t = threading.Thread(target=self.reader, args=(i,), daemon=True)
            t.start()
            self.threads.append(t)

    def finish(self):
        self.stop.set()
        for t in self.threads:
            t.join(timeout=180)

    def connect(self, who):
        while not self.stop.is_set():
            if self.paused.is_set():
                time.sleep(0.5)
                continue
            try:
                started = now()
                conn = self.node.session(self.creds[who % len(self.creds)], timeout=90)
                self.ledger.note("CONNECT+AUTHINFO", now() - started, "281")
                return conn
            except Exception as error:                  # noqa: BLE001
                if not self.ledger.in_window(now()) and not self.paused.is_set():
                    self.events.emit("connect-failed", who=who, error=str(error)[:200])
                time.sleep(1.0)
        return None

    # ---- posters

    def poster(self, i):
        rng = random.Random(1000 + i)
        mine = []
        n = 0
        conn = None
        while not self.stop.is_set():
            if conn is None:
                conn = self.connect(i)
                if conn is None:
                    return
            n += 1
            msgid = "<fit-{}-{}-{}@fitness.example.invalid>".format(i, n, secrets.token_hex(3))
            groups = [rng.choice(self.groups)]
            if rng.random() < 0.1:
                groups.append(rng.choice(self.groups))
                groups = sorted(set(groups))
            refs, extra, kind = None, (), "post"
            if mine and rng.random() < 0.2:
                refs = [rng.choice(mine)]
            if mine and n % 25 == 0:
                target = mine.pop(rng.randrange(len(mine)))
                kind, extra = "cancel", ("Control: cancel " + target,)
                groups = ["control.cancel"] if "control.cancel" in self.groups else groups
            elif mine and n % 40 == 0:
                target = mine.pop(rng.randrange(len(mine)))
                kind, extra = "supersede", ("Supersedes: " + target,)
            else:
                target = None
            octets = make_article(msgid, groups, "fitness {} {}".format(kind, n),
                                  rng.randint(1200, 3200), refs, extra)
            started = now()
            try:
                first, final = conn.post(octets)
            except Gone as error:
                self.ledger.note("POST", now() - started, None)
                with self.ledger.lock:
                    self.ledger.uncertain[msgid] = (started, str(error)[:120])
                    if target:
                        # the cancel or supersede may have been stored
                        self.ledger.retracted.add(target)
                self.events.emit("post-uncertain", msgid=msgid, why=str(error)[:120],
                                 in_window=self.ledger.in_window(started))
                conn = None
                continue
            took = now() - started
            status = final or first
            self.ledger.note("POST", took, status)
            if "uncertain" in status:
                # the node's own uncertain answer (a disk stall past H): a
                # disk event by construction; its presence is checked later
                with self.ledger.lock:
                    self.ledger.uncertain[msgid] = (started, status[:120])
                    self.ledger.told_uncertain.add(msgid)
                    if target:
                        self.ledger.retracted.add(target)
                self.events.emit("post-told-uncertain", msgid=msgid, reply=status)
            elif status.startswith("240"):
                with self.ledger.lock:
                    self.ledger.accepted[msgid] = (now(), groups)
                    self.post_count += 1
                    if target:
                        self.ledger.retracted.add(target)
                if kind == "post":
                    mine.append(msgid)
                    if len(mine) > 200:
                        mine.pop(0)
                if kind != "post":
                    self.events.emit(kind, msgid=msgid, target=target, reply=status)
            else:
                with self.ledger.lock:
                    self.ledger.refused[msgid] = (now(), status)
                if status[:1] == "5":
                    self.five("POST", status)
                self.events.emit("post-refused", msgid=msgid, post_kind=kind, reply=status,
                                 in_window=self.ledger.in_window(started))
        if conn:
            conn.close()

    def five(self, command, status):
        verb = command.split()[0].upper()
        if status[:3] not in FIVE_XX_ALLOWED.get(verb, set()):
            with self.ledger.lock:
                self.ledger.five.append((now(), command, status))
            self.events.emit("unexpected-5xx", command=command, reply=status)

    # ---- readers

    def timed(self, conn, command, multiline=False, name=None):
        started = now()
        status, body = conn.cmd(command, multiline)
        self.ledger.note(name or command.split()[0].upper(), now() - started, status)
        if status[:1] == "5":
            self.five(command, status)
        return status, body

    def reader(self, i):
        rng = random.Random(2000 + i)
        conn = None
        while not self.stop.is_set():
            if conn is None:
                conn = self.connect(100 + i)
                if conn is None:
                    return
            try:
                self.read_round(conn, rng)
            except Gone as error:
                if not self.ledger.in_window(now()) and not self.paused.is_set():
                    self.events.emit("reader-gone", who=i, error=str(error)[:200])
                conn = None

    def read_round(self, conn, rng):
        group = rng.choice([g for g in self.groups if g != "control.cancel"])
        with self.ledger.lock:
            known = [m for m, (t, g) in self.ledger.accepted.items()
                     if m not in self.ledger.retracted] if rng.random() < 0.3 else []
            cutoff = now()
        status, _ = self.timed(conn, "GROUP " + group)
        if not status.startswith("211"):
            return
        count, low, high = (int(x) for x in status.split()[1:4])
        if high >= low and count:
            number = rng.randint(low, high)
            self.timed(conn, "ARTICLE {}".format(number), True)
            start = max(low, high - 50)
            self.timed(conn, "OVER {}-{}".format(start, high), True)
            self.timed(conn, "HDR Subject {}-{}".format(start, high), True)
            self.timed(conn, "XPAT Subject {}-{} *fitness*".format(start, high), True)
            self.timed(conn, "LISTGROUP {} {}-{}".format(group, start, high), True,
                       name="LISTGROUP")
        if known:
            msgid = rng.choice(known)
            with self.ledger.lock:
                t, _ = self.ledger.accepted.get(msgid, (0, None))
            if t and t < cutoff:
                status, _ = self.timed(conn, "STAT " + msgid)
                if status.startswith("430"):
                    with self.ledger.lock:
                        retracted = msgid in self.ledger.retracted
                    if not retracted:
                        self.events.emit("finding", what="acknowledged article not found",
                                         msgid=msgid, acked=t, reply=status)
        time.sleep(rng.uniform(0.0, 0.2))


# --------------------------------------------------------------------------
# measurement helpers

class FsyncCounter:
    """bpftrace (sudo) counting fsync/fdatasync/sync_file_range by the owner's PID."""

    def __init__(self, pid, seconds):
        self.pid, self.seconds = pid, seconds

    def run(self):
        prog = ('tracepoint:syscalls:sys_enter_fsync,tracepoint:syscalls:sys_enter_fdatasync,'
                'tracepoint:syscalls:sys_enter_sync_file_range /pid == %d/ { @n = count(); } '
                'interval:s:%d { exit(); }' % (self.pid, self.seconds))
        try:
            out = subprocess.run(["sudo", "-n", "bpftrace", "-e", prog], stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=self.seconds + 60, check=False)
        except (OSError, subprocess.TimeoutExpired) as error:
            return None, str(error)
        match = re.search(rb"@n: (\d+)", out.stdout)
        return (int(match.group(1)) if match else 0), out.stderr.decode()[-200:]


def sample(node: Node, load: Load, ledger: Ledger, events: Events, fsync_seconds=30):
    pid = node.pid()
    if not pid:
        return None
    before = load.post_count
    counter = FsyncCounter(pid, fsync_seconds)
    fsyncs, err = counter.run()
    posts = load.post_count - before
    started = now()
    status = node.op("status", timeout=120)
    status_s = now() - started
    health = node.op("health", timeout=120)
    with ledger.lock:
        lat = {k: list(v) for k, v in ledger.lat.items()}
        codes = json.loads(json.dumps(ledger.codes))
        ledger.lat = {}
    try:
        pressure = Path("/proc/pressure/io").read_text().split()
        io_some = float(pressure[1].split("=")[1])
        io_full = float([w for w in pressure if w.startswith("avg10=")][1].split("=")[1])
    except (OSError, IndexError, ValueError):
        io_some = io_full = None
    row = dict(proc_status(pid), pid=pid, io_pressure_some10=io_some, io_pressure_full10=io_full,
               fsyncs=fsyncs, fsync_window_posts=posts,
               fsyncs_per_post=(round(fsyncs / posts, 3) if fsyncs is not None and posts else None),
               fsync_note=err if fsyncs is None else "",
               post_p50=pct(lat.get("POST", []), 0.5), post_p99=pct(lat.get("POST", []), 0.99),
               article_p50=pct(lat.get("ARTICLE", []), 0.5),
               login_p50=pct(lat.get("CONNECT+AUTHINFO", []), 0.5),
               login_max=pct(lat.get("CONNECT+AUTHINFO", []), 1.0),
               over_p50=pct(lat.get("OVER", []), 0.5), group_p50=pct(lat.get("GROUP", []), 0.5),
               status_s=round(status_s, 3), status_rc=status.returncode,
               health_rc=health.returncode,
               health=health.stdout.decode("utf-8", "replace")[-600:],
               n={k: len(v) for k, v in lat.items()}, codes=codes,
               accepted=len(ledger.accepted), refused=len(ledger.refused),
               uncertain=len(ledger.uncertain))
    events.emit("sample", **row)
    return row


# --------------------------------------------------------------------------
# the soak

def copy_fixture(fixture: Path, node: Node):
    src = fixture / "store"
    if node.store.exists():
        shutil.rmtree(node.store)
    subprocess.run(["cp", "-a", "--reflink=auto", str(src), str(node.store)], check=True)
    lock = node.store / "writer.lock"
    lock.touch()
    lock.chmod(0o600)
    rebind = node.fn("store", node.store, "rebind-filesystem")
    node.events.emit("fixture", fixture=str(fixture), rebind_rc=rebind.returncode,
                     rebind=(rebind.stdout + rebind.stderr).decode("utf-8", "replace")[-300:])


def live_sample_replies(node, creds, groups, rng, n=200):
    """ARTICLE and OVER replies to compare across a restart."""
    out = {}
    conn = node.session(creds)
    for group in groups:
        if group == "control.cancel":
            continue
        status, _ = conn.cmd("GROUP " + group)
        if not status.startswith("211"):
            continue
        count, low, high = (int(x) for x in status.split()[1:4])
        if not count:
            continue
        for number in sorted({rng.randint(low, high) for _ in range(n // len(groups))}):
            s, body = conn.cmd("ARTICLE {}".format(number), True)
            out["{} ARTICLE {}".format(group, number)] = hashlib.sha256(
                (s + "\n" + "\n".join(body)).encode()).hexdigest()
        s, body = conn.cmd("OVER {}-{}".format(max(low, high - 100), high), True)
        out["{} OVER tail".format(group)] = hashlib.sha256(
            (s + "\n" + "\n".join(body)).encode()).hexdigest()
    conn.close()
    return out


def replay_again(node, creds, keys):
    conn = node.session(creds)
    out = {}
    current = None
    for key in keys:
        group, verb, rest = key.split(" ", 2)
        if group != current:
            conn.cmd("GROUP " + group)
            current = group
        if verb == "ARTICLE":
            s, body = conn.cmd("ARTICLE " + rest, True)
        else:
            status, _ = conn.cmd("GROUP " + group)
            s, body = "", []
            # the tail is re-read with the SAME range as before: the key keeps it
        out[key] = hashlib.sha256((s + "\n" + "\n".join(body)).encode()).hexdigest()
    conn.close()
    return out


def pipelined_stat(conn, msgids, batch=100):
    """STAT each Message-ID, BATCH commands written before their replies are
    read (RFC 3977 section 3.5 pipelining): {msgid: status line}."""
    out = {}
    for at in range(0, len(msgids), batch):
        chunk = msgids[at:at + batch]
        try:
            conn.sock.sendall(b"".join(("STAT " + m + "\r\n").encode() for m in chunk))
        except (OSError, ssl.SSLError) as error:
            raise Gone(str(error)) from error
        for m in chunk:
            out[m] = conn.line()
    return out


def verify_presence(node, creds, ledger: Ledger, events: Events, label, limit=None):
    """Every acknowledged article is there; nothing refused is served."""
    conn = node.session(creds, timeout=120)
    missing, served_refused, uncertain_present = [], [], 0
    with ledger.lock:
        accepted = [m for m in ledger.accepted if m not in ledger.retracted]
        refused = list(ledger.refused)
        uncertain = list(ledger.uncertain)
    if limit and len(accepted) > limit:
        accepted = random.Random(label).sample(accepted, limit)
    stat = pipelined_stat(conn, accepted + refused + uncertain)
    for msgid in accepted:
        if not stat[msgid].startswith("223"):
            missing.append((msgid, stat[msgid]))
    for msgid in refused:
        if stat[msgid].startswith("223"):
            served_refused.append(msgid)
    for msgid in uncertain:
        uncertain_present += stat[msgid].startswith("223") or stat[msgid].startswith("430 withdrawn")
    conn.close()
    row = events.emit("presence", label=label, checked=len(accepted), missing=len(missing),
                      missing_ids=missing[:20], refused_checked=len(refused),
                      refused_served=len(served_refused), refused_served_ids=served_refused[:20],
                      uncertain=len(uncertain), uncertain_present=uncertain_present)
    if missing:
        events.emit("finding", what="acknowledged articles missing after " + label,
                    count=len(missing), ids=missing[:10])
    if served_refused:
        events.emit("finding", what="refused articles served after " + label,
                    count=len(served_refused), ids=served_refused[:10])
    return row


def reader_client_session(node: Node, events: Events, work: Path, clients="slrn"):
    """tools/reader_clients_phase.py --attach against this running node."""
    out = work / "clients-{}".format(int(now()))
    out.mkdir(parents=True, exist_ok=True)
    for name in ("ca.pem", "node.pem", "node.key"):
        shutil.copy2(node.dir / name, out / name)
    started = now()
    result = subprocess.run(
        [sys.executable, str(ROOT / "tools" / "reader_clients_phase.py"), "--image",
         str(node.image), "--work", str(out), "--clients", clients, "--group", "fit.general",
         "--second-group", "fit.crosspost", "--attach-config", str(node.config),
         "--attach-tls-port", str(node.tls_port), "--container", "fn-reader-clients-fitness"],
        cwd=str(ROOT), stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=1800, check=False)
    text = result.stdout.decode("utf-8", "replace").strip()
    try:
        report = json.loads(text.splitlines()[-1]) if text else {}
    except ValueError:
        report = {"raw": text[-800:]}
    rows = {}
    for client, entry in (report.get("clients") or {}).items():
        rows[client] = {"error": entry.get("error"), "driver_exit": entry.get("driver_exit"),
                        "outcomes": entry.get("outcomes"), "check": entry.get("check")}
    events.emit("reader-client", seconds=round(now() - started, 1), exit=result.returncode,
                clients=rows, error=report.get("error"),
                stderr=result.stderr.decode("utf-8", "replace")[-400:])
    return report


GROUPS = ["fn.test", "fit.general", "fit.crosspost", "fit.alpha", "fit.beta", "control.cancel"]


def prepare(node: Node, events: Events, fixture=None, groups=GROUPS, profile=()):
    if fixture:
        copy_fixture(Path(fixture), node)
    else:
        # init names a few groups and `group create' the rest, so the run
        # exercises the live admin path too (PKT-867 removed the argv word
        # bound that first forced this split).
        first, rest = list(groups[:4]), list(groups[4:])
        import native_env                                # noqa: E402
        init = node.op("init", *native_env.HARNESS_INIT_WORDS, *profile, *first)
        events.emit("init", node=node.name, rc=init.returncode,
                    out=(init.stdout + init.stderr).decode("utf-8", "replace")[-400:])
        if init.returncode:
            raise RuntimeError("init: " + init.stderr.decode()[-400:])
        for group in rest:
            made = node.op("group", "create", group)
            if made.returncode:
                raise RuntimeError("group create {}: {}".format(group, made.stderr.decode()[-300:]))


def ensure_groups(node, events, groups):
    for group in groups:
        made = node.op("group", "create", group)
        events.emit("group-create", node=node.name, group=group, rc=made.returncode,
                    out=(made.stdout + made.stderr).decode("utf-8", "replace")[-200:])


def digest_check(node: Node, events: Events, label):
    """`store digest' of the store as left, against a full replay of its log.

    While the log still holds segment 1, the replay is a copy with the
    checkpoint removed, and the two digests must agree.  After a compaction
    (the owner's automatic checkpoint or `store compact') dropped the
    segments the checkpoint covers, a copy without its checkpoint is not a
    replay: the open must refuse it by name (reason=checkpoint-damaged,
    books/store-log-segments.lisp) and `health' must say so; the digest is
    then compared with a second open of an identical copy."""
    first = node.fn("store", node.store, "digest")
    copy = node.dir / "digest-copy"
    if copy.exists():
        shutil.rmtree(copy)
    subprocess.run(["cp", "-a", "--reflink=auto", str(node.store), str(copy)], check=True)
    # the copy lives on another filesystem than a tmpfs-mounted store: bind it
    node.fn("store", copy, "rebind-filesystem")
    compacted = not (node.store / "journal" / "000001.log").exists()
    twin = node.fn("store", copy, "digest") if compacted else None
    dropped = []
    for path in copy.glob("store-checkpoint*"):
        dropped.append(path.name)
        if path.is_dir():
            shutil.rmtree(path)
        else:
            path.unlink()
    second = node.fn("store", copy, "digest")
    health = None
    if compacted:
        cfg = node.dir / "digest-copy.toml"
        cfg.write_text('[store]\npath = "{}"\n'.format(copy), encoding="ascii")
        h = node.fn("operator", cfg, "health")
        health = [h.returncode, (h.stdout + h.stderr).decode("utf-8", "replace")[-600:]]
    journal = node.fn("store", node.store, "journal")

    def digests(text):
        return sorted(set(re.findall(r"[0-9a-f]{64}", text)))

    a = first.stdout.decode("utf-8", "replace")
    b = second.stdout.decode("utf-8", "replace")
    err_b = second.stderr.decode("utf-8", "replace")
    if compacted:
        t = twin.stdout.decode("utf-8", "replace")
        same = first.returncode == 0 and twin.returncode == 0 and digests(a) == digests(t)
        refused_by_name = second.returncode == 1 and "reason=checkpoint-damaged" in err_b
        health_names_it = bool(health and "checkpoint-damaged" in health[1])
    else:
        same = digests(a) == digests(b) and first.returncode == 0 and second.returncode == 0
        refused_by_name = health_names_it = None
    row = events.emit("digest", label=label, compacted=compacted,
                      rc=[first.returncode, second.returncode],
                      seconds=[round(first.seconds, 1), round(second.seconds, 1)],
                      dropped=dropped, same=same, refused_by_name=refused_by_name,
                      health=health, health_names_it=health_names_it,
                      first=a[-700:], second=(b or err_b)[-700:],
                      journal_rc=journal.returncode,
                      journal=journal.stdout.decode("utf-8", "replace")[-400:],
                      errs=(first.stderr + second.stderr).decode("utf-8", "replace")[-400:])
    shutil.rmtree(copy, ignore_errors=True)
    if journal.returncode != 0:
        events.emit("finding", what="store journal: the decision journal does not replay",
                    label=label, journal=journal.stdout.decode("utf-8", "replace")[-300:])
    if not same:
        events.emit("finding", what="store digest: two opens of one history disagree",
                    label=label, compacted=compacted)
    if compacted and not refused_by_name:
        events.emit("finding", what="a compacted store without its checkpoint was not refused "
                    "by name", label=label, rc=second.returncode, err=err_b[-300:])
    if compacted and not health_names_it:
        events.emit("finding", what="health does not name checkpoint-damaged on a compacted "
                    "store without its checkpoint", label=label, health=health)
    return row


def starttls_session(node: Node, creds, events: Events):
    """The clear port as a reader that upgrades (RFC 4642): CAPABILITIES,
    STARTTLS, AUTHINFO, POST, a reply with References, a cancel of its own
    article; each reply line recorded."""
    rows = []
    try:
        conn = Client(node.port, None, 60)
        rows.append(("greeting", conn.greeting))
        s, caps = conn.cmd("CAPABILITIES", True)
        rows.append(("CAPABILITIES", s + " " + " ".join(caps)))
        s, _ = conn.cmd("AUTHINFO USER " + creds[0])
        rows.append(("AUTHINFO before STARTTLS", s))
        s, _ = conn.cmd("STARTTLS")
        rows.append(("STARTTLS", s))
        if s.startswith("382"):
            conn.sock = node.context().wrap_socket(conn.sock, server_hostname="127.0.0.1")
            conn.buf = b""
            rows.append(("AUTHINFO", conn.login(*creds)))
            mid = "<starttls-{}@fitness.example.invalid>".format(secrets.token_hex(4))
            first, final = conn.post(make_article(mid, ["fit.general"], "over starttls", 400))
            rows.append(("POST", final or first))
            reply = "<starttls-re-{}@fitness.example.invalid>".format(secrets.token_hex(4))
            first, final = conn.post(make_article(reply, ["fit.general"], "Re: over starttls",
                                                  300, [mid]))
            rows.append(("POST reply", final or first))
            s, head = conn.cmd("HEAD " + reply, True)
            rows.append(("HEAD reply References", next((h for h in head if h.lower().startswith(
                "references:")), s)))
            cancel = "<starttls-cancel-{}@fitness.example.invalid>".format(secrets.token_hex(4))
            first, final = conn.post(make_article(cancel, ["control.cancel"], "cmsg cancel " + mid,
                                                  50, extra=("Control: cancel " + mid,)))
            rows.append(("POST cancel", final or first))
            s, _ = conn.cmd("STAT " + mid)
            rows.append(("STAT cancelled", s))
        conn.close()
    except Exception as error:                          # noqa: BLE001
        rows.append(("error", "{}: {}".format(type(error).__name__, error)))
    events.emit("starttls", rows=rows)
    return rows


def overview_consistency(node: Node, creds, events: Events, groups, per_group=40):
    """OVER, HDR and XPAT against HEAD of the same articles (RFC 3977 8.3-8.5,
    RFC 2980 XPAT): every field the overview names equals the header."""
    conn = node.session(creds, timeout=120)
    checked, bad = 0, []
    for group in groups:
        s, _ = conn.cmd("GROUP " + group)
        if not s.startswith("211"):
            continue
        _, low, high = (int(x) for x in s.split()[1:4])
        lo = max(low, high - per_group)
        s, over = conn.cmd("OVER {}-{}".format(lo, high), True)
        s2, hdr = conn.cmd("HDR Subject {}-{}".format(lo, high), True)
        s3, xpat = conn.cmd("XPAT Subject {}-{} *fitness*".format(lo, high), True)
        hdr_map = dict(l.split(" ", 1) for l in hdr if " " in l)
        xpat_set = {l.split(" ", 1)[0] for l in xpat}
        for line in over:
            f = line.split("\t")
            if len(f) < 8:
                bad.append((group, "short OVER line", line[:80]))
                continue
            n = f[0]
            hs, head = conn.cmd("HEAD " + n, True)
            if not hs.startswith("221"):
                continue
            h = {}
            for l in head:
                k, _, v = l.partition(":")
                h.setdefault(k.lower(), v.strip())
            checked += 1
            for idx, key in ((1, "subject"), (2, "from"), (3, "date"), (4, "message-id"),
                             (5, "references")):
                if f[idx] != h.get(key, ""):
                    bad.append((group, n, key, f[idx][:60], h.get(key, "")[:60]))
            if hdr_map.get(n, None) != h.get("subject", ""):
                bad.append((group, n, "HDR Subject", hdr_map.get(n), h.get("subject")))
            if ("fitness" in h.get("subject", "")) != (n in xpat_set):
                bad.append((group, n, "XPAT", n in xpat_set, h.get("subject")))
    conn.close()
    events.emit("overview-consistency", checked=checked, bad=len(bad), rows=bad[:30])
    if bad:
        events.emit("finding", what="OVER/HDR/XPAT disagree with HEAD", count=len(bad),
                    rows=bad[:10])
    return checked, bad


def cmd_soak(args):
    work = Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    events = Events(work / "events.jsonl")
    ledger = Ledger()
    rng = random.Random(args.seed)
    node = Node(args.image, work, "soak", events)
    summary = {"image": args.image, "fixture": args.fixture, "minutes": args.minutes,
               "chaos": args.chaos, "started": now()}
    mount = None
    try:
        if args.disk_full_mb:
            mount = mount_tmpfs(node, args.disk_full_mb, events)
        prepare(node, events, args.fixture, profile=args.init_flag or PAIR_PROFILE)
        image_for_run = args.developer if args.chaos and args.developer else args.image
        stall = work / "stall"
        extra = {"FN_NATIVE_TEST_DISK_STALL_FILE": str(stall)} if args.chaos else {}
        node.extra_env.update(extra)
        ready = node.start(image=image_for_run)
        summary["first_open_s"] = round(ready, 2)
        ensure_groups(node, events, [g for g in GROUPS if g != "fn.test"])
        for slot, value in args.policy or ():
            r = node.op("policy", "set", slot, value)
            events.emit("policy", slot=slot, value=value, rc=r.returncode)
        creds = [node.account() for _ in range(4)]
        load = Load(node, events, ledger, [g for g in GROUPS], args.posters, args.readers,
                    creds, seed=args.seed)
        load.start()
        t0 = now()
        end = t0 + args.minutes * 60
        next_sample = t0 + 60                           # a first sample after warm-up
        next_client = t0 + args.client_minutes * 60 if args.client_minutes else float("inf")
        checkpoint_at = t0 + args.minutes * 60 * 0.4
        compact_at = t0 + args.minutes * 60 * 0.6
        chaos = plan_chaos(args, t0, end, rng) if args.chaos else []
        events.emit("plan", chaos=[(round(t - t0), what) for t, what in chaos])
        samples = []
        while now() < end:
            if now() >= next_sample:
                row = sample(node, load, ledger, events)
                if row:
                    samples.append(row)
                next_sample += args.sample_minutes * 60
            if now() >= next_client:
                try:
                    reader_client_session(node, events, work, args.clients)
                except Exception as error:              # noqa: BLE001
                    events.emit("reader-client", error="{}: {}".format(
                        type(error).__name__, str(error)[:300]))
                next_client += args.client_minutes * 60
            if checkpoint_at and now() >= checkpoint_at:
                # `store checkpoint' and `store compact' open the store as
                # `recover' does: refused while the owner runs (documented,
                # docs/operator-internals.md); the running owner checkpoints
                # itself at half the profile's K.  Recorded once, then the
                # compaction is a maintenance window: stop, compact, start.
                timed_op(node, events, "checkpoint-live", "store", "checkpoint")
                checkpoint_at = None
            if compact_at and now() >= compact_at:
                maintenance(node, load, ledger, events, creds, image_for_run)
                compact_at = None
            if chaos and now() >= chaos[0][0]:
                _, what = chaos.pop(0)
                run_chaos(what, node, load, ledger, events, creds, stall, image_for_run, work,
                          rng)
            time.sleep(1.0)
        load.finish()
        row = sample(node, load, ledger, events)
        if row:
            samples.append(row)
        verify_presence(node, creds[0], ledger, events, "end-live", limit=args.presence_limit)
        overview_consistency(node, creds[0], events, [g for g in GROUPS if g != "control.cancel"])
        starttls_session(node, creds[1], events)
        replies = live_sample_replies(node, creds[0], [g for g in GROUPS], rng)
        stop_rc = node.stop()
        events.emit("stopped", rc=stop_rc)
        digest_check(node, events, "end")
        node.start(image=image_for_run)
        again = replay_again(node, creds[0], [k for k in replies if " ARTICLE " in k])
        differ = [k for k in again if again[k] != replies[k]]
        events.emit("restart-replies", compared=len(again), differ=len(differ), keys=differ[:20])
        if differ:
            events.emit("finding", what="replies differ across a restart", count=len(differ),
                        keys=differ[:10])
        verify_presence(node, creds[0], ledger, events, "end-restart", limit=args.presence_limit)
        node.stop()
        summary["samples"] = samples
        summary["posts_accepted"] = len(ledger.accepted)
        summary["posts_refused"] = len(ledger.refused)
        summary["posts_uncertain"] = len(ledger.uncertain)
        stalls = disk_lines(node)
        summary["disk_lines"] = {k: len(v) for k, v in stalls.items()}
        summary["told_uncertain"] = len(ledger.told_uncertain)
        summary["uncertain_outside_window"] = [
            m for m, (t, _) in ledger.uncertain.items()
            if not ledger.in_window(t) and not (m in ledger.told_uncertain and stalls["stalled"])]
        summary["unexpected_5xx"] = ledger.five[:50]
        summary["codes"] = ledger.codes
        summary["windows"] = ledger.windows
        summary["rss_kb"] = [s.get("VmRSS") for s in samples]
        summary["auto_checkpoints"] = auto_checkpoints(node)
    finally:
        if node.pid():
            node.stop()
        if mount:
            # keep the store (and its decision journal) past the unmount
            subprocess.run(["cp", "-a", str(node.store), str(node.dir / "store-kept")])
            unmount_tmpfs(mount, events)
        summary["ended"] = now()
        findings = [json.loads(l) for l in (work / "events.jsonl").read_text().splitlines()
                    if '"kind": "finding"' in l or '"kind": "unexpected-5xx"' in l]
        summary["findings"] = findings[:200]
        (work / "summary.json").write_text(json.dumps(summary, indent=1, default=str))
        events.close()
    print(json.dumps({k: summary.get(k) for k in (
        "posts_accepted", "posts_refused", "posts_uncertain", "rss_kb")}, default=str))
    return 0


def maintenance(node, load, ledger, events, creds, image):
    """Stop the owner, `store compact', start it: the offline window."""
    window = ledger.open_window("maintenance")
    load.paused.set()
    started = now()
    rc = node.stop()
    stopped = now() - started
    compact = timed_op(node, events, "compact", "store", "compact")
    ready = node.start(image=image)
    ledger.close_window(window)
    load.paused.clear()
    events.emit("maintenance", stop_rc=rc, stop_s=round(stopped, 2),
                compact_rc=compact.returncode, compact_s=round(compact.seconds, 2),
                start_s=round(ready, 2), total_s=round(now() - started, 2))
    verify_presence(node, creds[0], ledger, events, "maintenance", limit=3000)


def disk_lines(node):
    """The node's own disk events in its service log: slow, stalled, recovered."""
    out = {"slow": [], "stalled": [], "recovered": []}
    try:
        for line in node.log.read_text(errors="replace").splitlines():
            for key in out:
                if line.startswith("disk " + key):
                    out[key].append(line)
    except OSError:
        pass
    return out


def auto_checkpoints(node):
    try:
        text = (node.dir / "owner.stderr").read_text(errors="replace")
    except OSError:
        return []
    return [l for l in text.splitlines() if l.startswith("CHECKPOINT")]


def timed_op(node, events, label, *words):
    result = node.op(*words, timeout=3600)
    events.emit("operator", label=label, words=words, rc=result.returncode,
                seconds=round(result.seconds, 2),
                out=(result.stdout + result.stderr).decode("utf-8", "replace")[-600:])
    return result


# --------------------------------------------------------------------------
# chaos

def plan_chaos(args, t0, end, rng):
    span = end - t0
    points = []
    for _ in range(args.kills):
        points.append((t0 + rng.uniform(0.05, 0.95) * span, "kill"))
    for _ in range(args.stalls):
        points.append((t0 + rng.uniform(0.05, 0.95) * span, "stall"))
    if args.torn:
        points.append((t0 + rng.uniform(0.3, 0.7) * span, "torn"))
    if args.disk_full_mb:
        points.append((t0 + 0.85 * span, "full"))
    points.sort()
    # at least 90 s between events so each recovery is measured alone
    spaced, last = [], 0
    for t, what in points:
        t = max(t, last + 90)
        spaced.append((t, what))
        last = t
    return spaced


def health_words(node):
    """(exit, the state line, the disk line and the first held state) of `health'."""
    r = node.op("health", timeout=120)
    lines = r.stdout.decode("utf-8", "replace").splitlines()
    keep = [l for l in lines if l.startswith(("health ", "disk ")) or " held" in l]
    return r.returncode, "\n".join(keep)[-500:]


def restart_after(node, load, ledger, events, creds, image, label, window):
    started = now()
    try:
        ready = node.start(image=image)
    except RuntimeError as error:
        events.emit("finding", what="owner did not restart after " + label, error=str(error)[-500:])
        raise
    ledger.close_window(window)
    rc, words = health_words(node)
    events.emit("recovered", label=label, seconds_to_listening=round(ready, 2),
                total_seconds=round(now() - started, 2), health_rc=rc, health=words)
    load.paused.clear()
    verify_presence(node, creds[0], ledger, events, label, limit=3000)


def run_chaos(what, node, load, ledger, events, creds, stall, image, work, rng):
    events.emit("chaos", what=what)
    if what == "kill":
        window = ledger.open_window("kill")
        load.paused.set()
        node.kill9()
        restart_after(node, load, ledger, events, creds, image, "kill", window)
    elif what == "torn":
        window = ledger.open_window("torn")
        load.paused.set()
        node.kill9()
        tear_tail(node, events)
        restart_after(node, load, ledger, events, creds, image, "torn", window)
    elif what == "stall":
        window = ledger.open_window("stall")
        stall.write_bytes(b"")
        seen = []
        for _ in range(12):
            time.sleep(5)
            rc, words = health_words(node)
            seen.append((rc, words))
        stall.unlink()
        time.sleep(5)
        ledger.close_window(window)
        rc, words = health_words(node)
        events.emit("stall-done", health_during=seen, health_after=[rc, words])
    elif what == "full":
        fill_disk(node, events, ledger, load, creds, image)


def tear_tail(node, events):
    """A torn PENDING write after the log's tail (log_damage's torn tail, placed
    where a crash can put it): the first half of the last entry's octets copied
    into the units after it, as the next entry's write interrupted.  Zeroing
    the last entry itself (as tests/test_native_log_damage.py does on a store
    with no clients) destroys an entry the node has fsynced and acknowledged:
    no power loss produces that, and the first version of this driver did
    it, and read its own damage as a lost article (lane fitness, 2026-09-28)."""
    segments = sorted((node.store / "journal").glob("*.log"))
    if not segments:
        events.emit("torn", error="no segment")
        return
    path = segments[-1]
    data = bytearray(path.read_bytes())
    starts = [q for q in range(0, len(data), 4096) if data[q:q + 4] == b"FNLG"]
    if not starts:
        events.emit("torn", error="no entry", segment=path.name)
        return
    last = starts[-1]
    try:
        end = data.index(b"\x00" * 64, last + 64)
    except ValueError:
        end = len(data)
    size = end - last
    at = last + ((size + 4095) // 4096) * 4096        # the next unit
    debris = bytes(data[last:last + size // 2])
    if at + len(debris) > len(data):
        data.extend(bytes(at + len(debris) - len(data)))
    data[at:at + len(debris)] = debris
    path.write_bytes(bytes(data))
    events.emit("torn", segment=path.name, last_entry_at=last, debris_at=at,
                debris_octets=len(debris))


def mount_tmpfs(node, megabytes, events):
    """A size-limited tmpfs (sudo) at DIR/vol, owned by us; the store is
    DIR/vol/store (init and the fixture copy create it, as they must)."""
    target = node.dir / "vol"
    target.mkdir(parents=True, exist_ok=True)
    r = subprocess.run(["sudo", "-n", "mount", "-t", "tmpfs", "-o",
                        "size={}m,uid={},gid={},mode=0700".format(megabytes, os.getuid(),
                                                                  os.getgid()),
                        "tmpfs", str(target)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    events.emit("tmpfs", target=str(target), megabytes=megabytes, rc=r.returncode,
                err=r.stderr.decode()[-200:])
    if r.returncode:
        raise RuntimeError("mount tmpfs: " + r.stderr.decode())
    node.store = target / "store"
    node.write_config()
    return target


def unmount_tmpfs(target, events):
    r = subprocess.run(["sudo", "-n", "umount", str(target)], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
    events.emit("tmpfs-umount", rc=r.returncode, err=r.stderr.decode()[-200:])


def fill_disk(node, events, ledger, load, creds, image):
    """Fill the store's filesystem to within a few KiB, watch, free, recover."""
    window = ledger.open_window("full")
    ballast = node.store.parent / ".fitness-ballast"
    st = os.statvfs(node.store)
    free = st.f_bavail * st.f_frsize
    keep = 64 * 1024
    with open(ballast, "wb") as out:
        left = max(0, free - keep)
        chunk = b"\0" * (1 << 20)
        try:
            while left > 0:
                out.write(chunk[:min(len(chunk), left)])
                left -= min(len(chunk), left)
        except OSError as error:
            events.emit("ballast", note=str(error))
    before = ledger.codes.get("POST", {}).copy()
    seen = []
    for _ in range(12):
        time.sleep(5)
        rc, words = health_words(node)
        seen.append((rc, words.splitlines()[0] if words else "", node.pid() is not None))
    after = ledger.codes.get("POST", {}).copy()
    events.emit("disk-full", free_before=free, health_during=seen, post_codes_before=before,
                post_codes_after=after, owner_alive=node.pid() is not None)
    ballast.unlink()
    if node.pid() is None:
        load.paused.set()
        restart_after(node, load, ledger, events, creds, image, "full", window)
    else:
        time.sleep(10)
        ledger.close_window(window)
        rc, words = health_words(node)
        events.emit("disk-full-freed", health=[rc, words])
        verify_presence(node, creds[0], ledger, events, "full", limit=3000)


# --------------------------------------------------------------------------
# memory at scale (f6)

def cmd_memory(args):
    work = Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    events = Events(work / "events.jsonl")
    node = Node(args.image, work, "mem", events, tls=False, auth=False)
    rows = {}
    try:
        copy_fixture(Path(args.fixture), node)
        for label in ("first-open", "reopen"):
            ready = node.start(timeout=7200)
            time.sleep(args.settle)
            status = proc_status(node.pid())
            conn = node.session(None, timeout=300)
            g, _ = conn.cmd("GROUP fn.test")
            a, _ = conn.cmd("ARTICLE 1", True)
            conn.close()
            after_read = proc_status(node.pid())
            st = node.op("status", timeout=600)
            rows[label] = {"seconds_to_listening": round(ready, 1), "settled": status,
                           "after_read": after_read, "group": g, "article": a[:3],
                           "status": st.stdout.decode("utf-8", "replace")[-1500:]}
            events.emit("memory", label=label, **rows[label])
            node.stop()
    finally:
        if node.pid():
            node.stop()
        (work / "summary.json").write_text(json.dumps(rows, indent=1, default=str))
        events.close()
    print(json.dumps({k: (v["seconds_to_listening"], v["settled"].get("VmRSS"),
                          v["settled"].get("VmHWM")) for k, v in rows.items()}))
    return 0


# --------------------------------------------------------------------------
# two nodes peering (f3)

# ~13.9 GB of init reservation (the heap figure the owner checks against its
# unit's memory): room for 10,000 x 2 KiB articles with a wide margin.
PAIR_PROFILE = ("--max-transactions", "131072", "--max-history-octets", "300000000",
                "--max-record-octets", "196608", "--max-article-octets", "32768",
                "--max-groups-per-article", "16", "--max-open-suffix", "4096")


def pair_article(side, n, group):
    msgid = "<pair-{}-{:05d}@fitness.example.invalid>".format(side, n)
    return msgid, make_article(msgid, [group], "pair {} {}".format(side, n), 1800)


def strip_local(lines):
    """ARTICLE less the Xref and Path lines: what both nodes must agree on."""
    return [l for l in lines if not l.lower().startswith(("xref:", "path:"))]


class PairSide:
    def __init__(self, node, name):
        self.node, self.name = node, name
        self.posted = {}          # msgid -> (t, n)
        self.refused = {}         # msgid -> (n, reply)
        self.uncertain = {}
        self.conn = None

    def post(self, n, group, events):
        msgid, octets = pair_article(self.name, n, group)
        for attempt in range(3):
            try:
                if self.conn is None:
                    self.conn = self.node.session(None, timeout=120)
                first, final = self.conn.post(octets)
                reply = final or first
                if reply.startswith("240"):
                    self.posted[msgid] = (now(), n)
                elif "uncertain" in reply:
                    # told uncertain by the node (a disk stall past H): it
                    # may still be stored; convergence decides
                    self.uncertain[msgid] = (n, reply)
                    events.emit("pair-told-uncertain", side=self.name, n=n, msgid=msgid,
                                reply=reply)
                else:
                    self.refused[msgid] = (n, reply)
                    events.emit("pair-refused", side=self.name, n=n, msgid=msgid, reply=reply)
                return msgid, reply
            except (Gone, OSError) as error:
                self.conn = None
                self.uncertain[msgid] = (n, str(error)[:120])
                time.sleep(1)
        return msgid, None


def arrived(node, msgids, timeout=60):
    """The subset of MSGIDS the node serves (STAT 223), on one connection."""
    have = set()
    conn = node.session(None, timeout=timeout)
    for m in msgids:
        s, _ = conn.cmd("STAT " + m)
        if s.startswith("223"):
            have.add(m)
    conn.close()
    return have


def fetch_articles(node, msgids):
    out = {}
    conn = node.session(None, timeout=120)
    for m in msgids:
        s, body = conn.cmd("ARTICLE " + m, True)
        out[m] = (s[:3], hashlib.sha256("\n".join(strip_local(body)).encode()).hexdigest()
                  if s.startswith("220") else None)
    conn.close()
    return out


def log_tail(node, n=40, pattern=None):
    try:
        lines = node.log.read_text(errors="replace").splitlines()
    except OSError:
        return []
    if pattern:
        lines = [l for l in lines if re.search(pattern, l)]
    return lines[-n:]


def cmd_pair(args):
    work = Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    events = Events(work / "events.jsonl")
    groups = ["fit.g{:02d}".format(i) for i in range(args.groups)]
    a = Node(args.image, work, "A", events, tls=False, auth=False)
    b = Node(args.image, work, "B", events, tls=False, auth=False)
    A, B = PairSide(a, "A"), PairSide(b, "B")
    summary = {"image": args.image, "per_side": args.per_side, "groups": len(groups)}
    try:
        for node in (a, b):
            prepare(node, events, None, groups=groups, profile=PAIR_PROFILE)
            r = node.op("policy", "set", "path-identity", node.identity)
            events.emit("policy", node=node.name, rc=r.returncode)
        for src, dst in ((a, b), (b, a)):
            r = src.op("peer", "add", dst.name, dst.identity, "127.0.0.1", dst.port,
                       "fit.*", "fit.*", "127.0.0.1", "true")
            events.emit("peer-add", node=src.name, peer=dst.name, rc=r.returncode,
                        out=(r.stdout + r.stderr).decode("utf-8", "replace")[-300:])
        if args.catch_up:
            r = b.op("peer", "catch-up", "A", args.catch_up)
            events.emit("catch-up-config", rc=r.returncode,
                        out=(r.stdout + r.stderr).decode("utf-8", "replace")[-300:])
        a.start()
        b.start()
        rng = random.Random(args.seed)
        total = args.per_side
        # Phase 1: both sides post, spaced over the first half of the budget.
        phase1 = int(total * 0.8)
        gap = (args.minutes * 60 * 0.5) / max(1, phase1)
        checkpoints = []
        first_refusal = {}
        for n in range(phase1):
            for side in (A, B):
                msgid, reply = side.post(n, groups[rng.randrange(len(groups))], events)
                if reply and not reply.startswith("240") and "uncertain" not in reply \
                        and side.name not in first_refusal:
                    first_refusal[side.name] = {"n": n, "reply": reply,
                                                "health": health_words(side.node)}
                    events.emit("finding", what="local POST refused while peering",
                                side=side.name, n=n, reply=reply)
            if (n + 1) % 100 == 0:
                row = pair_progress(A, B, events, n + 1)
                checkpoints.append(row)
            time.sleep(gap)
        settle(A, B, events, args.settle)
        summary["phase1"] = pair_progress(A, B, events, phase1, final=True)
        # Phase 2: B down for --down-minutes while A keeps posting; then B back.
        b.stop()
        events.emit("pair-b-down", minutes=args.down_minutes)
        rest = total - phase1
        down_posts = rest // 2
        down_end = now() + args.down_minutes * 60
        per = (args.down_minutes * 60) / max(1, down_posts)
        for n in range(phase1, phase1 + down_posts):
            A.post(n, groups[rng.randrange(len(groups))], events)
            time.sleep(per)
        while now() < down_end:
            time.sleep(1)
        restarted = now()
        b.start()
        missing = [m for m in A.posted]
        conv = converge(b, missing, events, args.settle, "after-down")
        summary["phase2"] = {"down_posts": down_posts, "converge": conv,
                             "catch_up_lines": log_tail(b, 10, "catch-up peer="),
                             "seconds_from_restart": round(now() - restarted, 1)}
        # Phase 3: kill -9 B in the middle of a burst A feeds it.
        burst = list(range(phase1 + down_posts, total))
        killed_at = None
        for i, n in enumerate(burst):
            A.post(n, groups[rng.randrange(len(groups))], events)
            if i == len(burst) // 2 and killed_at is None:
                b.kill9()
                killed_at = n
        b.start()
        conv3 = converge(b, list(A.posted), events, args.settle, "after-kill")
        summary["phase3"] = {"killed_after_post": killed_at, "converge": conv3}
        # B's own articles must all be on A too.
        conv_a = converge(a, list(B.posted), events, args.settle, "b-to-a")
        summary["b_to_a"] = conv_a
        # Octets: every article on both sides agrees apart from Path and Xref.
        both = sorted(set(A.posted) | set(B.posted))
        sample_ids = rng.sample(both, min(len(both), args.octet_sample))
        fa, fb = fetch_articles(a, sample_ids), fetch_articles(b, sample_ids)
        differ = [m for m in sample_ids if fa[m] != fb[m]]
        summary["octets"] = {"compared": len(sample_ids), "differ": len(differ),
                             "ids": differ[:20]}
        if differ:
            events.emit("finding", what="article octets differ between A and B",
                        count=len(differ), ids=differ[:10])
        # No duplicates on B: LISTGROUP count equals distinct Message-IDs.
        summary["duplicates"] = count_duplicates(b, groups, events)
        summary["first_refusal"] = first_refusal
        summary["refused"] = {"A": len(A.refused), "B": len(B.refused)}
        summary["uncertain"] = {"A": len(A.uncertain), "B": len(B.uncertain)}
        summary["progress"] = checkpoints
        summary["health"] = {"A": health_words(a), "B": health_words(b)}
        summary["feed_lines"] = {"A": log_tail(a, 15, "feed|FEED"), "B": log_tail(b, 15, "feed|FEED")}
    finally:
        for node in (a, b):
            if node.pid():
                node.stop()
        findings = [json.loads(l) for l in (work / "events.jsonl").read_text().splitlines()
                    if '"kind": "finding"' in l]
        summary["findings"] = findings
        (work / "summary.json").write_text(json.dumps(summary, indent=1, default=str))
        events.close()
    print(json.dumps({k: summary.get(k) for k in ("first_refusal", "refused", "octets")},
                     default=str))
    return 0


def pair_progress(A, B, events, n, final=False):
    row = {"n": n}
    for src, dst in ((A, B), (B, A)):
        ids = list(src.posted)
        have = arrived(dst.node, ids) if dst.node.pid() else set()
        row["{}->{}".format(src.name, dst.name)] = {"posted": len(ids), "arrived": len(have),
                                                     "backlog": len(ids) - len(have)}
    row["health"] = {s.name: health_words(s.node)[1].splitlines()[:3] for s in (A, B)
                     if s.node.pid()}
    for s in (A, B):
        if s.node.pid():
            row.setdefault("rss_kb", {})[s.name] = proc_status(s.node.pid()).get("VmRSS")
    events.emit("pair-progress", final=final, **row)
    return row


def settle(A, B, events, seconds):
    deadline = now() + seconds
    while now() < deadline:
        ok = True
        for src, dst in ((A, B), (B, A)):
            if len(arrived(dst.node, list(src.posted))) < len(src.posted):
                ok = False
        if ok:
            return True
        time.sleep(5)
    return False


def converge(node, msgids, events, seconds, label):
    started = now()
    deadline = started + seconds
    have = set()
    while now() < deadline:
        have = arrived(node, msgids)
        if len(have) == len(msgids):
            break
        time.sleep(5)
    row = {"label": label, "want": len(msgids), "have": len(have),
           "seconds": round(now() - started, 1), "missing": sorted(set(msgids) - have)[:20]}
    events.emit("converge", node=node.name, **row)
    if len(have) < len(msgids):
        events.emit("finding", what="did not converge: " + label, node=node.name,
                    missing=len(msgids) - len(have))
    return row


def count_duplicates(node, groups, events):
    conn = node.session(None, timeout=300)
    dup, total = 0, 0
    for g in groups:
        s, _ = conn.cmd("GROUP " + g)
        if not s.startswith("211"):
            continue
        s, lines = conn.cmd("OVER 1-", True)
        ids = [l.split("\t")[4] for l in lines if l.count("\t") >= 4]
        total += len(ids)
        dup += len(ids) - len(set(ids))
    conn.close()
    events.emit("duplicates", node=node.name, total=total, duplicates=dup)
    if dup:
        events.emit("finding", what="duplicate articles in a group", node=node.name, count=dup)
    return {"total": total, "duplicates": dup}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    soak = sub.add_parser("soak")
    soak.add_argument("--image", required=True)
    soak.add_argument("--developer", default="")
    soak.add_argument("--fixture", default="")
    soak.add_argument("--init-flag", action="append")
    soak.add_argument("--work", required=True)
    soak.add_argument("--minutes", type=float, default=120)
    soak.add_argument("--posters", type=int, default=8)
    soak.add_argument("--readers", type=int, default=8)
    soak.add_argument("--sample-minutes", type=float, default=15)
    soak.add_argument("--client-minutes", type=float, default=10)
    soak.add_argument("--clients", default="slrn")
    soak.add_argument("--presence-limit", type=int, default=0)
    soak.add_argument("--policy", nargs=2, action="append")
    soak.add_argument("--chaos", action="store_true")
    soak.add_argument("--kills", type=int, default=10)
    soak.add_argument("--stalls", type=int, default=2)
    soak.add_argument("--torn", action="store_true")
    soak.add_argument("--disk-full-mb", type=int, default=0)
    soak.add_argument("--seed", type=int, default=20260928)
    mem = sub.add_parser("memory")
    mem.add_argument("--image", required=True)
    mem.add_argument("--fixture", required=True)
    mem.add_argument("--work", required=True)
    mem.add_argument("--settle", type=float, default=30)
    pair = sub.add_parser("pair")
    pair.add_argument("--image", required=True)
    pair.add_argument("--work", required=True)
    pair.add_argument("--per-side", type=int, default=2000)
    pair.add_argument("--groups", type=int, default=20)
    pair.add_argument("--minutes", type=float, default=60)
    pair.add_argument("--down-minutes", type=float, default=10)
    pair.add_argument("--settle", type=float, default=600)
    pair.add_argument("--catch-up", default="30")
    pair.add_argument("--octet-sample", type=int, default=500)
    pair.add_argument("--seed", type=int, default=20260928)
    args = parser.parse_args(argv)
    if args.cmd == "pair":
        return cmd_pair(args)
    if args.cmd == "soak":
        return cmd_soak(args)
    if args.cmd == "memory":
        return cmd_memory(args)
    return 2


if __name__ == "__main__":
    sys.exit(main())
