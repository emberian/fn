#!/usr/bin/env python3
"""Power loss under an OpenBSD node: SIGKILL the virtual machine while a
client outside it posts, reboot, recover, and check what the store kept
(lane power-loss-openbsd, 2026-09-26;
planning/evidence/power-loss-openbsd-2026-09-26.md).

The rig (hbox; the driver and the oracle never run inside the guest):

  guest    OpenBSD 7.9 amd64, 1 vCPU / 2 GiB, a clone of the release-openbsd
           VM's disk (the fn tarball installed under /usr/local); qemu in the
           fn-openbsd-qemu container with /dev/kvm.  Two virtio disks: the
           root disk (an overlay over the clone, cache=writeback) and the
           STORE disk (a fresh qcow2, FFS2 on sd1a mounted at /pl, with or
           without -o softdep) whose qemu cache mode is the configuration's
           (writeback: the guest sees a volatile write cache and its flushes
           reach the host file; unsafe: qemu ignores the guest's flushes).
  node     `fn operator CFG run` started over ssh; its stdout and stderr are
           piped to files on hbox, so the owner's log survives the cut.
  client   posting threads on hbox against the guest's NNTP port (qemu user
           networking forwards 127.0.0.1:PORT); every attempt, 240, 441 and
           connection loss is appended to oracle.jsonl on hbox.
  cut      `docker kill -s KILL` of the container: qemu dies with the guest's
           buffer cache and every write qemu had not yet handed to the host
           file (qcow2 metadata it had not flushed, under unsafe any of it).
           The host's page cache survives, so this is an OS and virtual-disk
           power loss, not a physical disk's.
  after    reboot; `fsck -y` of the store file system (output kept);
           mount; `operator CFG recover`; the owner; the oracle; `status`.

The oracle, per epoch (one store; a new store when the epoch ends):
  - every Message-ID with a 240 answers ARTICLE with 220 and exactly the
    octets first read for it (the pin), until a reclaim has started;
  - a Message-ID whose POST drew a 441 answers 430, always;
  - an attempt with no reply answers the pin, a 220 with the posted content
    (then pinned: recovered-accepted stays accepted), or 430;
  - a 220's content is the posted article: the posted body exactly and every
    posted header line among the served ones;
  - OVER: a local number, once observed, keeps its Message-ID and a
    Message-ID keeps its number; no number is shared; a Message-ID first
    listed after a cut takes a number above every number observed before;
  - recover exits 0, the owner announces LISTENING, status exits 0;
  - after a reclaim that exited 0 every article answers 430; during an
    interrupted one each acknowledged article answers its pin or 430, and a
    rerun of the verb succeeds;
  - after an interrupted compact the rerun exits 0 (or 1 already compact).
Any other answer is a violation, with the cycle's record, fsck output and
the store disk copy kept.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import random
import re
import shlex
import socket
import subprocess
import sys
import threading
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))  # the repository root
from tools.wire_stream import whole_stream  # noqa: E402  writes are sendall

IMAGE = "fn-openbsd-qemu:local"
FN = "/usr/local/fn-a04213276edf/bin/fn"
GROUP = "fn.test"
KVM_GID = "993"
CKPT = re.compile(r"CHECKPOINT auto sequence=(\d+) suffix=(\d+) octets=(\d+) ms=(\d+)")


def now():
    return round(time.time(), 3)


def append(path, **rec):
    rec.setdefault("t", now())
    with open(path, "a") as f:
        f.write(json.dumps(rec, sort_keys=True) + "\n")
        f.flush()
        os.fsync(f.fileno())


def run(argv, timeout=600, **kw):
    r = subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       timeout=timeout, **kw)
    return r.returncode, r.stdout.decode("utf-8", "replace"), r.stderr.decode("utf-8", "replace")


# ---------------------------------------------------------------------------
# The virtual machine.

class VM:
    def __init__(self, base, cfg):
        self.base = Path(base)
        self.cfg = cfg
        self.dir = self.base / cfg["name"]
        self.name = "pl-obsd-" + cfg["name"]
        self.key = self.base / "vm" / "id_ed25519"
        self.boots = 0

    def qemu_argv(self, serial):
        c = self.cfg
        d = "/pl/" + c["name"]
        argv = ["qemu-system-x86_64", "-enable-kvm", "-cpu", "host", "-smp", str(c.get("smp", 1)),
                "-m", str(c.get("mem", 2048)),
                "-drive", "file=%s/root.img,if=virtio,format=raw,cache=writeback" % d,
                "-drive", "file=%s/%s,if=virtio,format=%s,cache=%s" % (d, store_file(c), c.get("format", "qcow2"), c["cache"]),
                "-netdev", "user,id=n0,hostfwd=tcp:127.0.0.1:%d-:22,hostfwd=tcp:127.0.0.1:%d-:11600"
                % (c["ssh"], c["nntp"]),
                "-device", "virtio-net-pci,netdev=n0", "-display", "none",
                "-serial", "file:%s/%s" % (d, serial),
                "-monitor", "unix:%s/monitor.sock,server,nowait" % d]
        if c.get("trace"):
            argv += ["-trace", "enable=file_paio_submit,file=%s/trace-%d.log" % (d, self.boots)]
        return argv

    def running(self):
        code, so, _ = run(["docker", "inspect", "-f", "{{.State.Running}}", self.name], timeout=60)
        return code == 0 and so.strip() == "true"

    def start(self, timeout=900):
        self.gone()
        self.boots += 1
        serial = "serial-%d.log" % self.boots
        argv = ["docker", "run", "-d", "--rm", "--name", self.name, "--user", "1000:1000",
                "--group-add", KVM_GID, "--device", "/dev/kvm", "--network", "host",
                "--memory", "%dm" % (self.cfg.get("mem", 2048) + 1024), "-v", "%s:/pl" % self.base, IMAGE] + self.qemu_argv(serial)
        t0 = time.time()
        code, so, se = run(argv, timeout=120)
        if code:
            raise RuntimeError("docker run: %s %s" % (so, se))
        while time.time() - t0 < timeout:
            code, so, _ = self.ssh("echo up", timeout=20)
            if code == 0 and "up" in so:
                return round(time.time() - t0, 2)
            if not self.running():
                raise RuntimeError("qemu exited during boot (%s)" % serial)
            time.sleep(1)
        raise RuntimeError("no ssh within %d s (%s)" % (timeout, serial))

    def kill(self):
        """The power cut: SIGKILL to qemu (the container's first process)."""
        t = now()
        run(["docker", "kill", "-s", "KILL", self.name], timeout=60)
        self.gone()
        return t

    def gone(self):
        for _ in range(120):
            code, _, _ = run(["docker", "inspect", self.name], timeout=60)
            if code:
                return
            run(["docker", "rm", "-f", self.name], timeout=60)
            time.sleep(0.5)
        raise RuntimeError("container %s did not go" % self.name)

    def ssh_argv(self, cmd):
        return ["ssh", "-p", str(self.cfg["ssh"]), "-i", str(self.key), "-o", "BatchMode=yes",
                "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null",
                "-o", "LogLevel=ERROR", "-o", "ConnectTimeout=5", "-o", "ServerAliveInterval=5",
                "root@127.0.0.1", cmd]

    def ssh(self, cmd, timeout=600):
        try:
            return run(self.ssh_argv(cmd), timeout=timeout)
        except subprocess.TimeoutExpired:
            return 124, "", "timeout"

    def popen(self, cmd, out, err):
        return subprocess.Popen(self.ssh_argv(cmd), stdout=out, stderr=err, stdin=subprocess.DEVNULL)

    def shutdown(self):
        self.ssh("sync; shutdown -p now", timeout=60)
        for _ in range(240):
            if not self.running():
                break
            time.sleep(0.5)
        self.gone()


def hmp(sock, cmd):
    s = socket.socket(socket.AF_UNIX)
    s.connect(str(sock))
    s.settimeout(3)
    buf = b""

    def rd():
        nonlocal buf
        try:
            while not buf.rstrip().endswith(b"(qemu)"):
                c = s.recv(65536)
                if not c:
                    break
                buf += c
        except socket.timeout:
            pass
    rd()
    buf = b""
    s.sendall(cmd.encode() + b"\n")
    rd()
    s.close()
    return re.sub(rb"\x1b\[[0-9;]*[A-Za-z]", b"", buf).decode("latin-1")


def store_file(cfg):
    return "store.img" if cfg.get("format") == "raw" else "store.qcow2"


def qemu_img(base, *args):
    return run(["docker", "run", "--rm", "--user", "1000:1000", "-v", "%s:/pl" % base, IMAGE,
                "qemu-img"] + list(args), timeout=600)


# ---------------------------------------------------------------------------
# The client.

def article(mid, i, size, group=GROUP):
    head = ("From: pl@power-loss-openbsd.invalid\r\nNewsgroups: %s\r\nSubject: pl %d\r\n"
            "Date: Sat, 26 Sep 2026 23:00:00 +0000\r\nMessage-ID: %s\r\n\r\n" % (group, i, mid))
    lines, n = [], len(head)
    k = 0
    while n < size:
        line = ("%s line %d " % (mid, k)).ljust(76, "x")[:76] + "\r\n"
        lines.append(line)
        n += len(line)
        k += 1
    if not lines:
        lines.append("body\r\n")
    return (head + "".join(lines)).encode("ascii")


def split_article(octets):
    head, _, body = octets.partition(b"\r\n\r\n")
    return head.split(b"\r\n"), body


class Conn:
    def __init__(self, port, timeout=120):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.f = whole_stream(self.sock)
        self.greeting = self.f.readline()
        if not self.greeting:
            raise ConnectionError("no greeting")

    def line(self, text):
        self.f.write(text.encode("ascii") + b"\r\n")
        return self.f.readline()

    def multiline(self):
        rows = []
        while True:
            l = self.f.readline()
            if not l:
                raise ConnectionError("closed inside a multi-line reply")
            if l == b".\r\n":
                return rows
            rows.append(l)

    def close(self):
        try:
            self.line("QUIT")
        except OSError:
            pass
        self.sock.close()


def poster(port, ep, tid, state, stop, log, refuse_every, sizes_rng):
    """Post until STOP, a fresh connection after each refusal or loss."""
    lock = state["lock"]
    while not stop.is_set():
        try:
            c = Conn(port, timeout=60)
        except OSError:
            time.sleep(0.2)
            continue
        try:
            while not stop.is_set():
                with lock:
                    i = state["next"][tid]
                    state["next"][tid] = i + 1
                mid = "<pl-%s-%d-%d@power-loss-openbsd.invalid>" % (ep, tid, i)
                refuse = refuse_every and tid == 0 and i % refuse_every == refuse_every // 2
                size = sizes_rng.choice((300, 900, 2000, 4000))
                art = article(mid, i, size, "fn.not-carried" if refuse else GROUP)
                append(log, tag="attempt", mid=mid, size=size, refuse=bool(refuse))
                r = c.line("POST")
                if not r.startswith(b"340"):
                    append(log, tag="noreply" if not r else "post-refused", mid=mid, reply=r.decode("latin-1").strip())
                    break
                c.f.write(art + b".\r\n")
                r = c.f.readline()
                word = r[:3].decode("latin-1")
                if word == "240":
                    append(log, tag="ack", mid=mid)
                    with lock:
                        state["acks"] += 1
                elif word in ("441", "437"):
                    append(log, tag="refuse", mid=mid, reply=r.decode("latin-1").strip())
                    break
                else:
                    append(log, tag="noreply" if not r else "other", mid=mid, reply=r.decode("latin-1").strip())
                    break
        except OSError as e:
            append(log, tag="conn-lost", tid=tid, err=repr(e)[:120])
        finally:
            try:
                c.sock.close()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# The oracle.

class Oracle:
    """The client's record, replayed from oracle.jsonl (so a restarted driver
    resumes).  Per epoch: attempts, acks, refusals, the posted octets (by
    regeneration), pins, the number map, the reclaim state."""

    def __init__(self, path):
        self.path = path
        self.ep = None
        self.eps = {}
        if path.exists():
            for l in path.read_text().splitlines():
                self.apply(json.loads(l))

    def epoch(self, ep=None):
        ep = ep or self.ep
        return self.eps.setdefault(ep, {"attempt": {}, "ack": set(), "refuse": set(), "pin": {},
                                        "num": {}, "mid_num": {}, "max_num": 0,
                                        "reclaim": None, "dead": False})

    def apply(self, r):
        tag = r["tag"]
        if tag == "epoch":
            self.ep = r["ep"]
            self.epoch()
            return
        e = self.epoch()
        if tag == "attempt":
            e["attempt"][r["mid"]] = (r["size"], r["refuse"])
        elif tag == "ack":
            e["ack"].add(r["mid"])
        elif tag == "refuse":
            e["refuse"].add(r["mid"])
        elif tag == "pin":
            e["pin"][r["mid"]] = r["reply"].encode("latin-1")
        elif tag == "number":
            e["num"][r["n"]] = r["mid"]
            e["mid_num"][r["mid"]] = r["n"]
            e["max_num"] = max(e["max_num"], r["n"])
        elif tag == "reclaim":
            e["reclaim"] = r["state"]
        elif tag == "dead":
            e["dead"] = True

    def log(self, **rec):
        append(self.path, **rec)
        self.apply(rec)

    def expected_content(self, mid):
        size, refuse = self.epoch()["attempt"][mid]
        i = int(mid.split("-")[3].split("@")[0])
        return article(mid, i, size, "fn.not-carried" if refuse else GROUP)

    def check(self, port, violations):
        """Read every attempted Message-ID and the overview; judge; pin."""
        e = self.epoch()
        c = Conn(port)
        got = {}
        try:
            for mid in e["attempt"]:
                first = c.line("ARTICLE " + mid)
                if first.startswith(b"220"):
                    got[mid] = first + b"".join(c.multiline())
                else:
                    got[mid] = first
            r = c.line("GROUP " + GROUP)
            over = []
            if r.startswith(b"211"):
                r = c.line("OVER 1-")
                if r.startswith(b"224"):
                    for l in c.multiline():
                        f = l.rstrip(b"\r\n").split(b"\t")
                        if len(f) > 4 and f[0].isdigit():
                            over.append((int(f[0]), f[4].decode("latin-1")))
        finally:
            c.close()
        counts = {"pinned": 0, "new-pin": 0, "absent": 0, "reclaimed": 0}
        reclaim = e["reclaim"]
        for mid, g in got.items():
            acked, refused, pin = mid in e["ack"], mid in e["refuse"], e["pin"].get(mid)
            ok = False
            if refused:
                ok = g.startswith(b"430")
                if not ok:
                    violations.append("refused-became-accepted:%s:%r" % (mid, g[:50]))
                continue
            if reclaim == "done":
                ok = g.startswith(b"430")
                counts["reclaimed"] += ok
                if not ok:
                    violations.append("served-after-completed-reclaim:%s:%r" % (mid, g[:50]))
            elif pin is not None:
                ok = g == pin or (reclaim == "started" and g.startswith(b"430"))
                counts["pinned" if g == pin else "reclaimed"] += ok
                if not ok:
                    violations.append("%s-pin-changed:%s:%r" % ("acked" if acked else "recovered", mid, g[:60]))
            elif g.startswith(b"220"):
                heads, body = split_article(self.expected_content(mid))
                sh, sb = split_article(g.split(b"\r\n", 1)[1] if b"\r\n" in g else b"")
                sb = sb[:-3] if sb.endswith(b".\r\n") else sb
                sb = sb.replace(b"\r\n..", b"\r\n.")
                ok = sb == body and all(h in sh for h in heads)
                if ok:
                    self.log(tag="pin", mid=mid, reply=g.decode("latin-1"))
                    counts["new-pin"] += 1
                else:
                    violations.append("content-mismatch:%s:%r" % (mid, g[:80]))
            elif g.startswith(b"430"):
                ok = not acked or reclaim == "started"
                counts["absent" if not acked else "reclaimed"] += ok
                if not ok:
                    violations.append("acked-lost:%s:%r" % (mid, g[:60]))
            else:
                violations.append("unexpected-reply:%s:%r" % (mid, g[:60]))
        nums = [n for n, _ in over]
        if len(set(nums)) != len(nums):
            violations.append("number-shared:%d" % (len(nums) - len(set(nums))))
        before = e["max_num"]
        for n, mid in over:
            if n in e["num"] and e["num"][n] != mid:
                violations.append("number-reassigned:%d:%s->%s" % (n, e["num"][n], mid))
            elif mid in e["mid_num"] and e["mid_num"][mid] != n:
                violations.append("number-changed:%s:%d->%d" % (mid, e["mid_num"][mid], n))
            elif n not in e["num"]:
                if n <= before:
                    violations.append("number-below-observed:%d<=%d:%s" % (n, before, mid))
                self.log(tag="number", n=n, mid=mid)
        # a pinned article the overview dropped (before any reclaim) is lost
        listed = {mid for _, mid in over}
        if reclaim is None:
            for mid in e["pin"]:
                if mid not in listed:
                    violations.append("pinned-not-listed:%s" % mid)
        counts["listed"] = len(over)
        counts["attempted"] = len(e["attempt"])
        counts["acked"] = len(e["ack"])
        counts["refused"] = len(e["refuse"])
        return counts


# ---------------------------------------------------------------------------
# The campaign.

GUEST_PREP = r"""
set -x
rcctl stop fn; rcctl disable fn
rcctl disable smtpd sndiod ntpd
grep -q library_aslr /etc/rc.conf.local || echo library_aslr=NO >> /etc/rc.conf.local
rm -f /var/db/kernel.SHA256
du -xsk /root/* 2>/dev/null | sort -n | tail -5
rm -f /root/sbcl.core; df -h /
fdisk -iy sd1
printf '/pl 100M-* 100%%\n' > /tmp/pl.tmpl
disklabel -w -A -T /tmp/pl.tmpl sd1
disklabel sd1 | tail -4
newfs NEWFS_FLAGS sd1a
dumpfs sd1a | head -3
mkdir -p /pl /var/pl
dmesg | grep -E 'vioblk|sd[01]'
"""


# The node listens on the guest's loopback (a loopback listener keeps the
# development defaults: no login, no exposure limits); pf redirects the
# forwarded port to it.  The client is still outside the guest.
PFRDR = r"""
grep -q 'port 11600' /etc/pf.conf || echo 'pass in quick on vio0 inet proto tcp to port 11600 rdr-to 127.0.0.1 port 11600' >> /etc/pf.conf
pfctl -f /etc/pf.conf && pfctl -sr | grep 11600
sync
"""


def cfg_text(ep):
    return ('[store]\npath = "/pl/%s"\n[listener]\nhost = "127.0.0.1"\nport = 11600\n'
            '[posting]\nenabled = true\n[control]\npath = "/var/pl/%s.sock"\n' % (ep, ep))


class Campaign:
    def __init__(self, a):
        self.a = a
        self.base = Path(a.base)
        self.cfg = json.loads((self.base / a.name / "cfg.json").read_text())
        self.vm = VM(self.base, self.cfg)
        self.dir = self.base / a.name
        self.cuts = self.dir / "cuts.jsonl"
        self.oracle = Oracle(self.dir / "oracle.jsonl")
        self.rng = random.Random(a.seed)
        self.est = {"compact": 5.0, "reclaim": 5.0, "recover": 5.0, "init": 5.0, "import": 20.0}
        self.cycle = 0
        if self.cuts.exists():
            rows = [json.loads(l) for l in self.cuts.read_text().splitlines()]
            self.cycle = len(rows)
            for r in rows:
                for k in self.est:
                    if r.get(k + "_wall"):
                        self.est[k] = r[k + "_wall"]

    def learn(self, verb, done, d, t0, rec):
        """The cut point is uniform over [0, 1.1 x the verb's estimated
        wall]; the estimate is the last completed wall, and grows while the
        verb never completes before its cut."""
        if done is not None:
            rec[verb + "_wall"] = round(time.time() - t0, 2)
            self.est[verb] = max(0.2, rec[verb + "_wall"])
        else:
            self.est[verb] = max(self.est[verb], d * 1.3)

    def qcheck(self):
        """The store disk's qcow2 state after the cut: leaked clusters are
        allocations whose table update qemu had not written."""
        if self.cfg.get("format") == "raw":
            return None
        code, so, se = qemu_img(self.base, "check", "--output=json", "/pl/%s/store.qcow2" % self.a.name)
        try:
            j = json.loads(so)
            return {k: j.get(k, 0) for k in ("leaks", "corruptions", "check-errors", "allocated-clusters")}
        except ValueError:
            return {"exit": code, "err": (so + se)[-200:]}

    def g(self, cmd, timeout=900):
        return self.vm.ssh(cmd, timeout=timeout)

    def fnv(self, ep, *verb, timeout=900):
        return self.g("cd /var/pl && %s operator /var/pl/%s.toml %s" % (FN, ep, " ".join(shlex.quote(v) for v in verb)),
                      timeout=timeout)

    def mount(self, rec):
        code, so, se = self.g("fsck -y /dev/rsd1a 2>&1; echo fsck-exit=$?", timeout=900)
        rec["fsck"] = so[-1500:]
        m = re.search(r"fsck-exit=(\d+)", so)
        rec["fsck_exit"] = int(m.group(1)) if m else None
        opts = "-o softdep " if self.cfg["softdep"] else ""
        code, so, se = self.g("mount %s/dev/sd1a /pl && mount | grep ' /pl '" % opts)
        rec["mount"] = (so + se).strip()
        return code == 0

    def owner_start(self, ep, rec, tag):
        out = open(self.dir / ("owner-%s.out" % tag), "wb")
        err = open(self.dir / ("owner-%s.err" % tag), "wb")
        p = self.vm.popen("cd /var/pl && echo $$ > /var/pl/owner.pid && exec %s operator /var/pl/%s.toml run"
                          % (FN, ep), out, err)
        t0 = time.time()
        while time.time() - t0 < 300:
            if b"LISTENING" in (self.dir / ("owner-%s.out" % tag)).read_bytes():
                rec["owner_start_wall"] = round(time.time() - t0, 2)
                return p, err
            if p.poll() is not None:
                break
            time.sleep(0.2)
        rec["owner_err"] = (self.dir / ("owner-%s.err" % tag)).read_bytes()[-600:].decode("latin-1")
        return None, err

    def owner_stop(self, p):
        self.g("kill -TERM $(cat /var/pl/owner.pid)", timeout=60)
        try:
            return p.wait(timeout=600)
        except subprocess.TimeoutExpired:
            return None

    def new_epoch(self):
        ep = "e%03d" % (len(self.oracle.eps) + 1)
        self.oracle.log(tag="epoch", ep=ep)
        return ep

    def finding(self, rec):
        """A defect that does not end the epoch (the store is made again)."""
        fdir = self.dir / ("finding-%04d" % self.cycle)
        fdir.mkdir(exist_ok=True)
        (fdir / "cycle.json").write_text(json.dumps(rec, indent=1, default=str))

    def violation(self, rec, violations):
        vdir = self.dir / ("violation-%04d" % self.cycle)
        vdir.mkdir(exist_ok=True)
        (vdir / "cycle.json").write_text(json.dumps(rec, indent=1, default=str))
        for f in self.dir.glob("owner-c%04d-*" % self.cycle):
            (vdir / f.name).write_bytes(f.read_bytes())
        if self.a.keep_disk:
            qemu_img(self.base, "convert", "-O", "qcow2", "/pl/%s/%s" % (self.a.name, store_file(self.cfg)),
                     "/pl/%s/%s/store.qcow2" % (self.a.name, vdir.name))
        self.oracle.log(tag="dead", violations=violations[:20])

    def post_until(self, ep, rec, kill_rule):
        """Posting threads; KILL_RULE(stats) returns seconds to wait before the cut."""
        e = self.oracle.epoch(ep)
        nxt = [0, 0]
        for mid in e["attempt"]:
            tid, i = int(mid.split("-")[2]), int(mid.split("-")[3].split("@")[0])
            nxt[tid] = max(nxt[tid], i + 1)
        state = {"lock": threading.Lock(), "next": nxt, "acks": 0}
        stop = threading.Event()
        log = self.dir / "oracle.jsonl"
        ths = [threading.Thread(target=poster, args=(self.cfg["nntp"], ep, tid, state, stop, log,
                                                     self.a.refuse_every, random.Random(self.rng.random())),
                                daemon=True) for tid in (0, 1)]
        t0 = time.time()
        for t in ths:
            t.start()
        kill_rule(t0, state)
        rec["cut_after_s"] = round(time.time() - t0, 3)
        rec["cut_t"] = self.vm.kill()
        stop.set()
        for t in ths:
            t.join(timeout=120)
        self.oracle = Oracle(self.dir / "oracle.jsonl")

    def run_cycle(self, phase, ep, prev):
        a = self.a
        self.cycle += 1
        tag = "c%04d" % self.cycle
        rec = {"cycle": self.cycle, "phase": phase, "ep": ep, "t0": now()}
        violations = []
        rec["qcow2"] = self.qcheck()
        rec["boot_wall"] = self.vm.start()
        rec["uptime"] = self.g("uptime")[1].strip()
        if not self.mount(rec):
            violations.append("mount-failed")
        if phase == "init":
            # the configuration is on the root disk (write-through); sync(2)
            # writes it out of the guest's buffer cache before the cut
            self.g("rm -rf /pl/%s /pl/%s.init-*; printf %s > /var/pl/%s.toml; sync" % (ep, ep, shlex.quote(cfg_text(ep)), ep))
            p = self.vm.popen("cd /var/pl && %s operator /var/pl/%s.toml init %s %s"
                              % (FN, ep, a.init_flags, GROUP), subprocess.DEVNULL, subprocess.DEVNULL)
            lo, hi = a.init_window
            d = self.rng.uniform(self.est["init"] * lo, self.est["init"] * hi)
            t0 = time.time()
            done = None
            while time.time() - t0 < d:
                if p.poll() is not None:
                    done = p.returncode
                    break
                time.sleep(0.02)
            rec["init_completed_before_cut"] = done
            self.learn("init", done, d, t0, rec)
            rec["phase_cut_t"] = self.vm.kill()
            rec["phase_cut_after_s"] = round(time.time() - t0, 3)
            p.wait()
            rec["qcow2_2"] = self.qcheck()
            rec["boot2_wall"] = self.vm.start()
            if not self.mount(rec):
                violations.append("mount-failed")
            # after an init cut (PKT-647's published init,
            # fn-bs-init-log-program-crash-is-no-store-or-the-complete-empty-log):
            # ROOT is absent (at most one ROOT.init-*, which the next init
            # names as interrupted-init and after whose removal init
            # succeeds) or the complete empty store (status 0,
            # transactions=0).  With --legacy-init (a release before PKT-647)
            # a half store is a finding, not a violation.
            self.check_init(ep, done, rec, violations)
        if phase == "recovery-interrupted":
            p = self.vm.popen("cd /var/pl && exec %s operator /var/pl/%s.toml recover" % (FN, ep),
                              subprocess.DEVNULL, subprocess.DEVNULL)
            d = self.rng.uniform(0, self.est["recover"] * 1.1)
            t0 = time.time()
            done = None
            while time.time() - t0 < d:
                if p.poll() is not None:
                    done = p.returncode
                    break
                time.sleep(0.02)
            rec["recover1_completed_before_cut"] = done
            self.learn("recover", done, d, t0, rec)
            rec["phase_cut_t"] = self.vm.kill()
            rec["phase_cut_after_s"] = round(time.time() - t0, 3)
            p.wait()
            rec["qcow2_2"] = self.qcheck()
            rec["boot2_wall"] = self.vm.start()
            if not self.mount(rec):
                violations.append("mount-failed")
        t0 = time.time()
        code, so, se = self.fnv(ep, "recover")
        rec["recover"] = [code, (so + se).strip()[-400:]]
        rec["recover_wall"] = round(time.time() - t0, 2)
        if not code:
            self.est["recover"] = max(0.5, rec["recover_wall"])
        if code:
            violations.append("recover-exit-%d" % code)
        self.rerun_after(ep, prev, rec, violations)
        p, err = self.owner_start(ep, rec, tag + "-a")
        if p is None:
            violations.append("owner-no-listening")
        else:
            try:
                rec["oracle"] = self.oracle.check(self.cfg["nntp"], violations)
            except Exception as ex:
                violations.append("oracle-read-failed:%r" % ex)
            code, so, se = self.fnv(ep, "status")
            rec["status"] = [code, [l for l in so.splitlines()
                                    if l.split() and l.split()[0] in ("transactions", "pack-chain", "checkpoint", "reclaim", "headroom")]]
            if code:
                violations.append("status-exit-%d" % code)
            e = self.oracle.epoch(ep)
            if e["reclaim"] in ("started",):
                counts = dict(re.findall(r"\b(articles|reclaimable|held|reclaimed)=(\d+)", so))
                rec["reclaim_counts"] = counts
        # the phase's work, ending in the next cut
        if phase == "after-reclaim" and p is not None and not violations:
            rec["owner_stop"] = self.owner_stop(p)
            self.vm.shutdown()
            append(self.cuts, **rec)
            return rec
        if violations:
            rec["violations"] = violations
            rec["cut_t"] = self.vm.kill() if self.vm.running() else None
            self.violation(rec, violations)
            append(self.cuts, **rec)
            return rec
        if phase == "recovery-interrupted" or phase == "init":
            # the cut this cycle counted is already taken; post and cut again
            phase_work = "post"
        else:
            phase_work = phase
        rec["work"] = phase_work
        if phase_work == "post":
            self.post_until(ep, rec, lambda t0, st: time.sleep(self.rng.uniform(0.3, a.max_post_s)))
        elif phase_work == "checkpoint":
            errf = self.dir / ("owner-%s-a.err" % tag)
            ep_ = ep

            def rule(t0, st):
                seen = len(CKPT.findall(errf.read_text("latin-1")))
                last_ms = 50
                deadline = t0 + 60
                while time.time() < deadline:
                    lines = CKPT.findall(errf.read_text("latin-1"))
                    if len(lines) > seen:
                        last_ms = int(lines[-1][3])
                        # the next capture is due after about suffix records;
                        # cut at a random point of the next window
                        k = int(lines[-1][1])
                        acks0 = st["acks"]
                        while time.time() < deadline and st["acks"] - acks0 < max(1, k - 2):
                            time.sleep(0.01)
                        d = self.rng.uniform(0, 3 * last_ms / 1000.0 + 0.3)
                        time.sleep(d)
                        rec["ckpt_window"] = {"after_line": lines[-1], "delay": round(d, 3),
                                              "lines_at_cut": len(CKPT.findall(errf.read_text("latin-1"))),
                                              "lines_before": len(lines)}
                        return
                    time.sleep(0.02)
                rec["ckpt_window"] = "no-capture-line-in-60s"
            self.post_until(ep, rec, rule)
        elif phase_work == "import":
            # the owner stops; the store is exported (not cut); the import of
            # that archive into a new ROOT2 is cut
            self.post_until_stop(ep, rec, p)
            archive = "/pl/%s.archive" % ep
            self.g("rm -rf %s /pl/%si /pl/%si.import-*" % (archive, ep, ep))
            code, so, se = self.fnv(ep, "store", "export", archive, timeout=1800)
            rec["export"] = [code, (so + se)[-300:]]
            c1, so1, _ = self.fnv(ep, "status")
            n1 = re.search(r"(?m)^transactions=(\d+) articles=", so1)
            rec["export_transactions"] = n1.group(1) if n1 else None
            self.g("sync")
            if code:
                rec["violations"] = ["export-exit-%d" % code]
                rec["cut_t"] = self.vm.kill()
                self.violation(rec, rec["violations"])
                append(self.cuts, **rec)
                return rec
            self.import_cfg(ep)
            pr = self.vm.popen("cd /var/pl && exec %s operator /var/pl/%si.toml store import %s" % (FN, ep, archive),
                               open(self.dir / ("%s-import.out" % tag), "wb"), subprocess.STDOUT)
            d = self.rng.uniform(0, self.est["import"] * 1.1)
            t0 = time.time()
            done = None
            while time.time() - t0 < d:
                if pr.poll() is not None:
                    done = pr.returncode
                    break
                time.sleep(0.02)
            rec["import_completed_before_cut"] = done
            self.learn("import", done, d, t0, rec)
            rec["cut_t"] = self.vm.kill()
            rec["cut_after_s"] = round(time.time() - t0, 3)
            pr.wait()
            rec["pending_rerun"] = "import"
        elif phase_work in ("compact", "reclaim"):
            self.post_until_stop(ep, rec, p)
            if phase_work == "reclaim":
                code, so, se = self.fnv(ep, "retention", "set", "released-by-all-holders")
                rec["retention"] = [code, (so + se)[-200:]]
                self.oracle.log(tag="reclaim", state="started")
            verb = "compact" if phase_work == "compact" else "reclaim"
            pr = self.vm.popen("cd /var/pl && exec %s operator /var/pl/%s.toml store %s" % (FN, ep, verb),
                               open(self.dir / ("%s-%s.out" % (tag, verb)), "wb"), subprocess.STDOUT)
            d = self.rng.uniform(0, self.est[verb] * 1.1)
            t0 = time.time()
            done = None
            while time.time() - t0 < d:
                if pr.poll() is not None:
                    done = pr.returncode
                    break
                time.sleep(0.02)
            rec[verb + "_completed_before_cut"] = done
            self.learn(verb, done, d, t0, rec)
            rec["cut_t"] = self.vm.kill()
            rec["cut_after_s"] = round(time.time() - t0, 3)
            pr.wait()
            if verb == "reclaim" and done == 0:
                self.oracle.log(tag="reclaim", state="done")
            rec["pending_rerun"] = verb
        append(self.cuts, **rec)
        return rec

    def stages(self, root, kind):
        so = self.g("ls -d %s.%s-* 2>/dev/null" % (root, kind))[1]
        return [l for l in so.split() if l]

    def check_init(self, ep, done, rec, violations):
        a = self.a
        root = "/pl/%s" % ep
        present = self.g("test -d %s && echo present" % root)[1].strip() == "present"
        stages = self.stages(root, "init")
        code, so, se = self.fnv(ep, "status")
        rec["init_cut"] = {"store": "present" if present else "absent", "stages": stages,
                           "status": [code, (so + se)[-300:]],
                           "listing": self.g("ls -la /pl | head -40")[1]}
        findings = []
        if done == 0 and code != 0:
            # init's exit 0 reached the client and its store is not there
            violations.append("init-acknowledged-then-lost:%s" % (so + se).strip()[-120:])
        if present:
            if code != 0 or not re.search(r"(?m)^transactions=0 articles=0", so):
                if a.legacy_init:
                    findings.append("init-cut-left-a-partial-store:%s" % (so + se).strip()[-160:])
                    self.g("rm -rf %s" % root)
                    present = False
                else:
                    violations.append("init-partial-store:status-%d:%s" % (code, (so + se).strip()[-160:]))
                    return
            elif stages:
                # the rename landed and the stage's removal did not: the next
                # init must refuse (publication-uncertain), recover must open
                rc, so2, se2 = self.fnv(ep, "init", *a.init_flags.split(), GROUP)
                rec["init_cut"]["reinit"] = [rc, (so2 + se2)[-300:]]
                if rc != 1 or "publication-uncertain" not in so2 + se2:
                    violations.append("init-uncertain-not-named:init-%d" % rc)
                self.g("rm -rf %s" % " ".join(stages))
            if present:
                if findings:
                    rec["findings"] = findings
                    self.finding(rec)
                return
        if len(stages) > 1:
            violations.append("init-stages-%d" % len(stages))
            return
        rc, so2, se2 = self.fnv(ep, "init", *a.init_flags.split(), GROUP)
        rec["init_cut"]["reinit"] = [rc, (so2 + se2)[-300:]]
        if stages and not a.legacy_init:
            want = "reason=interrupted-init stage=%s" % stages[0]
            if rc != 1 or want not in so2 + se2:
                violations.append("init-leftover-not-named:init-%d:%s" % (rc, (so2 + se2).strip()[-160:]))
                return
            self.g("rm -rf %s" % stages[0])
            rc, so2, se2 = self.fnv(ep, "init", *a.init_flags.split(), GROUP)
            rec["init_cut"]["init_after_removal"] = [rc, (so2 + se2)[-300:]]
        if rc != 0:
            if a.legacy_init:
                findings.append("init-cut-left-a-store-neither-open-nor-init:%s" % (so2 + se2)[-160:])
                self.g("rm -rf %s %s.init-*" % (root, root))
                rc, so2, se2 = self.fnv(ep, "init", *a.init_flags.split(), GROUP)
                rec["init_cut"]["reinit_after_rm"] = [rc, (so2 + se2)[-300:]]
            if rc != 0:
                violations.append("init-stuck:init-%d:%s" % (rc, (so2 + se2).strip()[-160:]))
        if findings:
            rec["findings"] = findings
            self.finding(rec)

    def import_cfg(self, ep):
        """The import target: a second configuration naming ROOT2 = /pl/EPi."""
        self.g("printf %s > /var/pl/%si.toml; sync" % (shlex.quote(cfg_text(ep + "i")), ep))
        return "/var/pl/%si.toml" % ep

    def fni(self, ep, *verb, timeout=900):
        return self.g("cd /var/pl && %s operator /var/pl/%si.toml %s" % (FN, ep, " ".join(shlex.quote(v) for v in verb)),
                      timeout=timeout)

    def check_import(self, ep, rec, violations):
        """After a cut during `store import` onto ROOT2 (fn-bs-imp-program):
        ROOT2 absent (at most one ROOT2.import-*, named by the next import,
        which succeeds once it is removed) or the complete imported store:
        status 0 with the source's transactions=N and sampled Message-IDs'
        `store inspect` equal.  The source store is judged by the oracle."""
        root2 = "/pl/%si" % ep
        archive = "/pl/%s.archive" % ep
        present = self.g("test -d %s && echo present" % root2)[1].strip() == "present"
        stages = self.stages(root2, "import")
        r = {"store2": "present" if present else "absent", "stages": stages}
        rec["import_check"] = r
        if not present:
            if len(stages) > 1:
                violations.append("import-stages-%d" % len(stages))
                return
            code, so, se = self.fni(ep, "store", "import", archive, timeout=1800)
            r["reimport"] = [code, (so + se)[-300:]]
            if stages:
                want = "reason=interrupted-import stage=%s" % stages[0]
                if code != 1 or want not in so + se:
                    violations.append("import-leftover-not-named:import-%d:%s" % (code, (so + se).strip()[-160:]))
                    return
                self.g("rm -rf %s" % stages[0])
                code, so, se = self.fni(ep, "store", "import", archive, timeout=1800)
                r["import_after_removal"] = [code, (so + se)[-300:]]
            if code:
                violations.append("import-stuck:import-%d:%s" % (code, (so + se).strip()[-160:]))
                return
        elif stages:
            code, so, se = self.fni(ep, "store", "import", archive, timeout=1800)
            r["reimport_over_present"] = [code, (so + se)[-300:]]
            if code != 1:
                violations.append("import-over-present-root2:import-%d" % code)
            self.g("rm -rf %s" % " ".join(stages))
        c1, so1, se1 = self.fnv(ep, "status")
        c2, so2, se2 = self.fni(ep, "status")
        n1 = re.search(r"(?m)^transactions=(\d+) articles=", so1)
        n2 = re.search(r"(?m)^transactions=(\d+) articles=", so2)
        r["status2"] = [c2, (so2 + se2)[-300:]]
        # the archive was taken with the owner stopped: the source's count at
        # export is the imported store's; the source may have grown since
        # (the posting cut after this phase has not happened yet), so compare
        # with the count the export recorded
        want = rec.get("export_transactions") or (n1.group(1) if n1 else None)
        if c2 or not n2 or n2.group(1) != str(want):
            violations.append("import-incomplete:status-%d:transactions=%s want %s"
                              % (c2, n2.group(1) if n2 else None, want))
            return
        e = self.oracle.epoch(ep)
        sample = sorted(m for m in e["pin"])[:: max(1, len(e["pin"]) // 6)][:6]
        for mid in sample:
            a_ = self.fnv(ep, "store", "inspect", mid)
            b_ = self.fni(ep, "store", "inspect", mid)
            if a_[:2] != b_[:2]:
                violations.append("import-inspect-differs:%s" % mid)
                break
        r["inspected"] = len(sample)

    def post_until_stop(self, ep, rec, owner):
        """Post for a while, then stop the owner in order (the offline verbs
        need the store lock)."""
        e = self.oracle.epoch(ep)
        nxt = [0, 0]
        for mid in e["attempt"]:
            tid, i = int(mid.split("-")[2]), int(mid.split("-")[3].split("@")[0])
            nxt[tid] = max(nxt[tid], i + 1)
        state = {"lock": threading.Lock(), "next": nxt, "acks": 0}
        stop = threading.Event()
        ths = [threading.Thread(target=poster, args=(self.cfg["nntp"], ep, tid, state, stop,
                                                     self.dir / "oracle.jsonl", self.a.refuse_every,
                                                     random.Random(self.rng.random())), daemon=True)
               for tid in (0, 1)]
        for t in ths:
            t.start()
        time.sleep(self.rng.uniform(1.0, 3.0))
        stop.set()
        for t in ths:
            t.join(timeout=120)
        rec["owner_stop"] = self.owner_stop(owner)
        self.oracle = Oracle(self.dir / "oracle.jsonl")

    def rerun_after(self, ep, prev, rec, violations):
        verb = prev.get("pending_rerun")
        if not verb:
            return
        if verb == "import":
            rec["export_transactions"] = prev.get("export_transactions")
            self.check_import(ep, rec, violations)
            return
        code, so, se = self.fnv(ep, "store", verb)
        rec["rerun"] = [verb, code, (so + se).strip()[-300:]]
        rec["rerun_head"] = (so + se).strip()[:1500]
        done = code == 0 or (code == 1 and re.search(r"already|nothing|no ", so + se))
        if not done:
            violations.append("rerun-%s-exit-%d" % (verb, code))
        if verb == "reclaim" and done:
            self.oracle.log(tag="reclaim", state="done")


def plan_epoch(k):
    """The phases of one epoch: an init cut, ordinary commits, captures, two
    compactions, an interrupted recovery, and the reclaim that ends it."""
    return (["init"] + ["post"] * 4 + ["checkpoint"] * 2 + ["compact"] + ["post"] * 4
            + ["recovery-interrupted"] + ["checkpoint"] * 2 + ["post"] * 3 + ["compact"]
            + ["post"] * 2 + ["import", "post", "reclaim", "after-reclaim"])


def campaign(a):
    c = Campaign(a)
    status = c.dir / "status.txt"
    for k in range(a.epochs):
        ep = c.new_epoch()
        prev = {}
        for phase in plan_epoch(k):
            if c.cycle >= a.max_cycles:
                return 0
            try:
                rec = c.run_cycle(phase, ep, prev)
            except Exception as ex:
                rec = {"cycle": c.cycle, "phase": phase, "ep": ep, "violations": ["driver:%r" % ex]}
                append(c.cuts, **rec)
                try:
                    c.vm.kill()
                except Exception:
                    pass
                status.write_text("cycle %d driver error %r\n" % (c.cycle, ex))
                return 3
            status.write_text("cycle %d epoch %s phase %s v=%s oracle=%s\n"
                              % (c.cycle, ep, phase, rec.get("violations"), rec.get("oracle")))
            if rec.get("violations"):
                break
            prev = rec
    return 0


def initcuts(a):
    """Cuts during `operator init` only: each a new store (epoch), then one
    ordinary posting cut on it."""
    c = Campaign(a)
    for k in range(a.epochs):
        ep = c.new_epoch()
        try:
            rec = c.run_cycle("init", ep, {})
        except Exception as ex:
            append(c.cuts, cycle=c.cycle, phase="init", ep=ep, violations=["driver:%r" % ex])
            c.vm.kill()
            return 3
        (c.dir / "status.txt").write_text("cycle %d init %s F=%s V=%s\n" % (c.cycle, ep, rec.get("findings"), rec.get("violations")))
    return 0


# ---------------------------------------------------------------------------
# Preparation and the flush probe.

def prepare(a):
    base = Path(a.base)
    d = base / a.name
    d.mkdir(parents=True, exist_ok=True)
    cfg = {"name": a.name, "cache": a.cache, "softdep": a.softdep, "ssh": a.ssh, "nntp": a.nntp,
           "trace": a.trace, "format": a.format, "ffs": a.ffs, "smp": a.smp, "mem": a.mem}
    (d / "cfg.json").write_text(json.dumps(cfg, indent=1))
    for f in ("root.qcow2", "root.img", "store.qcow2", "store.img"):
        if (d / f).exists():
            (d / f).unlink()
    # a raw root: every write the guest completed is in the host file (a
    # qcow2 overlay would lose cluster allocations qemu had not flushed, and
    # the guest never flushes)
    if a.root_from:
        # another configuration's root (e.g. one with a newer release
        # installed), copied sparse
        print(run(["cp", "--sparse=always", str(base / a.root_from / "root.img"), str(d / "root.img")], timeout=5400))
    else:
        print(qemu_img(base, "convert", "-O", "raw", "-S", "4k", "/pl/vm/root-base.qcow2", "/pl/%s/root.img" % a.name))
    print(qemu_img(base, "create", "-f", a.format, "/pl/%s/%s" % (a.name, store_file(cfg)), a.store_size))
    vm = VM(base, cfg)
    print("boot", vm.start())
    code, so, se = vm.ssh("sh -s <<'EOF'\n" + GUEST_PREP.replace("NEWFS_FLAGS", "-O %d" % a.ffs) + PFRDR + "\nEOF\n", timeout=900)
    (d / "prepare.log").write_text(so + se)
    print(so[-3000:], se[-2000:])
    vm.shutdown()
    return 0


def install(a):
    """Install a release tarball in a configuration's root disk, under
    /usr/local/fn-REV12 (a wxallowed file system), and check its version."""
    base = Path(a.base)
    cfg = json.loads((base / a.name / "cfg.json").read_text())
    vm = VM(base, cfg)
    vm.boots = 800
    print("boot", vm.start())
    tb = Path(a.tarball)
    m = re.match(r"fn-([0-9a-f]{12})-openbsd-amd64\.tar\.gz$", tb.name)
    if not m:
        raise SystemExit("not an OpenBSD release tarball name: %s" % tb.name)
    dest = "/usr/local/fn-%s" % m.group(1)
    code, so, se = run(["scp", "-q", "-P", str(cfg["ssh"]), "-i", str(vm.key), "-o", "StrictHostKeyChecking=no",
                        "-o", "UserKnownHostsFile=/dev/null", "-o", "LogLevel=ERROR", str(tb), "root@127.0.0.1:/tmp/"])
    print("scp", code, se)
    code, so, se = vm.ssh("rm -rf %s && mkdir -p %s && tar -xzf /tmp/%s -C %s && rm /tmp/%s && cd %s/fn && sha256 -c SHA256SUMS | grep -vc ': OK$'; "
                          "%s/fn/bin/fn --version; sync" % (dest, dest, tb.name, dest, tb.name, dest, dest))
    print(code, so, se)
    vm.shutdown()
    return 0 if ("fn " + m.group(1)) in so else 1


def flushprobe(a):
    """Count the flushes the guest sends while N fsyncs run on the store file
    system (the trace records every paio request qemu submits to the host
    file: type 0x4 is a flush)."""
    base = Path(a.base)
    cfg = json.loads((base / a.name / "cfg.json").read_text())
    vm = VM(base, cfg)
    vm.boots = 900
    boot = vm.start()
    rec = {"boot": boot}
    opts = "-o softdep " if cfg["softdep"] else ""
    rec["mount"] = vm.ssh("mount %s/dev/sd1a /pl; mount | grep ' /pl '" % opts)[1]
    prog = r"""
cat > /tmp/fs.c <<'EOF'
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
int main(int c, char **v) { int n = atoi(v[2]); int fd = open(v[1], O_WRONLY|O_CREAT|O_APPEND, 0600);
 char b[4096]; memset(b, 'x', sizeof b); for (int i = 0; i < n; i++) { write(fd, b, sizeof b); if (v[3][0]=='y') fsync(fd); } close(fd); return 0; }
EOF
cc -O2 -o /tmp/fs /tmp/fs.c
"""
    rec["cc"] = vm.ssh("rm -f /root/sbcl.core;" + prog)
    def flushes():
        """qemu's own count of the guest's flush requests to the store disk
        (HMP `info blockstats`, the second virtio drive: virtio1)."""
        out = hmp(base / a.name / "monitor.sock", "info blockstats")
        m = re.search(r"virtio1:.*?flush_operations=(\d+).*?wr_operations=(\d+)|virtio1:(.*)", out, re.S)
        blk = out.split("virtio1:")[1] if "virtio1:" in out else ""
        f = re.search(r"flush_operations=(\d+)", blk)
        w = re.search(r"wr_operations=(\d+)", blk)
        return int(f.group(1)) if f else -1, int(w.group(1)) if w else -1

    time.sleep(3)
    for label, cmd in (("idle-5s", "sleep 5"),
                       ("write-100-nofsync", "/tmp/fs /pl/probe-a 100 n"),
                       ("write-100-fsync", "/tmp/fs /pl/probe-b 100 y"),
                       ("sync", "sync"),
                       ("write-100-fsync-again", "/tmp/fs /pl/probe-c 100 y"),
                       ("umount", "umount /pl")):
        f0, n0 = flushes()
        t0 = time.time()
        vm.ssh(cmd)
        time.sleep(1)
        f1, n1 = flushes()
        rec[label] = {"flushes": f1 - f0, "writes": n1 - n0, "wall": round(time.time() - t0, 2)}
    vm.ssh("mount /dev/sd1a /pl && rm -f /pl/probe-a /pl/probe-b /pl/probe-c && umount /pl")
    rec["blockstats"] = hmp(base / a.name / "monitor.sock", "info blockstats")
    vm.shutdown()
    out = json.dumps(rec, indent=1, default=str)
    (base / a.name / "flushprobe.json").write_text(out)
    print(out)
    return 0


def summary(a):
    base = Path(a.base)
    tot = {}
    for d in sorted(base.iterdir()):
        f = d / "cuts.jsonl"
        if not f.exists():
            continue
        cfg = json.loads((d / "cfg.json").read_text())
        rows = [json.loads(l) for l in f.read_text().splitlines()]
        per = {}
        viol = []
        for r in rows:
            if r.get("tag") == "rerun":
                if r.get("violations"):
                    viol.append((r["cycle"], "rerun", r["violations"]))
                continue
            ph = r["phase"]
            if r.get("phase_cut_t"):
                per[ph] = per.get(ph, 0) + 1
            if r.get("cut_t"):
                k = r.get("work") or ph
                if ph in ("init", "recovery-interrupted"):
                    k = "post"
                per[k] = per.get(k, 0) + 1
            if ph == "after-reclaim":
                per[ph] = per.get(ph, 0) + 1
            if r.get("violations"):
                viol.append((r["cycle"], ph, r["violations"]))
        orc = Oracle(d / "oracle.jsonl")
        acked = sum(len(e["ack"]) for e in orc.eps.values())
        print(d.name, "store=%s cache=%s ffs=%s softdep=%s" % (cfg.get("format", "qcow2"), cfg["cache"], cfg.get("ffs"), cfg["softdep"]),
              per, "acked=%d" % acked)
        for ep, e in sorted(orc.eps.items()):
            print("   epoch %s acked=%d refused=%d attempted=%d pinned=%d reclaim=%s dead=%s"
                  % (ep, len(e["ack"]), len(e["refuse"]), len(e["attempt"]), len(e["pin"]), e["reclaim"], e["dead"]))
        for v in viol:
            print("   VIOLATION", v)
        for k, n in per.items():
            tot[k] = tot.get(k, 0) + n
    print("total", tot)
    return 0


def main(argv=None):
    global FN
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--base", default="/tank/fn/scratch/power-loss-openbsd")
    ap.add_argument("--fn", default=FN, help="the guest's installed bin/fn (the release under test)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("prepare")
    p.add_argument("name")
    p.add_argument("--cache", choices=("writeback", "unsafe", "writethrough", "none", "directsync"), required=True)
    p.add_argument("--softdep", action="store_true")
    p.add_argument("--ssh", type=int, required=True)
    p.add_argument("--nntp", type=int, required=True)
    p.add_argument("--store-size", default="4G")
    p.add_argument("--format", choices=("raw", "qcow2"), default="qcow2")
    p.add_argument("--trace", action="store_true")
    p.add_argument("--ffs", type=int, choices=(1, 2), default=1,
                   help="the store file system: FFS1 (newfs -O 1, the docs' rule) or FFS2 (the installer's)")
    p.add_argument("--smp", type=int, default=1)
    p.add_argument("--mem", type=int, default=2048, help="guest memory in MiB")
    p.add_argument("--root-from", help="copy this configuration's root disk instead of the clone")
    p = sub.add_parser("install")
    p.add_argument("name")
    p.add_argument("tarball")
    p = sub.add_parser("flushprobe")
    p.add_argument("name")
    p = sub.add_parser("campaign")
    p.add_argument("name")
    p.add_argument("--init-window", type=lambda v: tuple(float(x) for x in v.split(",")), default=(0.0, 1.1),
                   help="the init cut falls uniformly in [LO, HI] x the last completed init's wall "
                        "(most of an init's wall is the process start and heap probe, before any write)")
    p.add_argument("--legacy-init", action="store_true",
                   help="a release before PKT-647: a half store after an init cut is a finding")
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--epochs", type=int, default=1)
    p.add_argument("--max-cycles", type=int, default=10 ** 6)
    p.add_argument("--max-post-s", type=float, default=6.0)
    p.add_argument("--refuse-every", type=int, default=7)
    p.add_argument("--keep-disk", action="store_true")
    # the small preset's fields (a 2 GB guest: the installed launcher refuses
    # scale, heap 54,751 MB) with a small open suffix so captures run often
    p.add_argument("--init-flags", default="--max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-article-octets 8192 --max-groups-per-article 16 --max-open-suffix 16")
    p = sub.add_parser("initcuts")
    p.add_argument("name")
    p.add_argument("--init-window", type=lambda v: tuple(float(x) for x in v.split(",")), default=(0.0, 1.1),
                   help="the init cut falls uniformly in [LO, HI] x the last completed init's wall "
                        "(most of an init's wall is the process start and heap probe, before any write)")
    p.add_argument("--legacy-init", action="store_true",
                   help="a release before PKT-647: a half store after an init cut is a finding")
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--epochs", type=int, default=10)
    p.add_argument("--max-post-s", type=float, default=4.0)
    p.add_argument("--refuse-every", type=int, default=7)
    p.add_argument("--keep-disk", action="store_true")
    p.add_argument("--init-flags", default="--max-transactions 16384 --max-history-octets 8388608 --max-record-octets 196608 --max-article-octets 8192 --max-groups-per-article 16 --max-open-suffix 16")
    p = sub.add_parser("summary")
    a = ap.parse_args(argv)
    FN = a.fn
    return {"prepare": prepare, "install": install, "flushprobe": flushprobe, "campaign": campaign, "initcuts": initcuts, "summary": summary}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
