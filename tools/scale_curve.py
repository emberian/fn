#!/usr/bin/env python3
"""Scale evidence by curve: probe an image at N = 1k .. 100k, fit, extrapolate.

ember, 2026-09-28: "instead of doing all these expensive replays at 1M, we
can simply extrapolate from the curve at 1k 2k 5k 10k 25k 50k 100k ...
2-4 minutes of performance probing instead of doing the whole thing that we
know is expensive."  closeout-common's SCALE BY CURVE section is the rule;
this is the one way every lane probes.

    scale_curve.py box --image HBOX_IMAGE [run options] [--out LOCAL_DIR]
        (laptop) reserves hbox (tools/boxes.sh reserve), ships this file,
        runs `run` there detached, waits on its status file, fetches
        curve.json and curve.md, releases the reservation, prints the table.
    scale_curve.py run --image IMAGE [--probes P,..] [--ns N,..] [--jobs J]
                       [--fixtures DIR] [--out DIR] [--mem 24G]
        (hbox) every probe at every N; writes DIR/curve.json, DIR/curve.md.
    scale_curve.py fit CURVE.json [--known SERIES=VALUE@N ...] [--md]
        (anywhere) refits a curve and compares it with measured points.
    scale_curve.py list
        the probes and their series.

FIXTURES.  tools/fixtures.py's `curve` fixture: one 1,000-article seed and,
from it, a synthesized log per N (tools/synth_log_store.py writes the log
directly; nothing is POSTed past the seed), at
hbox:/tank/fn/scratch/fixtures/curve/nN/store.  Build it once per store
format: `python3 tools/fixtures.py rebuild --only curve --image
build/fn-host-developer --rev REV` in a tools/hbox_native.sh tree.  Every
point shares the seed's node, profile (SYNTH_100K) and payloads, so the
curve varies N alone.  A point copies its store to --work (default /dev/shm)
and never opens the fixture in place.

A POINT, per N, in its own `systemd-run --user --scope -p MemoryMax` and on
its own cores (taskset), runs the stages in order, each stage's built-in
measurement first and then the selected probes of that stage:

  replay      the owner (`IMAGE --fn operator CFG run`) opens the copy by full
              replay: seconds exec -> LISTENING, VmHWM / VmRSS at LISTENING,
              the anonymous peak (RssAnon sampled every 20 ms), the stop.
  checkpoint  `IMAGE --fn store ROOT checkpoint` offline: seconds, peak, the
              checkpoint's octets (its report line).  Bytes consed are not
              exposed by the production image: absent, never estimated.
  served      the owner opens again, now from that checkpoint: the same open
              figures, then the probes against it (one client, serial:
              latency at N, not throughput under load), then the stop.
  offline     verbs with no owner: digest, export.

A PROBE is a function of one stage that returns {metric: number}; its
series is PROBE.metric.  Adding one is a few lines here:

    @probe("served")
    def listgroup(pt):
        '''LISTGROUP fn.test: one command over the whole group.'''
        with pt.client() as c:
            return {"ms": c.timed("LISTGROUP fn.test", multi=True)}

`pt` has .n, .store, .config, .work, .image, .env, .owner (a live Owner in
the replay and served stages: .pid, .port, .memory()), .client() (an NNTP
client: .cmd, .timed, .multi), .verb(words) (a timed `operator CFG ...`
against the live owner) and .offline(words) (a timed `store ROOT ...`).

THE FIT.  Each series is fitted against N with five models, y = a + b g(N)
for g = 1 (constant), log N, N, N log N, N^2, by least squares on RELATIVE
error (every point counts, not only the largest), b >= 0.  A model's rise
over the measured range must exceed twice its residual, or its N-dependence
is noise and it counts as the constant.  The chosen model is the simplest
within 10% (+0.005) of the least residual; the output names it, its
residual, a power law's exponent k (y ~ N^k, a cross-check), and the
extrapolation to 1M and 10M.  A series is FLAGGED, which is the only case where a real large run is
justified (closeout-common), when:
  ambiguous  another model fits within 1.5x the best residual (or +0.05) and
             extrapolates to 1M more than 1.5x apart;
  bend       the chosen model fitted on N <= 25k UNDER-predicts the measured
             100k point by more than 30% (and twice the noise): a threshold, a
             cache boundary, heap growth;
  steepens   the last segment's log-log slope exceeds the fitted model's over
             the same segment by more than 0.4, and the last point sits above
             the model by more than twice the noise;
  threshold  a known phase transition (THRESHOLDS: the open nursery trigger,
             the automatic checkpoint, the transaction budget) lies inside the
             measured range and the segment containing it bends as `steepens'
             does; every crossing is listed with the fit either way;
  failed     a point is missing (a probe failed or timed out at some N).
Stack depth and heap exhaustion are the depth lint's and the heap model's
questions, not a large run's.

VARIANTS (run by name with --probes, never in the standard set) force a
phase transition at small N or cost minutes at 100k: auto_checkpoint (the
owner's automatic checkpoint under POSTs), pinned_reader (an old reader
while 500 POSTs land), reclaim (the reclamation walk).  The first-read
latencies after an open (cold) are in `reads'.

WHEN A 1M RUN IS STILL REQUIRED (GPT-6's review 2026-09-28, section Scale):
curves are for iteration; ADVERTISING 1M support needs one real held-out 1M
run per release (the prerelease checklist), compared with the curve's
extrapolation (`fit --known SERIES=VALUE@1000000`, which also prints the
load-free ratio between two measured points against the model's).  A curve
also cannot answer a flagged series.  Measurement campaigns run in the
prerelease checklist, not during development (ember 2026-09-28 18:15Z).

Never touches /tank/fn/node.  The box's load at the start and end of every
task is recorded beside it; a curve taken at a different load is a
different curve (the SHAPE is comparable, the seconds are not): reserve the
box (`box` does, tools/boxes.sh).
"""
from __future__ import annotations

import argparse
import contextlib
import datetime as dt
import json
import math
import os
from pathlib import Path
import random
import re
import select
import shlex
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time

HERE = Path(__file__).resolve()
NS = (1000, 2000, 5000, 10000, 25000, 50000, 100000)
FIXTURES = "/tank/fn/scratch/fixtures/curve"
BOX = "hbox"
BOX_RUNS = "/tank/fn/scratch/scale-curve/runs"
STEP_TIMEOUT = 900
STAGES = ("replay", "checkpoint", "served", "offline")

# ---------------------------------------------------------------------------
# Probes.

PROBES: dict[str, tuple[str, object]] = {}
# Probes that force a phase transition or cost minutes at 100k: run by name
# (--probes), never in the standard set.
VARIANTS: set[str] = set()


def probe(stage, variant=False):
    if stage not in STAGES:
        raise ValueError(stage)

    def register(fn):
        PROBES[fn.__name__] = (stage, fn)
        if variant:
            VARIANTS.add(fn.__name__)
        return fn
    return register


def standard_probes():
    return [p for p in PROBES if p not in VARIANTS]


def pct(values, q):
    if not values:
        return None
    v = sorted(values)
    return v[min(len(v) - 1, int(round(q * (len(v) - 1))))]


def summary(name, seconds):
    ms = [s * 1000 for s in seconds]
    name = name + "_" if name else ""
    return {name + "p50_ms": pct(ms, 0.5), name + "p99_ms": pct(ms, 0.99)}


@probe("replay")
def open_replay(pt):
    """The owner's open by full replay: seconds to LISTENING and memory then."""
    return dict(pt.owner.opened)


@probe("replay", variant=True)
def auto_checkpoint(pt):
    """Forces the owner's automatic checkpoint (a phase transition): the replay-opened
    owner's suffix is N, and the publication is due at 2 x suffix >= K (N >= 32,768
    with the fixture's K 65,536; books/owner-checkpoint-open.lisp
    fn-ock-publication-duep), checked between accepts.  200 serial POSTs (the
    publication starts at the first), then waits up to 300 s for its
    `CHECKPOINT auto' line (printed when it ends): fired (0/1), the
    publication's ms= and octets=, and the POST latencies while it ran."""
    seconds, fired = [], None
    with pt.client() as c:
        for i in range(200):
            seconds.append(post_one(c, "ack%d" % pt.n, i))
    deadline = time.monotonic() + (300 if pt.n >= 16384 else 2)
    while fired is None and time.monotonic() < deadline:
        fired = next((l for l in pt.owner.stderr().splitlines()
                      if l.startswith("CHECKPOINT auto")), None)
        time.sleep(0.5)
    out = summary("post", seconds)
    out["post_max_ms"] = max(seconds) * 1000
    out["fired"] = 1 if fired and "sequence=" in fired else 0
    for key in ("ms", "octets"):
        m = re.search(r"\b%s=(\d+)" % key, fired or "")
        if m:
            out[key] = int(m.group(1))
    return out


@probe("replay")
def stop_replay(pt):
    """SIGTERM to exit, the owner opened by replay and idle."""
    return {"s": pt.stop_owner()}


@probe("checkpoint")
def checkpoint(pt):
    """`store ROOT checkpoint` offline (a full replay, then the publication)."""
    r = pt.offline(["checkpoint"])
    m = re.search(rb"octets=(\d+)", r["stdout"])
    out = {"s": r["s"], "peak_hwm_kib": r["hwm_kib"], "anon_peak_kib": r["anon_peak_kib"]}
    if m:
        out["octets"] = int(m.group(1))
    if r["rc"] != 0:
        raise ProbeError("checkpoint exit {}: {}".format(r["rc"], r["stderr"][-300:]))
    return out


@probe("served")
def open_checkpoint(pt):
    """The owner's open from the checkpoint: seconds to LISTENING and memory then."""
    if "checkpoint" not in pt.owner.open_line:
        raise ProbeError("the served open was not from a checkpoint: " + pt.owner.open_line)
    return dict(pt.owner.opened)


@probe("served")
def reads(pt):
    """One client: the first ARTICLE, OVER and HDR after the open (cold), then
    GROUP x20, ARTICLE x200 at random numbers, OVER and HDR Subject over
    100-article windows x50, and HDR Subject over the whole range once."""
    rng = random.Random(pt.n)
    g, a, o, h = [], [], [], []
    out = {}
    with pt.client() as c:
        # The first read of each kind after the open: cold (nothing touched yet).
        line = c.cmd("GROUP fn.test")
        _, _, lo, hi = line.split()[:4]
        lo, hi = int(lo), int(hi)
        k = rng.randint(lo, max(lo, hi - 99))
        out["first_article_ms"] = c.timed("ARTICLE %d" % k, multi=True) * 1000
        out["first_over100_ms"] = c.timed("OVER %d-%d" % (k, k + 99), multi=True) * 1000
        out["first_hdr100_ms"] = c.timed("HDR Subject %d-%d" % (k, k + 99), multi=True) * 1000
        for _ in range(20):
            t = time.perf_counter(); line = c.cmd("GROUP fn.test"); g.append(time.perf_counter() - t)
        _, _, lo, hi = line.split()[:4]
        lo, hi = int(lo), int(hi)
        for _ in range(200):
            k = rng.randint(lo, hi)
            a.append(c.timed("ARTICLE %d" % k, multi=True))
        for _ in range(50):
            k = rng.randint(lo, max(lo, hi - 99))
            o.append(c.timed("OVER %d-%d" % (k, k + 99), multi=True))
            h.append(c.timed("HDR Subject %d-%d" % (k, k + 99), multi=True))
        whole = c.timed("HDR Subject %d-%d" % (lo, hi), multi=True)
    for name, v in (("group", g), ("article", a), ("over100", o), ("hdr100", h)):
        out.update(summary(name, v))
    out["hdr_all_ms"] = whole * 1000
    return out


def control(pt, verb, answered=(0,)):
    runs = [pt.verb([verb]) for _ in range(3)]
    bad = [r for r in runs if r["rc"] not in answered]
    if bad:
        raise ProbeError("{} exit {}: {}".format(verb, [r["rc"] for r in bad],
                                                 " ".join(bad[0]["stderr"].split())[-300:]))
    out = summary("", [r["s"] for r in runs])
    out["exit"] = runs[-1]["rc"]
    return out


@probe("served")
def status(pt):
    """The live `operator CFG status`, three times."""
    return control(pt, "status")


@probe("served")
def health(pt):
    """The live `operator CFG health`, three times; a held state (exit 19-28,
    books/native-health.lisp) is an answer, recorded as health.exit."""
    return control(pt, "health", answered=(0, 19) + tuple(range(20, 29)))


@probe("served")
def posts(pt):
    """K = 50 serial POSTs of about 2 KiB, then the owner's memory."""
    with pt.client() as c:
        seconds = [post_one(c, "k%d" % pt.n, i) for i in range(50)]
    out = summary("post", seconds)
    mem = pt.owner.memory()
    out.update({"after_rss_kib": mem.get("VmRSS"), "after_hwm_kib": mem.get("VmHWM"),
                "after_anon_peak_kib": pt.owner.anon_peak})
    return out


def post_one(c, tag, i):
    art = (("From: curve <c@curve.invalid>\r\nNewsgroups: fn.test\r\nSubject: curve %s %d\r\n"
            "Message-ID: <curve-%s-%d-%d@curve.invalid>\r\n\r\n" % (tag, i, tag, i, os.getpid()))
           + ("scale curve probe line %06d\r\n" % i) * 64).encode()
    t = time.perf_counter()
    r = c.cmd("POST")
    if r.startswith("340"):
        c.sock.sendall(art + b".\r\n")
        r = c.line()
    if not r.startswith("240"):
        raise ProbeError("POST %s %d: %s" % (tag, i, r))
    return time.perf_counter() - t


# ML-DSA-65 key generation needs OpenSSL 3.5; hbox's toolchain has it.
OPENSSL = os.environ.get("FN_OPENSSL", "/tank/fn/toolchains/openssl-3.5.8/bin/openssl")
SIGNED_K = 20


def owner_cpu_s(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) / os.sysconf("SC_CLK_TCK")


@probe("served", variant=True)
def signed_posts(pt):
    """K = 20 serial hybrid-signed POSTs of about 2 KiB (Q5b; the harness of
    planning/evidence/signed-post-linear-2026-09-26/prof_signed.py): one
    author enrolled through the control socket, K + 1 carriers signed by the
    image's own hybrid-sign-carrier (not timed), one warm signed POST, then K
    on one connection opened before them: the latency from POST to 240 and
    the owner's CPU (utime + stime) per POST over the batch."""
    keys = pt.work / "signed-keys"
    keys.mkdir(exist_ok=True)
    principal = keys / "principal.bin"
    principal.write_bytes(bytes([0x55]) * 32)
    edp, eds = keys / "ed-public.bin", keys / "ed-secret.bin"
    # RFC 8032 section 7.1 test 1.
    edp.write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
    eds.write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                                  "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
    mlpriv, mlpub = keys / "ml-private.pem", keys / "ml-public.pem"
    for argv in ([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(mlpriv)],
                 [OPENSSL, "pkey", "-in", str(mlpriv), "-pubout", "-out", str(mlpub)]):
        r = subprocess.run(argv, env=pt.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if r.returncode:
            raise ProbeError("openssl: " + r.stderr.decode("utf-8", "replace")[-300:])

    def fn(*args):
        r = pt.timed_process([str(pt.image), "--fn"] + [str(a) for a in args])
        if r["rc"]:
            raise ProbeError("{} -> {}: {}".format(args[0], r["rc"], r["stderr"][-400:]))

    fn("hybrid-enroll", pt.work / "control.sock", "1", principal, edp, mlpub)
    body = b"".join(b"signed curve line %05d " % i + b"x" * 50 + b"\r\n" for i in range(22))
    carriers = []
    for i in range(SIGNED_K + 1):
        src, out = keys / ("s%d.eml" % i), keys / ("s%d-carried.eml" % i)
        src.write_bytes(b"From: curve <c@curve.invalid>\r\nDate: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                        b"Newsgroups: fn.test\r\nSubject: signed curve %d\r\n"
                        b"Message-ID: <signed-curve-%d-%d-%d@curve.invalid>\r\n\r\n"
                        % (i, pt.n, i, os.getpid()) + body)
        fn("hybrid-sign-carrier", principal, edp, eds, mlpub, mlpriv, src, out)
        carriers.append(b"".join((b"." + l if l.startswith(b".") else l)
                                 for l in out.read_bytes().splitlines(keepends=True)))

    def post(c, octets):
        t = time.perf_counter()
        r = c.cmd("POST")
        if r.startswith("340"):
            c.sock.sendall(octets + b".\r\n")
            r = c.line()
        if not r.startswith("240"):
            raise ProbeError("signed POST: " + r)
        return time.perf_counter() - t

    with pt.client() as c:
        post(c, carriers[0])
    with pt.client() as c:
        c0 = owner_cpu_s(pt.owner.pid)
        seconds = [post(c, x) for x in carriers[1:]]
        c1 = owner_cpu_s(pt.owner.pid)
    out = summary("signed_post", seconds)
    out["owner_cpu_ms_per_post"] = 1000.0 * (c1 - c0) / SIGNED_K
    return out


@probe("served", variant=True)
def pinned_reader(pt):
    """An old reader: client A selects the group and reads its first article, then
    stays open while client B POSTs 500 articles; then A reads again (its old
    view) and re-selects.  The owner's RSS growth over the 500 and A's latencies
    after them: what an old pinned view costs the owner and the reader."""
    with pt.client() as a, pt.client() as b:
        _, _, lo, hi = a.cmd("GROUP fn.test").split()[:4]
        lo = int(lo)
        a.timed("ARTICLE %d" % lo, multi=True)
        before = pt.owner.memory().get("VmRSS", 0)
        posts = [post_one(b, "pin", i) for i in range(500)]
        after = pt.owner.memory().get("VmRSS", 0)
        out = summary("post", posts)
        out["rss_growth_kib"] = after - before
        out["old_article_ms"] = a.timed("ARTICLE %d" % (lo + 1), multi=True) * 1000
        out["old_over100_ms"] = a.timed("OVER %d-%d" % (lo, lo + 99), multi=True) * 1000
        out["regroup_ms"] = a.timed("GROUP fn.test") * 1000
    return out


@probe("served")
def stop_served(pt):
    """SIGTERM to exit after the served probes."""
    return {"s": pt.stop_owner()}


@probe("offline")
def digest(pt):
    """`store ROOT digest` offline."""
    r = pt.offline(["digest"])
    if r["rc"] != 0:
        raise ProbeError("digest exit {}: {}".format(r["rc"], r["stderr"][-300:]))
    return {"s": r["s"], "peak_hwm_kib": r["hwm_kib"]}


@probe("offline", variant=True)
def reclaim(pt):
    """`operator CFG store reclaim --dry-run` offline: the reclamation walk over the
    log (the default retention reclaims nothing; the walk is the cost)."""
    r = pt.verb(["store", "reclaim", "--dry-run"])
    if r["rc"] != 0:
        raise ProbeError("reclaim exit {}: {}".format(r["rc"], r["stderr"][-300:]))
    return {"s": r["s"], "peak_hwm_kib": r["hwm_kib"]}


@probe("offline")
def export(pt):
    """`store ROOT export ARCHIVE` offline, the archive beside the copy."""
    archive = pt.work / "export"
    shutil.rmtree(archive, ignore_errors=True)
    r = pt.offline(["export", str(archive)])
    if r["rc"] != 0:
        raise ProbeError("export exit {}: {}".format(r["rc"], r["stderr"][-300:]))
    shutil.rmtree(archive, ignore_errors=True)
    return {"s": r["s"], "peak_hwm_kib": r["hwm_kib"]}


class ProbeError(Exception):
    pass


# ---------------------------------------------------------------------------
# One point.

@probe("served", variant=True)
def heap(pt):
    """F8 by curve (folded in from tools/fundamentals/f8_curve.py): the live
    heap after a full collection, the collector's garbage, and the process's
    resident set, anonymous memory and threads, on the owner that opened N
    from its checkpoint.  Needs a heap image (tools/fundamentals/
    build_heap_image.sh, whose hook FN_PROF_LOAD loads): on another image
    the snapshot never answers and the probe says so.  tools/f8_breakdown.py
    --curve reads these series."""
    directory = Path(pt.env["FN_HEAP_DIR"])
    tag = "gc-{}".format(pt.n)
    (directory / "go").write_text(tag)
    deadline = time.monotonic() + 600
    while not (directory / ("done-" + tag)).exists():
        if time.monotonic() > deadline:
            raise ProbeError("the heap hook did not answer in 600 s (not a heap image?)")
        time.sleep(0.05)
    doc = {}
    for line in (directory / ("heap-" + tag + ".txt")).read_text().splitlines():
        words = line.split()
        if len(words) == 2 and words[1].isdigit():
            doc[words[0]] = int(words[1])
    status = proc_status(pt.owner.pid)
    try:
        threads = len(os.listdir("/proc/{}/task".format(pt.owner.pid)))
    except OSError:
        threads = None
    return {"live_bytes": doc.get("dynamic-usage-after-gc"),
            "garbage_bytes": doc["dynamic-usage"] - doc["dynamic-usage-after-gc"]
            if "dynamic-usage-after-gc" in doc and "dynamic-usage" in doc else None,
            "rss_kib": status.get("VmRSS"), "hwm_kib": status.get("VmHWM"),
            "anon_kib": status.get("RssAnon"), "threads": threads}


def proc_status(pid):
    out = {}
    try:
        for line in open("/proc/%d/status" % pid):
            key = line.split(":")[0]
            if key in ("VmHWM", "VmRSS", "RssAnon"):
                out[key] = int(line.split()[1])
    except (OSError, ValueError, IndexError):
        pass
    return out


class Sampler:
    """The process's RssAnon peak and last VmHWM, sampled every 20 ms."""
    def __init__(self, pid):
        self.pid, self.anon_peak, self.hwm, self.done = pid, 0, 0, threading.Event()
        threading.Thread(target=self.loop, daemon=True).start()

    def loop(self):
        while not self.done.is_set():
            s = proc_status(self.pid)
            if not s:
                return
            self.anon_peak = max(self.anon_peak, s.get("RssAnon", 0))
            self.hwm = max(self.hwm, s.get("VmHWM", 0))
            self.done.wait(0.02)


class Owner:
    def __init__(self, pt):
        self.pt = pt
        self.err = open(pt.work / "owner.{}.err".format(pt.stage), "wb")
        started = time.monotonic()
        self.proc = subprocess.Popen([str(pt.image), "--fn", "operator", str(pt.config), "run"],
                                     env=pt.env, stdout=subprocess.PIPE, stderr=self.err)
        self.pid, self.port = self.proc.pid, pt.port
        self.sampler = Sampler(self.pid)
        seconds = None
        while seconds is None:
            if not select.select([self.proc.stdout], [], [], STEP_TIMEOUT)[0]:
                self.kill()
                raise ProbeError("no LISTENING in {} s".format(STEP_TIMEOUT))
            line = self.proc.stdout.readline()
            if not line:
                raise ProbeError("the owner exited {} before LISTENING: {}".format(
                    self.proc.wait(), self.stderr()[-400:]))
            if line.startswith(b"LISTENING"):
                seconds = time.monotonic() - started
        threading.Thread(target=lambda: [None for _ in iter(
            lambda: self.proc.stdout.read(4096), b"")], daemon=True).start()
        mem = self.memory()
        self.opened = {"s": seconds, "hwm_kib": mem.get("VmHWM"), "rss_kib": mem.get("VmRSS"),
                       "anon_peak_kib": self.sampler.anon_peak}
        self.open_line = next((l for l in self.stderr().splitlines()
                               if l.startswith("OWNER-OPEN")), "")

    @property
    def anon_peak(self):
        return self.sampler.anon_peak

    def memory(self):
        return proc_status(self.pid)

    def stderr(self):
        return (self.pt.work / "owner.{}.err".format(self.pt.stage)).read_text("utf-8", "replace")

    def stop(self):
        started = time.monotonic()
        if self.proc.poll() is None:
            self.proc.terminate()
        try:
            rc = self.proc.wait(STEP_TIMEOUT)
        except subprocess.TimeoutExpired:
            self.kill()
            raise ProbeError("no exit {} s after SIGTERM".format(STEP_TIMEOUT))
        finally:
            self.sampler.done.set()
            self.err.close()
        if rc != 0:
            raise ProbeError("the owner exited {} on SIGTERM: {}".format(rc, self.stderr()[-400:]))
        return time.monotonic() - started

    def kill(self):
        with contextlib.suppress(OSError):
            self.proc.kill()
        with contextlib.suppress(subprocess.TimeoutExpired):
            self.proc.wait(30)
        self.sampler.done.set()


class Client:
    def __init__(self, port):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=STEP_TIMEOUT)
        self.buf = b""
        self.line()

    def line(self):
        while b"\r\n" not in self.buf:
            d = self.sock.recv(1 << 16)
            if not d:
                raise EOFError("connection closed")
            self.buf += d
        line, self.buf = self.buf.split(b"\r\n", 1)
        return line.decode("latin-1")

    def multi(self):
        n = 0
        while self.line() != ".":
            n += 1
        return n

    def cmd(self, text):
        self.sock.sendall(text.encode() + b"\r\n")
        return self.line()

    def timed(self, text, multi=False):
        t = time.perf_counter()
        r = self.cmd(text)
        if multi and r[:1] == "2":
            self.multi()
        elif r[:1] not in ("2", "3"):
            raise ProbeError("{}: {}".format(text, r))
        return time.perf_counter() - t

    def close(self):
        with contextlib.suppress(OSError, EOFError):
            self.cmd("QUIT")
        self.sock.close()


class Point:
    def __init__(self, n, image, source, work, env):
        self.n, self.image, self.work, self.env = n, Path(image), Path(work), env
        self.store = self.work / "store"
        self.owner, self.stage = None, None
        shutil.rmtree(self.work, ignore_errors=True)
        self.work.mkdir(parents=True)
        started = time.monotonic()
        shutil.copytree(source, self.store, symlinks=True)
        self.copy_s = time.monotonic() - started
        lock = self.store / "writer.lock"
        lock.touch()
        lock.chmod(0o600)
        s = socket.socket(); s.bind(("127.0.0.1", 0)); self.port = s.getsockname()[1]; s.close()
        self.config = self.work / "fn.toml"
        self.config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                               '[control]\npath = "%s"\n' % (self.store, self.port,
                                                            self.work / "control.sock"))

    @contextlib.contextmanager
    def client(self):
        c = Client(self.port)
        try:
            yield c
        finally:
            c.close()

    def timed_process(self, argv):
        started = time.monotonic()
        p = subprocess.Popen(argv, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        sampler = Sampler(p.pid)
        try:
            out, err = p.communicate(timeout=STEP_TIMEOUT)
        except subprocess.TimeoutExpired:
            p.kill()
            out, err = p.communicate()
            raise ProbeError("{} timed out at {} s".format(" ".join(argv[-2:]), STEP_TIMEOUT))
        finally:
            sampler.done.set()
        return {"rc": p.returncode, "s": time.monotonic() - started, "stdout": out,
                "stderr": err.decode("utf-8", "replace"), "hwm_kib": sampler.hwm,
                "anon_peak_kib": sampler.anon_peak}

    def verb(self, words):
        return self.timed_process([str(self.image), "--fn", "operator", str(self.config)] + words)

    def offline(self, words):
        return self.timed_process([str(self.image), "--fn", "store", str(self.store)] + words)

    def stop_owner(self):
        owner, self.owner = self.owner, None
        return owner.stop()


def run_point(args) -> dict:
    """One N: every selected probe, stage by stage.  Prints the point's JSON."""
    tree = Path(args.tree)
    sys.path.insert(0, str(tree / "tools"))
    import native_env  # the tree's: the harness stores' budget, named once
    env = native_env.harness_store_env(dict(os.environ, ACL2_CUSTOMIZATION="NONE"))
    for k in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_PROF_OUT", "FN_PROF_HOOK"):
        env.pop(k, None)
    selected = args.probes.split(",")
    stages = args.stages.split(",")
    if "heap" in selected:
        # The heap image's hook (tools/fundamentals/hook.lisp) answers a tag
        # written into FN_HEAP_DIR; the probe `heap` asks it.
        heap_dir = Path(args.work) / "heap-n{}".format(args.n)
        shutil.rmtree(heap_dir, ignore_errors=True)
        heap_dir.mkdir(parents=True)
        env["FN_HEAP_DIR"] = str(heap_dir)
        env["FN_PROF_LOAD"] = str(tree / "tools" / "fundamentals" / "hook.lisp")
    result = {"n": args.n, "stages": stages, "load_start": open("/proc/loadavg").read().split()[:3],
              "values": {}, "errors": {}, "seconds": {}}
    started = time.monotonic()
    pt = Point(args.n, args.image, Path(args.fixtures) / "n{}".format(args.n) / "store",
               Path(args.work) / "n{}".format(args.n), env)
    result["copy_s"] = round(pt.copy_s, 2)
    skip_rest = None
    try:
        for stage in [s for s in STAGES if s in stages]:
            names = [p for p in selected if PROBES[p][0] == stage]
            need = names or (stage == "checkpoint" and any(PROBES[p][0] == "served" for p in selected))
            if not need:
                continue
            if stage == "checkpoint" and not names:
                names = ["checkpoint"]  # the served stage opens from it
            pt.stage = stage
            if skip_rest:
                for name in names:
                    result["errors"][name] = "not run: " + skip_rest
                continue
            if stage in ("replay", "served"):
                try:
                    pt.owner = Owner(pt)
                except ProbeError as e:
                    for name in names:
                        result["errors"][name] = "open: {}".format(e)
                    if stage == "replay":
                        continue
                    skip_rest = "the served open failed"
                    continue
                result["open_line_" + stage] = pt.owner.open_line
            # A stop probe runs last in its stage.
            for name in sorted(names, key=lambda x: x.startswith("stop_")):
                t = time.monotonic()
                try:
                    if name.startswith("stop_") and pt.owner is None:
                        raise ProbeError("no owner to stop")
                    values = PROBES[name][1](pt)
                    for k, v in values.items():
                        if isinstance(v, (int, float)) and v is not None:
                            result["values"]["{}.{}".format(name, k)] = v
                except Exception as e:  # noqa: BLE001 -- recorded per probe; the rest go on
                    result["errors"][name] = "{}: {}".format(type(e).__name__, e)
                    if name == "checkpoint":
                        skip_rest = "the checkpoint failed"
                result["seconds"][name] = round(time.monotonic() - t, 2)
            if pt.owner is not None:
                with contextlib.suppress(ProbeError):
                    pt.stop_owner()
    finally:
        if pt.owner is not None:
            pt.owner.kill()
        result["wall_s"] = round(time.monotonic() - started, 1)
        result["load_end"] = open("/proc/loadavg").read().split()[:3]
        if not args.keep:
            shutil.rmtree(pt.work, ignore_errors=True)
    print(json.dumps(result), flush=True)
    return result


# ---------------------------------------------------------------------------
# The sweep (on the box).

def cores_for(slot, per, first):
    lo = first + slot * per
    return "{}-{}".format(lo, lo + per - 1)


def sha256_head(path):
    import hashlib
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def cmd_run(args) -> int:
    image = Path(args.image).resolve()
    tree = Path(args.tree).resolve() if args.tree else image.parent.parent
    ns = [int(x) for x in args.ns.split(",")]
    probes = args.probes.split(",") if args.probes else standard_probes()
    unknown = [p for p in probes if p not in PROBES]
    if unknown:
        raise SystemExit("unknown probe(s) {}; `list` names them".format(unknown))
    missing = [n for n in ns if not (Path(args.fixtures) / "n{}".format(n) / "store").is_dir()]
    if missing:
        raise SystemExit("no curve store for N = {} under {}: build the fixture (tools/fixtures.py "
                         "rebuild --only curve)".format(missing, args.fixtures))
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="fn-curve-", dir=args.work))
    started = time.monotonic()
    meta = {"image": str(image), "tree": str(tree), "fixtures": args.fixtures,
            "probes": probes, "ns": ns, "jobs": args.jobs, "mem": args.mem,
            "cores_per_job": args.cores, "work": str(work),
            "started_utc": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "load_start": open("/proc/loadavg").read().split()[:3]}
    core = Path(str(image) + ".core")
    if core.is_file():
        meta["core_sha256"] = sha256_head(core)
    for name in ("FIXTURE.json", "build.json"):
        with contextlib.suppress(OSError, ValueError):
            meta["fixture_" + name.split(".")[0].lower()] = json.loads(
                (Path(args.fixtures) / name).read_text())
    # A point is split into TASKS, each on its own copy, cores and scope: the
    # replay open; the checkpoint and the served stage (which opens from it);
    # each offline probe (on a copy with no checkpoint, so its open is a full
    # replay, as the fixture's first use is).  Largest N first, the served
    # task first within an N: the longest chain starts at once.
    tasks = []
    for n in ns:
        for label, stage_set, weight in (("served", ("checkpoint", "served"), 0),
                                         ("replay", ("replay",), 2)):
            chosen = [p for p in probes if PROBES[p][0] in stage_set]
            if chosen:
                tasks.append((-n, weight, label, n, ",".join(stage_set), chosen))
        for p in probes:
            if PROBES[p][0] == "offline":
                tasks.append((-n, 1, "offline-" + p, n, "offline", [p]))
    queue = sorted(tasks)
    points, running = {}, {}

    def launch(n, label, stages, chosen, slot):
        argv = [sys.executable, str(HERE), "point", "--n", str(n), "--image", str(image),
                "--tree", str(tree), "--fixtures", args.fixtures, "--work", str(work / label),
                "--stages", stages, "--probes", ",".join(chosen)] + (["--keep"] if args.keep else [])
        argv = ["taskset", "-c", cores_for(slot, args.cores, args.first_core)] + argv
        if shutil.which("systemd-run") and not args.no_scope:
            argv = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=" + args.mem,
                    "-p", "MemorySwapMax=0", "--"] + argv
        log = open(out / "point-n{}-{}.log".format(n, label), "wb")
        return subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=log), log

    free = list(range(args.jobs))
    while queue or running:
        while queue and free:
            _, _, label, n, stages, chosen = queue.pop(0)
            slot = free.pop(0)
            proc, log = launch(n, label, stages, chosen, slot)
            running[(n, label)] = (proc, log, slot)
            print("scale-curve: N={} {} started (cores {})".format(
                n, label, cores_for(slot, args.cores, args.first_core)), flush=True)
        time.sleep(0.2)
        for (n, label), (proc, log, slot) in list(running.items()):
            if proc.poll() is None:
                continue
            out_text = proc.stdout.read().decode("utf-8", "replace").strip().splitlines()
            log.close()
            del running[(n, label)]
            free.append(slot)
            try:
                got = json.loads(out_text[-1])
            except (IndexError, ValueError):
                got = {"values": {}, "errors": {label: "exit {}; see point-n{}-{}.log".format(
                    proc.returncode, n, label)}}
            point = points.setdefault(n, {"n": n, "values": {}, "errors": {}, "tasks": {}})
            point["values"].update(got.get("values", {}))
            point["errors"].update(got.get("errors", {}))
            point["tasks"][label] = {k: got.get(k) for k in ("wall_s", "load_start", "load_end",
                                                             "seconds", "copy_s", "stages")}
            for k, v in got.items():
                if k.startswith("open_line_"):
                    point[k] = v
            point["wall_s"] = max(t.get("wall_s") or 0 for t in point["tasks"].values())
            print("scale-curve: N={} {} done in {} s{}".format(
                n, label, got.get("wall_s"), "; errors: {}".format(got["errors"])
                if got.get("errors") else ""), flush=True)
    shutil.rmtree(work, ignore_errors=True)
    meta["wall_s"] = round(time.monotonic() - started, 1)
    meta["load_end"] = open("/proc/loadavg").read().split()[:3]
    curve = {"meta": meta, "points": {str(n): points[n] for n in sorted(points)}}
    curve["fits"] = fit_all(curve)
    (out / "curve.json").write_text(json.dumps(curve, indent=1) + "\n")
    (out / "curve.md").write_text(markdown(curve))
    print(markdown(curve), flush=True)
    return 0 if all(not p.get("errors") for p in points.values()) else 1


# ---------------------------------------------------------------------------
# The fit.

MODELS = {
    "constant": lambda n: 0.0,
    "log N": lambda n: math.log(n),
    "N": lambda n: float(n),
    "N log N": lambda n: n * math.log(n),
    "N^2": lambda n: float(n) * n,
}
AMBIGUOUS_RATIO, AMBIGUOUS_ABS, AMBIGUOUS_SPREAD = 1.5, 0.05, 1.5

# Known phase transitions, as N (2 KiB articles, ~2.9 KB records) under the curve
# fixture's profile (SYNTH_100K: T 131,072, K 65,536).  A series whose curve bends
# in the segment containing one is flagged `threshold'; every crossing inside the
# measured range is listed with the fit.  (name, N, source, series prefixes it
# can move; () = any.)  Add one here when a lane finds another.
THRESHOLDS = (
    ("open nursery trigger leaves 8 MiB", 720, "books/heap-open-nursery.lisp (PRF-364): "
     "max(8 MiB, min(64 MiB, 4 x history)); history 2 MiB", ("open_", "checkpoint", "digest", "export")),
    ("open nursery trigger reaches 64 MiB", 5800, "books/heap-open-nursery.lisp: history 16 MiB",
     ("open_", "checkpoint", "digest", "export")),
    ("automatic checkpoint due (2 x suffix >= K)", 32768, "books/owner-checkpoint-open.lisp "
     "fn-ock-publication-duep; K = --max-open-suffix 65,536", ("auto_checkpoint", "posts", "pinned_reader")),
    ("transaction budget T (commits refused)", 131072, "books/store-budget.lisp; the fixture's "
     "--max-transactions: a 1M extrapolation assumes a profile that holds 1M", ()),
)
THRESHOLD_SLOPE = 0.4
BEND_HOLDOUT_N, BEND_ERROR = 25000, 0.30
STEEPEN_SLOPE = 0.4


def fit_model(xs, ys, g):
    """Least squares of y = a + b g(x) on relative error (weights 1/y^2), b >= 0.
    Returns (a, b, relative RMS residual)."""
    w = [1.0 / (y * y) if y else 1.0 for y in ys]
    gs = [g(x) for x in xs]
    sw = sum(w)
    if all(v == 0.0 for v in gs):
        a, b = sum(wi * y for wi, y in zip(w, ys)) / sw, 0.0
    else:
        sg = sum(wi * v for wi, v in zip(w, gs)); sy = sum(wi * y for wi, y in zip(w, ys))
        sgg = sum(wi * v * v for wi, v in zip(w, gs)); sgy = sum(wi * v * y for wi, v, y in zip(w, gs, ys))
        det = sw * sgg - sg * sg
        b = (sw * sgy - sg * sy) / det if det else 0.0
        if b < 0:
            b = 0.0
        a = (sy - b * sg) / sw
    resid = math.sqrt(sum(((y - (a + b * v)) / (y if y else 1.0)) ** 2
                          for y, v in zip(ys, gs)) / len(ys))
    return a, b, resid


def segment_excess(xs, ys, k, g, m):
    """How much the measured log-log slope of segment k exceeds the fitted model's
    over the same segment, when the measured rise also exceeds twice the noise."""
    fa, fb = m["a"] + m["b"] * g(xs[k]), m["a"] + m["b"] * g(xs[k + 1])
    if min(ys[k], ys[k + 1], fa, fb) <= 0:
        return None
    span = math.log(xs[k + 1] / xs[k])
    measured, model = math.log(ys[k + 1] / ys[k]) / span, math.log(fb / fa) / span
    if ys[k + 1] / fb - 1 <= 2 * m["residual"]:
        return 0.0
    return measured - model


def power_exponent(xs, ys):
    pts = [(math.log(x), math.log(y)) for x, y in zip(xs, ys) if y > 0]
    if len(pts) < 2:
        return None
    mx = sum(p[0] for p in pts) / len(pts); my = sum(p[1] for p in pts) / len(pts)
    sxx = sum((p[0] - mx) ** 2 for p in pts)
    return sum((p[0] - mx) * (p[1] - my) for p in pts) / sxx if sxx else None


def fit_series(xs, ys, expected_ns, series=""):
    out = {"points": len(xs), "models": {}, "flags": []}
    if len(xs) < 3:
        out["flags"].append("failed: {} of {} points".format(len(xs), len(expected_ns)))
        return out
    lo_n, hi_n = min(xs), max(xs)
    for name, g in MODELS.items():
        a, b, r = fit_model(xs, ys, g)
        top = a + b * g(hi_n)
        rise = b * (g(hi_n) - g(lo_n)) / top if top > 0 else 0.0
        out["models"][name] = {"a": a, "b": b, "residual": r, "rise": rise,
                               # An N-dependence smaller than twice the noise is no evidence of one.
                               "significant": name == "constant" or (b > 0 and rise >= 2 * r),
                               "at_1M": a + b * g(1e6), "at_10M": a + b * g(1e7)}
    live = {m: v for m, v in out["models"].items() if v["significant"]}
    least = min(v["residual"] for v in live.values())
    # Parsimony: the simplest model within 10% (+0.005) of the least residual.
    best = next(m for m in MODELS if m in live and live[m]["residual"] <= 1.1 * least + 0.005)
    out["best"] = best
    bm = out["models"][best]
    out["residual"], out["at_1M"], out["at_10M"] = bm["residual"], bm["at_1M"], bm["at_10M"]
    out["power_k"] = power_exponent(xs, ys)
    missing = [n for n in expected_ns if n not in xs]
    if missing:
        out["flags"].append("failed: no point at N = {}".format(missing))
    rivals = []
    for name, m in live.items():
        if name == best:
            continue
        close = m["residual"] <= max(AMBIGUOUS_RATIO * bm["residual"], bm["residual"] + AMBIGUOUS_ABS)
        lo, hi = sorted([max(m["at_1M"], 1e-12), max(bm["at_1M"], 1e-12)])
        if close and hi / lo > AMBIGUOUS_SPREAD:
            rivals.append("{} (resid {:.3f}, 1M {})".format(name, m["residual"], fmt(m["at_1M"])))
    if rivals:
        out["flags"].append("ambiguous: " + "; ".join(rivals))
    low = [(x, y) for x, y in zip(xs, ys) if x <= BEND_HOLDOUT_N]
    if len(low) >= 3 and hi_n > BEND_HOLDOUT_N:
        a, b, r = fit_model([p[0] for p in low], [p[1] for p in low], MODELS[best])
        pred = a + b * MODELS[best](hi_n)
        meas = ys[xs.index(hi_n)]
        err = (meas - pred) / pred if pred > 0 else 0.0
        out["holdout"] = {"fit_on_n_le": BEND_HOLDOUT_N, "predicted": pred, "measured": meas,
                          "n": hi_n, "error": err}
        # Only a curve that gets WORSE than its small-N fit predicts is a threshold
        # suspicion; one that flattens makes the extrapolation pessimistic.
        if err > max(BEND_ERROR, 2 * r, 2 * bm["residual"]):
            out["flags"].append("bend: fitted on N <= {:,} it predicts {} at {:,}, measured {} ({:+.0%})".format(
                BEND_HOLDOUT_N, fmt(pred), hi_n, fmt(meas), err))
    crossed = [t for t in THRESHOLDS if lo_n < t[1] <= hi_n and
               (not t[3] or any(series.startswith(pre) for pre in t[3]))]
    if crossed:
        out["crosses"] = ["{} at ~{:,}".format(t[0], t[1]) for t in crossed]
        for name, n, _, _ in crossed:
            k = next(i for i in range(len(xs) - 1) if xs[i] < n <= xs[i + 1])
            excess = segment_excess(xs, ys, k, MODELS[best], bm)
            if excess is not None and excess > THRESHOLD_SLOPE:
                out["flags"].append("threshold: {} (~{:,}) inside {:,}-{:,}: the curve's slope there "
                                    "exceeds its fitted model's by {:.2f}".format(
                                        name, n, xs[k], xs[k + 1], excess))
    excess = segment_excess(xs, ys, len(xs) - 2, MODELS[best], bm)
    if excess is not None:
        out["last_segment_excess"] = excess
        if excess > STEEPEN_SLOPE:
            out["flags"].append("steepens: the last segment's log-log slope exceeds the fitted "
                                "model's there by {:.2f}".format(excess))
    return out


def fit_all(curve):
    ns = [int(n) for n in curve["meta"]["ns"]]
    series = sorted({k for p in curve["points"].values() for k in p.get("values", {})})
    fits = {}
    for s in series:
        pts = sorted((int(n), p["values"][s]) for n, p in curve["points"].items()
                     if p.get("values", {}).get(s) is not None)
        fits[s] = fit_series([x for x, _ in pts], [float(y) for _, y in pts], ns, s)
    return fits


def fmt(v):
    if v is None:
        return "-"
    a = abs(v)
    if a >= 1e6:
        return "{:.3g}".format(v)
    if a >= 100:
        return "{:,.0f}".format(v)
    if a >= 1:
        return "{:.2f}".format(v)
    return "{:.3g}".format(v)


def markdown(curve):
    meta, fits = curve["meta"], curve["fits"]
    ns = [int(n) for n in meta["ns"]]
    head = ["# Scale curve: {}".format(meta.get("image")), "",
            "N = {}; probes {}; {} jobs x {} cores, MemoryMax {} each; load {} at the start, {} at the "
            "end; wall {} s; core sha256 {}; fixtures {}.".format(
                ", ".join("{:,}".format(n) for n in ns), ", ".join(meta["probes"]), meta["jobs"],
                meta["cores_per_job"], meta["mem"], " ".join(meta["load_start"]),
                " ".join(meta.get("load_end", [])), meta.get("wall_s"),
                (meta.get("core_sha256") or "?")[:16], meta["fixtures"]), "",
            "Each series fitted y = a + b g(N) on relative error; `fit` is the least residual "
            "(relative RMS); k is a power law's exponent; 1M and 10M are the fitted model's "
            "extrapolation. A flag is the only case for a real large run.", ""]
    cols = ["series"] + ["{:g}k".format(n / 1000) for n in ns] + ["fit", "resid", "k", "1M", "10M", "flags"]
    rows = ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
    for s, f in fits.items():
        vals = []
        for n in ns:
            v = curve["points"].get(str(n), {}).get("values", {}).get(s)
            vals.append(fmt(v))
        rows.append("| " + " | ".join([s] + vals + [
            f.get("best", "-"), "{:.3f}".format(f["residual"]) if "residual" in f else "-",
            "{:.2f}".format(f["power_k"]) if f.get("power_k") is not None else "-",
            fmt(f.get("at_1M")), fmt(f.get("at_10M")),
            "; ".join(f["flags"]) or "-"]) + " |")
    crossings = sorted({c for f in fits.values() for c in f.get("crosses", [])})
    rows += ["", "Known thresholds inside the measured range (tools/scale_curve.py THRESHOLDS): "
             + ("; ".join(crossings) if crossings else "none") + "."]
    errors = ["- N={}: {}".format(n, p["errors"]) for n, p in curve["points"].items() if p.get("errors")]
    tail = ["", "Per point: its longest task's wall seconds {}.".format(", ".join(
        "{:,}: {}".format(int(n), p.get("wall_s")) for n, p in curve["points"].items()))]
    if errors:
        tail += ["", "Errors:"] + errors
    return "\n".join(head + rows + tail) + "\n"


def cmd_fit(args) -> int:
    curve = json.loads(Path(args.curve).read_text())
    curve["fits"] = fit_all(curve)
    if args.md:
        print(markdown(curve))
    else:
        for s, f in curve["fits"].items():
            print("{:32} {:9} resid {:.3f} k {:5} 1M {:>10} 10M {:>10} {}".format(
                s, f.get("best", "-"), f.get("residual", float("nan")),
                "{:.2f}".format(f["power_k"]) if f.get("power_k") is not None else "-",
                fmt(f.get("at_1M")), fmt(f.get("at_10M")), "; ".join(f["flags"])))
    known = {}
    if args.known:
        print("\n| series | at N | measured | curve's model | extrapolated | ratio |\n|---|---|---|---|---|---|")
        for item in args.known:
            m = re.fullmatch(r"([^=]+)=([0-9.eE+-]+)@([0-9.eE+]+)", item)
            if not m:
                raise SystemExit("--known SERIES=VALUE@N, got " + item)
            s, value, n = m.group(1), float(m.group(2)), float(m.group(3))
            f = curve["fits"].get(s)
            if not f or "best" not in f:
                print("| {} | {:,.0f} | {} | - | no fit | - |".format(s, n, fmt(value)))
                continue
            bm = f["models"][f["best"]]
            pred = bm["a"] + bm["b"] * MODELS[f["best"]](n)
            print("| {} | {:,.0f} | {} | {} | {} | {:.2f} |".format(
                s, n, fmt(value), f["best"], fmt(pred), pred / value if value else float("nan")))
            known.setdefault(s, []).append((n, value, pred))
        # The SHAPE, free of the box's load: two measured points of one series
        # (one run, one load) against the model's ratio between the same N.
        shapes = [(s, sorted(v)) for s, v in known.items() if len({n for n, _, _ in v}) > 1]
        if shapes:
            print("\n| series | measured ratio | model ratio | model/measured |\n|---|---|---|---|")
            for s, v in shapes:
                (n0, m0, p0), (n1, m1, p1) = v[0], v[-1]
                print("| {} {:,.0f}/{:,.0f} | {:.2f} | {:.2f} | {:.2f} |".format(
                    s, n1, n0, m1 / m0, p1 / p0, (p1 / p0) / (m1 / m0)))
    return 0


# ---------------------------------------------------------------------------
# The laptop's one command.

def cmd_box(args) -> int:
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    remote = "{}/{}-{}".format(BOX_RUNS, args.name, stamp)
    boxes = HERE.parent / "boxes.sh"
    reserved = False
    if args.reserve:
        r = subprocess.run(["sh", str(boxes), "reserve", BOX, "--for", str(args.reserve),
                            "--why", "scale curve ({})".format(args.name)])
        if r.returncode == 4:
            print("scale-curve: hbox is reserved; waiting for the lease", flush=True)
            if subprocess.run(["sh", str(boxes), "wait", BOX]).returncode != 0:
                return 4
            r = subprocess.run(["sh", str(boxes), "reserve", BOX, "--for", str(args.reserve),
                                "--why", "scale curve ({})".format(args.name)])
        reserved = r.returncode == 0
    try:
        subprocess.run(["ssh", BOX, "mkdir -p " + shlex.quote(remote)], check=True)
        subprocess.run(["scp", "-q", str(HERE), "{}:{}/scale_curve.py".format(BOX, remote)], check=True)
        words = ["run", "--image", args.image, "--out", remote, "--ns", args.ns,
                 "--jobs", str(args.jobs), "--cores", str(args.cores), "--mem", args.mem,
                 "--fixtures", args.fixtures]
        if args.probes:
            words += ["--probes", args.probes]
        if args.tree:
            words += ["--tree", args.tree]
        cmd = "cd {r} && nohup sh -c {c} > {r}/run.log 2>&1 < /dev/null &".format(
            r=shlex.quote(remote), c=shlex.quote("python3 scale_curve.py {}; echo $? > status".format(
                " ".join(shlex.quote(w) for w in words))))
        subprocess.run(["ssh", BOX, cmd], check=True)
        print("scale-curve: running on {}:{} (run.log)".format(BOX, remote), flush=True)
        deadline = time.monotonic() + args.timeout
        status = ""
        while time.monotonic() < deadline:
            done = subprocess.run(["ssh", BOX, "cat {}/status 2>/dev/null".format(shlex.quote(remote))],
                                  stdout=subprocess.PIPE, text=True)
            status = done.stdout.strip()
            if status:
                break
            time.sleep(10)
        if not status:
            print("scale-curve: no status after {} s; the run stays on {}:{}".format(
                args.timeout, BOX, remote), file=sys.stderr)
            return 3
        out = Path(args.out or "build/scale-curve/{}-{}".format(args.name, stamp))
        out.mkdir(parents=True, exist_ok=True)
        subprocess.run(["rsync", "-a", "{}:{}/".format(BOX, remote), str(out) + "/"], check=False)
        print((out / "curve.md").read_text() if (out / "curve.md").exists()
              else (out / "run.log").read_text()[-3000:])
        print("scale-curve: exit {}; results in {}".format(status, out))
        return int(status)
    finally:
        if reserved:
            subprocess.run(["sh", str(boxes), "release", BOX])


def cmd_list(_args) -> int:
    for name, (stage, fn) in PROBES.items():
        print("{:16} {:10} {:8} {}".format(name, stage, "variant" if name in VARIANTS else "standard",
                                          " ".join((fn.__doc__ or "").split())))
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    def run_options(q):
        q.add_argument("--image", required=True, help="a tools/hbox_native.sh tree's build/fn-host (on hbox)")
        q.add_argument("--tree", default=None, help="the image's tree (default: the image's ../..)")
        q.add_argument("--probes", default=None,
                       help="comma-separated (default: the standard set; `list` marks the variants)")
        q.add_argument("--ns", default=",".join(str(n) for n in NS))
        q.add_argument("--jobs", type=int, default=4, help="points at once, each on its own cores")
        q.add_argument("--cores", type=int, default=4, help="cores per point (taskset)")
        q.add_argument("--mem", default="24G", help="MemoryMax per point")
        q.add_argument("--fixtures", default=FIXTURES)
    r = sub.add_parser("run")
    run_options(r)
    r.add_argument("--out", required=True)
    r.add_argument("--work", default="/dev/shm")
    r.add_argument("--first-core", type=int, default=0)
    r.add_argument("--keep", action="store_true", help="keep each point's copy")
    r.add_argument("--no-scope", action="store_true")
    pt = sub.add_parser("point")
    for a in ("--image", "--tree", "--fixtures", "--work", "--probes", "--stages"):
        pt.add_argument(a, required=True)
    pt.add_argument("--n", type=int, required=True)
    pt.add_argument("--keep", action="store_true")
    b = sub.add_parser("box")
    run_options(b)
    b.add_argument("--name", default=Path.cwd().name)
    b.add_argument("--out", default=None)
    b.add_argument("--reserve", type=int, default=15, help="minutes to reserve hbox (0: none)")
    b.add_argument("--timeout", type=int, default=1800)
    f = sub.add_parser("fit")
    f.add_argument("curve")
    f.add_argument("--md", action="store_true")
    f.add_argument("--known", nargs="*", default=[], help="SERIES=VALUE@N: a measured point to compare")
    sub.add_parser("list")
    args = p.parse_args(argv)
    if args.cmd == "point":
        signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
        run_point(args)
        return 0
    return {"run": cmd_run, "fit": cmd_fit, "box": cmd_box, "list": cmd_list}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
