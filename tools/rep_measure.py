#!/usr/bin/env python3
"""Matched representation measurement of a native fn image (D27; rep-wave-d).

One scratch store initialised through the operator verb under a named
profile (`operator CONFIG init --profile PROFILE GROUP`; the `default`
profile admits N = 10,000 articles of 32 KiB, which `development` refuses),
one `operator run` of the image on a kernel port.  Measured, in order:

  greeting     connect and read the 200 line, K times, each on a fresh socket
  post         N articles of about L octets over one NNTP connection, every
               POST timed; VmRSS at each quarter of the load
  heap         after the load: VmRSS, VmHWM (peak residency) and, on an image
               with the heap hook (the lane's profiling entry with
               FN_PROF_LOAD=heap.lisp and FN_HEAP_DIR set), the dynamic-space
               usage before and after a full collection (the live heap), the
               collection's seconds, the allocation counter and SBCL's
               bytes-consed-between-gcs (the garbage headroom)
  alloc        bytes consed per operation: K POSTs, K STATs, K ARTICLEs,
               each batch bracketed by the hook's allocation counter
  reads        STAT, ARTICLE (the whole multi-line reply), OVER, for K
               identifiers spread over the store, on a fresh connection
  contention   the same K POSTs and K ARTICLEs timed while R reader
               connections loop ARTICLE over the store; the readers' own
               throughput is counted
  reopen       stop, start again on the same store: seconds to the LISTENING
               line (the open at N), then RSS and the live heap
  checkpoint   stop, `store checkpoint` (offline, timed), start again: the
               open from the checkpoint, then RSS and the live heap

Every timing is a command written and its reply read on an open socket, so
it includes the loopback round trip and the owner's whole read.  The JSON
holds every number with the image digests, the profile and the init
transcript; nothing is derived from RSS.

    FN_PROF_LOAD=heap.lisp FN_HEAP_DIR=/dir python3 tools/rep_measure.py \\
        --image build/fn-host-developer-prof --heap-dir /dir \\
        --work /tank/fn/scratch/LANE/work/n1000-32k --articles 1000 \\
        --octets 32768 --samples 32 --readers 3 --json out.json
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))
import msgid_measure as m  # noqa: E402
from tests.native_process import wait_for_announcement  # noqa: E402

HEAD = ("From: rep@example.invalid\r\nNewsgroups: fn.test\r\nSubject: rep %d\r\n"
        "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\nMessage-ID: %s\r\n\r\n")
LINE = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdef"[:78] + b"\r\n"


def article(i, octets):
    """An article of about OCTETS octets (the wave-C generator): the fixed
    header, then 78-character body lines; 0 is the 155-octet article."""
    if octets == 0:
        return m.article(i)
    head = (HEAD % (i, m.msgid(i))).encode("ascii")
    need = max(0, octets - len(head))
    body = LINE * (need // len(LINE))
    rest = need - len(body)
    if rest >= 2:
        body += LINE[:rest - 2] + b"\r\n"
    return head + body


def read_multiline(conn):
    total = 0
    while True:
        line = conn.readline()
        if not line:
            raise SystemExit("connection closed in a multi-line reply")
        total += len(line)
        if line == b".\r\n":
            return total


def timed_multiline(conn, text):
    started = time.perf_counter()
    reply = conn.line(text)
    octets = read_multiline(conn) if reply[:1] == b"2" else 0
    return time.perf_counter() - started, reply, octets


def post(conn, i, octets):
    t0 = time.perf_counter()
    r = conn.line("POST")
    if not r.startswith(b"340"):
        raise SystemExit("POST %d: %r" % (i, r))
    conn.stream.write(article(i, octets) + b".\r\n")
    r = conn.readline()
    if not r.startswith(b"240"):
        raise SystemExit("POST %d body: %r" % (i, r))
    return time.perf_counter() - t0


def status_kib(pid, key):
    try:
        for row in Path("/proc/%d/status" % pid).read_text().splitlines():
            if row.startswith(key + ":"):
                return int(row.split()[1])
    except OSError:
        return None
    return None


class Heap:
    """The heap hook's trigger protocol (heap.lisp): write DIR/go with a tag,
    read DIR/heap-<tag>.txt when DIR/done-<tag> appears."""

    def __init__(self, directory, proc):
        self.dir = Path(directory) if directory else None
        self.proc = proc
        self.n = 0

    def snap(self, label, gc=False):
        if self.dir is None:
            return None
        self.n += 1
        tag = ("gc-" if gc else "a-") + "%03d-%s" % (self.n, label)
        (self.dir / "go.tmp").write_text(tag + "\n")
        os.rename(self.dir / "go.tmp", self.dir / "go")
        started = time.perf_counter()
        while not (self.dir / ("done-" + tag)).exists():
            time.sleep(0.02)
            if self.proc.poll() is not None:
                raise SystemExit("owner died during a heap snapshot")
            if time.perf_counter() - started > 600:
                raise SystemExit("heap hook did not answer within 600 s")
        out = {"tag": tag}
        for line in (self.dir / ("heap-" + tag + ".txt")).read_text().splitlines():
            k, v = line.split()
            out[k.replace("-", "_")] = float(v) if "." in v else int(v)
        return out


def start_owner(image, config, env, stderr_path, timeout=3600):
    stderr = open(stderr_path, "ab")
    started = time.perf_counter()
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"],
                            env=env, stdout=subprocess.PIPE, stderr=stderr)
    wait_for_announcement(proc, b"LISTENING ", timeout=timeout)
    return proc, time.perf_counter() - started, stderr


def stop_owner(proc, stderr):
    proc.terminate()
    try:
        proc.wait(timeout=600)
    except subprocess.TimeoutExpired:
        proc.kill()
    stderr.close()


def residency(proc, heap, label):
    out = {"rss_kib": status_kib(proc.pid, "VmRSS"), "hwm_kib": status_kib(proc.pid, "VmHWM")}
    snap = heap.snap(label, gc=True)
    if snap:
        out["heap"] = snap
        out["rss_after_gc_kib"] = status_kib(proc.pid, "VmRSS")
    return out


def alloc_batch(heap, label, fn, k):
    """Run FN k times between two allocation readings; bytes per call, and the timings."""
    before = heap.snap(label + "0")
    times = [fn(i) for i in range(k)]
    after = heap.snap(label + "1")
    out = {"n": k, "timing": m.summary(times)}
    if before and after:
        out["bytes_consed_per_op"] = (after["bytes_consed"] - before["bytes_consed"]) / float(k)
    return out


def reader_loop(port, msgids, stop, counter, errors):
    try:
        c = m.Conn(port)
        i = 0
        while not stop.is_set():
            dt, r, octets = timed_multiline(c, "ARTICLE %s" % msgids[i % len(msgids)])
            if not r.startswith(b"220"):
                errors.append(r)
                break
            counter[0] += 1
            counter[1] += octets
            i += 1
        c.close()
    except Exception as e:  # noqa: BLE001 - reported, never hidden
        errors.append(repr(e))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--image", required=True)
    p.add_argument("--work", required=True)
    p.add_argument("--articles", type=int, required=True)
    p.add_argument("--octets", type=int, default=0, help="target article size; 0 = the 155-octet article")
    p.add_argument("--samples", type=int, default=32, help="K: identifiers read, operations per alloc batch")
    p.add_argument("--readers", type=int, default=3, help="R: concurrent ARTICLE readers for the contention window")
    p.add_argument("--profile", default="default")
    p.add_argument("--heap-dir", default=None, help="FN_HEAP_DIR of an image running the heap hook")
    p.add_argument("--json", required=True)
    p.add_argument("--skip-reopen", action="store_true")
    p.add_argument("--skip-checkpoint", action="store_true")
    p.add_argument("--reopen-timeout", type=int, default=3600)
    a = p.parse_args()
    image = Path(a.image).resolve()
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    if a.heap_dir:
        Path(a.heap_dir).mkdir(parents=True, exist_ok=True)
        env["FN_HEAP_DIR"] = a.heap_dir
    port = m.free_port()
    store, control, config = work / "store", work / "control.sock", work / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, control), encoding="ascii")
    init = [str(image), "--fn", "operator", str(config), "init", "--profile", a.profile, "fn.test"]
    r = subprocess.run(init, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (work / "init.out").write_bytes(r.stdout)
    if r.returncode != 0:
        raise SystemExit("init failed rc=%d: %r" % (r.returncode, r.stdout[-400:]))
    out = {"image": str(image), "launcher_sha256": m.digest(image),
           "core_sha256": m.digest(str(image) + ".core"), "profile": a.profile,
           "articles": a.articles, "octets": a.octets, "article0_octets": len(article(0, a.octets)),
           "samples": a.samples, "readers": a.readers, "port": port, "store": str(store),
           "init_out": r.stdout.decode("ascii", "replace"), "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    proc, out["first_open_seconds"], stderr = start_owner(image, config, env, work / "owner.stderr")
    heap = Heap(a.heap_dir, proc)
    k = a.samples
    try:
        out["residency_empty"] = residency(proc, heap, "empty")
        greet = []
        for _ in range(k):
            t0 = time.perf_counter()
            c = m.Conn(port)
            greet.append(time.perf_counter() - t0)
            c.close()
        out["greeting"] = m.summary(greet)
        c = m.Conn(port)
        load, quarters = [], {}
        started_all = time.perf_counter()
        n = a.articles
        for i in range(n):
            load.append(post(c, i, a.octets))
            if n >= 4 and (i + 1) % (n // 4) == 0:
                quarters["rss_kib_at_%d" % (i + 1)] = status_kib(proc.pid, "VmRSS")
        c.close()
        out["load_seconds"] = time.perf_counter() - started_all
        q = max(1, n // 4)
        out["post_all"] = m.summary(load)
        out["post_first_quarter"] = m.summary(load[:q])
        out["post_last_quarter"] = m.summary(load[-q:])
        out["rss_quarters_kib"] = quarters
        out["residency_after_load"] = residency(proc, heap, "load")
        next_i = [n]

        def one_post(_):
            i = next_i[0]
            next_i[0] += 1
            return post(cw, i, a.octets)

        step = max(1, n // k)
        present = [m.msgid(i) for i in range(0, n, step)][:k]
        numbers = [i + 1 for i in range(0, n, step)][:k]
        cw = m.Conn(port)
        cr = m.Conn(port)
        cr.line("STAT %s" % present[0])
        out["alloc_post"] = alloc_batch(heap, "post", one_post, k)
        out["alloc_stat"] = alloc_batch(heap, "stat", lambda i: cr.timed("STAT %s" % present[i % len(present)])[0], k)
        out["alloc_article"] = alloc_batch(heap, "article", lambda i: timed_multiline(cr, "ARTICLE %s" % present[i % len(present)])[0], k)
        cw.close()
        cr.close()
        c = m.Conn(port)
        c.line("STAT %s" % present[0])
        stat, art, art_octets = [], [], 0
        for msgid in present:
            dt, r = c.timed("STAT %s" % msgid)
            assert r.startswith(b"223"), r
            stat.append(dt)
        for msgid in present:
            dt, r, octets = timed_multiline(c, "ARTICLE %s" % msgid)
            assert r.startswith(b"220"), r
            art.append(dt)
            art_octets += octets
        r = c.line("GROUP fn.test")
        out["group_reply"] = r.decode("ascii", "replace").strip()
        over = []
        for num in numbers:
            dt, r, octets = timed_multiline(c, "OVER %d" % num)
            assert r.startswith(b"224"), r
            over.append(dt)
        c.close()
        out["stat_present"] = m.summary(stat)
        out["article_present"] = m.summary(art)
        out["article_octets_read"] = art_octets
        out["over_present"] = m.summary(over)
        # Contention: R readers loop ARTICLE while K POSTs and K ARTICLEs are timed.
        if a.readers > 0:
            stop, counter, errors, threads = threading.Event(), [0, 0], [], []
            for _ in range(a.readers):
                t = threading.Thread(target=reader_loop, args=(port, present, stop, counter, errors), daemon=True)
                t.start()
                threads.append(t)
            time.sleep(1.0)
            cw = m.Conn(port)
            cr = m.Conn(port)
            cr.line("STAT %s" % present[0])
            window = time.perf_counter()
            cpost = [one_post(i) for i in range(k)]
            cart = [timed_multiline(cr, "ARTICLE %s" % present[i % len(present)])[0] for i in range(k)]
            window = time.perf_counter() - window
            stop.set()
            for t in threads:
                t.join(timeout=120)
            cw.close()
            cr.close()
            out["contention"] = {"readers": a.readers, "window_seconds": window,
                                 "reader_articles": counter[0], "reader_octets": counter[1],
                                 "post": m.summary(cpost), "article": m.summary(cart),
                                 "reader_errors": [str(e) for e in errors]}
        out["articles_total"] = next_i[0]
        out["residency_after_reads"] = residency(proc, heap, "reads")
    finally:
        stop_owner(proc, stderr)
    Path(a.json + ".partial").write_text(json.dumps(out, indent=2) + "\n")
    if not a.skip_reopen:
        proc, out["reopen_seconds"], stderr = start_owner(image, config, env, work / "owner-reopen.stderr",
                                                          timeout=a.reopen_timeout)
        heap = Heap(a.heap_dir, proc)
        try:
            c = m.Conn(port)
            dt, r = c.timed("STAT %s" % m.msgid(a.articles - 1))
            out["reopen_last_stat"] = r.decode("ascii", "replace").strip()
            c.close()
            out["residency_after_reopen"] = residency(proc, heap, "reopen")
        finally:
            stop_owner(proc, stderr)
    if not a.skip_checkpoint:
        t0 = time.perf_counter()
        r = subprocess.run([str(image), "--fn", "operator", str(config), "store", "checkpoint"],
                           env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out["checkpoint_seconds"] = time.perf_counter() - t0
        out["checkpoint_rc"] = r.returncode
        out["checkpoint_out"] = r.stdout.decode("ascii", "replace")[-600:]
        if r.returncode == 0:
            proc, out["reopen_from_checkpoint_seconds"], stderr = start_owner(
                image, config, env, work / "owner-checkpoint.stderr", timeout=a.reopen_timeout)
            heap = Heap(a.heap_dir, proc)
            try:
                c = m.Conn(port)
                dt, r = c.timed("STAT %s" % m.msgid(a.articles - 1))
                out["checkpoint_last_stat"] = r.decode("ascii", "replace").strip()
                c.close()
                out["residency_after_checkpoint_open"] = residency(proc, heap, "ckpt")
            finally:
                stop_owner(proc, stderr)
    out["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    Path(a.json).write_text(json.dumps(out, indent=2) + "\n")
    for key in ("greeting", "post_first_quarter", "post_last_quarter", "stat_present", "article_present", "over_present"):
        v = out.get(key)
        if v:
            print("%-20s median %.3f ms  p95 %.3f ms  max %.3f ms" % (key, v["median_ms"], v["p95_ms"], v["max_ms"]))
    for key in ("residency_after_load", "residency_after_reopen", "residency_after_checkpoint_open"):
        v = out.get(key)
        if v:
            live = v.get("heap", {}).get("dynamic_usage_after_gc")
            print("%-32s rss %s KiB  hwm %s KiB  live %s" % (key, v["rss_kib"], v["hwm_kib"], live))
    for key in ("first_open_seconds", "load_seconds", "reopen_seconds", "checkpoint_seconds", "reopen_from_checkpoint_seconds"):
        if key in out:
            print("%-32s %.3f s" % (key, out[key]))


if __name__ == "__main__":
    main()
