#!/usr/bin/env python3
"""qual-b6759850, section 15 "Long-lived mixed workload": one measured hour on
the developer image.  One owner (profile default with K=4096, so it publishes
state checkpoints on its own at K/2), and together:

  readers    3 threads looping GROUP / OVER / ARTICLE / XPAT, every reply timed
  posts      1 unsigned POST every 0.5 s (NNTP), timed
  signed     agent A (tools/fn_consumer.py `report`): a hybrid-signed report
             through hybrid-sign + hybrid-author every 20 s
  consumer   agent B (tools/fn_consumer.py `wake`): polls, applies, replies
             signed, acknowledges, every 30 s
  control    every 120 s a live `group create` and `control grant`; `status`
             and `health` live every 30 s (timed)
  BP debt    the DTN developer image's bp-service queues one job every 60 s
             to a refused peer (a journal that only grows: debt, never sent)
             and resumes it every 300 s -- a separate process and journal

Sampled every 10 s: owner CPU (utime+stime from /proc), VmRSS, VmHWM, store
octets and inodes, BP journal octets.  GC is not observable on the shipped
images (the heap hook is a profiling entry only): RSS/HWM are reported as
residency, never as GC.  Every decision is the image's; this is a client.
"""
import json, os, random, shutil, signal, socket, subprocess, sys, threading, time
from pathlib import Path

S = Path("/tank/fn/scratch/qual-b6759850")
T = S / "tree"
sys.path.insert(0, str(T / "tools")); sys.path.insert(0, str(T))
import msgid_measure as m
from tests.native_process import wait_for_announcement

I = Path("/tank/fn/gates/qual-b6759850-20260926/build/images/b675985074cf14b009204f6eb3e5409f4a025a80")
IMG = I / "fn-host-developer"
DTN = I / "fn-host-dtn-developer"
OPENSSL = str(S / "bin" / "test-openssl")
W = Path(sys.argv[1])
HOUR = float(sys.argv[2]) if len(sys.argv) > 2 else 3600.0
ENV = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
for k in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_CONSUMER_CUT", "FN_NATIVE_CONTROL_FAULT", "FN_NATIVE_CONTROL_TEST_STOP"):
    ENV.pop(k, None)
LAT = {}
LOCK = threading.Lock()
EVENTS = []
STOP = threading.Event()


def lat(kind, seconds, ok=True):
    with LOCK:
        LAT.setdefault(kind, []).append(seconds)
        if not ok:
            LAT.setdefault(kind + ":not-ok", []).append(seconds)


def ev(**r):
    r["t"] = round(time.time() - T0, 2)
    with LOCK:
        EVENTS.append(r)


def native(*words, image=IMG, timeout=600):
    t = time.perf_counter()
    r = subprocess.run([str(image), "--fn", *map(str, words)], cwd=T, env=ENV, capture_output=True, timeout=timeout)
    return r.returncode, (r.stdout + r.stderr).decode("utf-8", "replace"), time.perf_counter() - t


def summary(xs):
    if not xs:
        return None
    s = sorted(xs)
    q = lambda p: s[min(len(s) - 1, int(p * len(s)))]
    return {"n": len(s), "p50_ms": q(.5) * 1e3, "p95_ms": q(.95) * 1e3, "p99_ms": q(.99) * 1e3, "max_ms": s[-1] * 1e3}


def signer(label, byte, gen):
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ed25519
    key = ed25519.Ed25519PrivateKey.generate()
    seed = key.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw, serialization.NoEncryption())
    pub = key.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    base = W / label
    base.mkdir()
    keys = {n: str(base / n) for n in ("principal", "ed_public", "ed_secret", "ml_private", "ml_public")}
    Path(keys["principal"]).write_bytes(bytes([byte]) * 32)
    Path(keys["ed_public"]).write_bytes(pub)
    Path(keys["ed_secret"]).write_bytes(seed + pub)
    subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", keys["ml_private"]], check=True, capture_output=True)
    subprocess.run([OPENSSL, "pkey", "-in", keys["ml_private"], "-pubout", "-out", keys["ml_public"]], check=True, capture_output=True)
    rc, out, _ = native("hybrid-enroll", CONTROL, gen, keys["principal"], keys["ed_public"], keys["ml_public"])
    ev(kind="enroll", label=label, rc=rc, out=out.strip()[-200:])
    cfg = base / "consumer.json"
    cfg.write_text(json.dumps({"image": str(IMG), "control": str(CONTROL), "consumer": label, "group": "fn.test",
                               "application_id": "qual-mixed", "from": "%s@example.invalid" % label,
                               "db": str(base / "state.db"), "work": str(base / "work"), "keys": keys,
                               "principal_hex": (bytes([byte]) * 32).hex(), "generation": str(gen)}))
    return cfg


def consumer(cfg, *words):
    t = time.perf_counter()
    r = subprocess.run([sys.executable, str(T / "tools" / "fn_consumer.py"), str(cfg), *words], cwd=T, env=ENV,
                       capture_output=True, timeout=900)
    return r.returncode, (r.stdout + r.stderr).decode("utf-8", "replace"), time.perf_counter() - t


def readers(port, idx):
    rnd = random.Random(idx)
    c = None
    while not STOP.is_set():
        try:
            if c is None:
                c = m.Conn(port)
            t = time.perf_counter(); r = c.line("GROUP fn.test"); lat("reader-group", time.perf_counter() - t, r.startswith(b"211"))
            parts = r.split()
            hi = int(parts[3]) if r.startswith(b"211") and len(parts) > 3 else 0
            if hi <= 0:
                time.sleep(0.5); continue
            n = rnd.randint(1, hi)
            for kind, cmd in (("reader-over", "OVER %d-%d" % (max(1, n - 20), n)), ("reader-article", "ARTICLE %d" % n),
                              ("reader-xpat", "XPAT Subject %d-%d *mixed*" % (max(1, n - 50), n))):
                t = time.perf_counter(); rep = c.line(cmd)
                if rep[:1] == b"2":
                    while c.readline() != b".\r\n":
                        pass
                lat(kind, time.perf_counter() - t, rep[:1] == b"2" or rep.startswith(b"423"))
        except Exception as e:
            ev(kind="reader-error", idx=idx, error=repr(e)[:200])
            c = None
            time.sleep(1)


def poster(port):
    i = 0
    c = None
    while not STOP.is_set():
        try:
            if c is None:
                c = m.Conn(port)
            art = ("From: mixed@example.invalid\r\nNewsgroups: fn.test\r\nSubject: mixed %d\r\n"
                   "Date: Sat, 26 Sep 2026 07:00:00 +0000\r\nMessage-ID: <mixed-%d@qual.invalid>\r\n\r\n" % (i, i)).encode() + b"x" * 700 + b"\r\n"
            t = time.perf_counter()
            r = c.line("POST")
            c.stream.write(art + b".\r\n"); rep = c.readline()
            lat("post", time.perf_counter() - t, rep.startswith(b"240"))
            if not rep.startswith(b"240"):
                ev(kind="post-not-240", i=i, reply=rep.decode(errors="replace").strip())
            i += 1
        except Exception as e:
            ev(kind="post-error", i=i, error=repr(e)[:200]); c = None
        STOP.wait(0.5)


def every(period, fn):
    while not STOP.wait(period):
        try:
            fn()
        except Exception as e:
            ev(kind="task-error", fn=fn.__name__, error=repr(e)[:300])


def main():
    global CONTROL, T0
    if W.exists():
        shutil.rmtree(W)
    W.mkdir(parents=True)
    port = m.free_port()
    store, CONTROL, cfg = W / "store", W / "control.sock", W / "fn.toml"
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n[log]\npath = "%s"\n'
                   % (store, port, CONTROL, W / "service.log"))
    rc, out, _ = native("operator", cfg, "init", "--max-open-suffix", "4096", "fn.test")
    print("init rc", rc, out.strip()[-400:], flush=True)
    owner_err = open(W / "owner.stderr", "ab")
    T0 = time.time()
    owner = subprocess.Popen([str(IMG), "--fn", "operator", str(cfg), "run"], cwd=T, env=ENV, stdout=subprocess.PIPE, stderr=owner_err)
    wait_for_announcement(owner, b"LISTENING ", timeout=300)
    rc, out, _ = native("consumer", "bootstrap", CONTROL); ev(kind="bootstrap", rc=rc, out=out.strip()[-200:])
    a = signer("agent-a", 0xA1, 1)
    b = signer("agent-b", 0xB2, 2)
    for label in ("agent-a", "agent-b"):
        rc, out, _ = native("consumer", "register", CONTROL, label, "fn.test", W / label / "registered.fncu")
        ev(kind="register", label=label, rc=rc, out=out.strip()[-200:])
    # BP debt: a DTN journal to a refused peer
    bp = W / "bp"; bp.mkdir(); (bp / "adu").write_bytes(b"mixed workload debt " * 50)
    reservation = socket.socket(); reservation.bind(("127.0.0.1", 0)); refused = reservation.getsockname()[1]
    k = [0]

    def signed_report():
        k[0] += 1
        rc, out, dt = consumer(a, "report", "op-%d" % k[0], "mixed-report-%d" % k[0])
        lat("signed-report", dt, rc == 0); ev(kind="report", n=k[0], rc=rc, tail=out.strip()[-160:])

    def consumer_wake():
        rc, out, dt = consumer(b, "wake")
        lat("consumer-wake", dt, rc == 0); ev(kind="wake", rc=rc, tail=out.strip()[-160:])

    g = [0]

    def control():
        g[0] += 1
        rc, out, dt = native("operator", cfg, "group", "create", "fn.mixed%d" % g[0])
        lat("control-group-create", dt, rc == 0); ev(kind="group-create", n=g[0], rc=rc, tail=out.strip()[-160:])
        rc, out, dt = native("operator", cfg, "control", "grant", (bytes([0xA1]) * 32).hex(), "keys", "fn.test")
        lat("control-grant", dt, rc == 0); ev(kind="control-grant", rc=rc, tail=out.strip()[-160:])

    def maintenance():
        rc, out, dt = native("operator", cfg, "status")
        lat("status-live", dt, rc == 0)
        line = [l for l in out.splitlines() if l.startswith(("transactions=", "headroom", "open=", "checkpoint-file"))]
        ev(kind="status", rc=rc, lines=line)
        rc, out, dt = native("operator", cfg, "health")
        lat("health-live", dt, rc in (0, 19)); ev(kind="health", rc=rc, tail=out.strip()[-160:])

    j = [0]

    def bp_debt():
        j[0] += 1
        rc, out, dt = native("bp-service", "run", "127.0.0.1", refused, bp / "adu", bp / "journal", "dtn://fn-a/",
                             "dtn://fn-b/", "work-%d" % j[0], "attempt-%d" % j[0], "0", image=DTN)
        lat("bp-queue", dt, rc == 7); ev(kind="bp-queue", n=j[0], rc=rc, tail=out.strip()[-120:])

    def bp_resume():
        rc, out, dt = native("bp-service", "resume", bp / "journal", "dtn://fn-a/", image=DTN)
        lat("bp-resume", dt, rc == 7); ev(kind="bp-resume", rc=rc, tail=out.strip()[-160:])

    samples = []

    def sample():
        try:
            st = open("/proc/%d/stat" % owner.pid).read().split(")")[1].split()
            tick = os.sysconf("SC_CLK_TCK")
            cpu = (int(st[11]) + int(st[12])) / tick
            vm = {l.split(":")[0]: l.split()[1] for l in open("/proc/%d/status" % owner.pid) if l.startswith(("VmRSS", "VmHWM"))}
        except FileNotFoundError:
            cpu, vm = None, {}
        du = subprocess.run(["du", "-sb", str(store)], capture_output=True, text=True).stdout.split()[0]
        inodes = sum(len(fs) + len(ds) for _, ds, fs in os.walk(store))
        bpj = subprocess.run(["du", "-sb", str(bp / "journal")], capture_output=True, text=True).stdout.split()
        samples.append({"t": round(time.time() - T0, 1), "cpu_s": cpu, "rss_kib": vm.get("VmRSS"), "hwm_kib": vm.get("VmHWM"),
                        "store_octets": int(du), "store_inodes": inodes, "bp_journal_octets": int(bpj[0]) if bpj else 0,
                        "owner_alive": owner.poll() is None})

    threads = [threading.Thread(target=readers, args=(port, i), daemon=True) for i in range(3)]
    threads.append(threading.Thread(target=poster, args=(port,), daemon=True))
    for period, fn in ((20, signed_report), (30, consumer_wake), (120, control), (30, maintenance), (60, bp_debt),
                       (300, bp_resume), (10, sample)):
        threads.append(threading.Thread(target=every, args=(period, fn), daemon=True))
    sample()
    for t in threads:
        t.start()
    end = T0 + HOUR
    while time.time() < end and owner.poll() is None:
        time.sleep(5)
    STOP.set()
    for t in threads:
        t.join(timeout=900)
    sample()
    alive = owner.poll() is None
    owner.send_signal(signal.SIGTERM)
    try:
        owner.wait(300)
    except subprocess.TimeoutExpired:
        owner.kill(); owner.wait()
    rest = owner.stdout.read().decode("utf-8", "replace")
    reservation.close()
    rc, recov, dt = native("operator", cfg, "recover")
    rc2, stat, _ = native("operator", cfg, "status")
    sa, sb = consumer(a, "summary"), consumer(b, "summary")
    result = {"image": str(IMG), "hour_seconds": HOUR, "owner_alive_at_end": alive, "owner_exit": owner.returncode,
              "owner_stdout_after_listening": rest[-2000:], "latency": {k: summary(v) for k, v in LAT.items()},
              "samples": samples, "events": EVENTS, "recover": [rc, recov[-600:], dt], "status_after": [rc2, stat[-1500:]],
              "agent_a_summary": sa[1][-3000:], "agent_b_summary": sb[1][-3000:]}
    (W / "mixed.json").write_text(json.dumps(result, indent=1))
    print(json.dumps({"latency": result["latency"], "first": samples[0], "last": samples[-1],
                      "owner_alive_at_end": alive, "owner_exit": owner.returncode, "recover_rc": rc,
                      "event_kinds": {k: sum(1 for e in EVENTS if e["kind"] == k) for k in sorted({e["kind"] for e in EVENTS})},
                      "nonzero": [e for e in EVENTS if e.get("rc") not in (None, 0) and e["kind"] not in ("bp-queue", "bp-resume", "health")][:20]},
                     indent=1))


if __name__ == "__main__":
    main()
