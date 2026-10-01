#!/usr/bin/env python3
"""Signed POST profile and owner CPU (lane signed-post-linear, 2026-09-26).

    prof_signed.py load TREE IMAGE WORK --n N [--signed S] [--probes K]
    prof_signed.py run  TREE IMAGE WORK TAG [--k K] [--sprof]

load: one store under WORK/store (operator init, profile `scale`,
--max-transactions 1048576, --max-article-octets 16384, group fn.test), one
hybrid author enrolled, N POSTs of about 2 KiB over one connection, S of them
hybrid-signed carriers spread evenly (measure_signed.py's history); K probe
carriers and K unsigned probes are written under WORK/probes/ for later runs.
Carriers are signed by the image's own hybrid-sign-carrier.

run: copies WORK/store to WORK/TAG/store (a fresh copy per run, so the probes
are new), opens it with IMAGE, warms with one unsigned and one signed POST,
then times K unsigned and K signed POSTs, each batch on one connection opened
before it (no greeting in the figure), from the
terminating line to the reply, with the owner's CPU (/proc/PID/stat
utime+stime) over each batch.  --sprof: IMAGE is the profiling twin
(prof-raw.lisp); the sb-sprof :cpu window (1 ms, all threads) covers the K
signed POSTs only; flat.txt and graph.txt land in WORK/TAG/sprof/.
Prints one JSON line RESULT."""
import argparse, json, os, shutil, socket, subprocess, sys, time
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument("mode", choices=["load", "run"])
p.add_argument("tree"); p.add_argument("image"); p.add_argument("work")
p.add_argument("tag", nargs="?")
p.add_argument("--n", type=int, default=1000)
p.add_argument("--signed", type=int, default=32)
p.add_argument("--probes", type=int, default=40)
p.add_argument("--k", type=int, default=20)
p.add_argument("--sprof", action="store_true")
a = p.parse_args()
tree, image, work = Path(a.tree), Path(a.image).resolve(), Path(a.work)
sys.path.insert(0, str(tree))
from tests.test_fn_verify import big_body, source_for, dot_stuff  # noqa: E402
from tests.native_process import wait_for_announcement, stop_and_diagnostics  # noqa: E402
OPENSSL = "/tank/fn/toolchains/openssl-3.5.8/bin/openssl"
TICK = os.sysconf("SC_CLK_TCK")
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
body = big_body(2048 - 400)


def fn(*args, timeout=1800):
    r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=tree, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if r.returncode != 0:
        raise SystemExit("{} -> {}: {}".format(args[:2], r.returncode, r.stderr.decode()[-2000:]))
    return r


def cpu_s(pid):
    f = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1].split()
    return (int(f[11]) + int(f[12])) / TICK


def write_config(dirp, store):
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0)); port = probe.getsockname()[1]
    config = dirp / "fn.toml"
    config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                      '[control]\npath = "%s"\n' % (store, port, dirp / "control.sock"), encoding="ascii")
    return config, port


def owner(dirp, config, extra_env=None):
    e = dict(env, **(extra_env or {}))
    err = open(dirp / "owner.stderr", "wb")
    proc = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], cwd=tree,
                            env=e, stdout=subprocess.PIPE, stderr=err)
    line = wait_for_announcement(proc, b"LISTENING ", timeout=3600)
    assert line.startswith(b"LISTENING "), line
    return proc


def connect(port):
    s = socket.create_connection(("127.0.0.1", port), timeout=3600)
    f = s.makefile("rwb", buffering=0)
    assert f.readline().startswith(b"20")
    return s, f


def post_on(f, octets):
    f.write(b"POST\r\n"); l = f.readline(); assert l.startswith(b"340"), l
    f.write(dot_stuff(octets)); t0 = time.perf_counter()
    f.write(b".\r\n"); reply = f.readline().decode().strip()
    el = time.perf_counter() - t0
    assert reply.startswith("240"), reply
    return el


def post(port, octets):
    s, f = connect(port)
    try:
        return post_on(f, octets)
    finally:
        f.write(b"QUIT\r\n"); s.close()


def med(xs):
    xs = sorted(xs); return xs[len(xs) // 2]


def box():
    return Path("/proc/loadavg").read_text().strip()


if a.mode == "load":
    work.mkdir(parents=True)
    keys = work / "keys"; keys.mkdir()
    principal = keys / "principal.bin"; principal.write_bytes(bytes([0x55]) * 32)
    edp, eds = keys / "ed-public.bin", keys / "ed-secret.bin"
    edp.write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
    eds.write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                                  "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
    mlpriv, mlpub = keys / "ml-private.pem", keys / "ml-public.pem"
    subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(mlpriv)], check=True, env=env)
    subprocess.run([OPENSSL, "pkey", "-in", str(mlpriv), "-pubout", "-out", str(mlpub)], check=True, env=env)
    probes = work / "probes"; probes.mkdir()

    def carrier(stem, outdir):
        src = outdir / (stem + ".eml"); out = outdir / (stem + "-carried.eml")
        src.write_bytes(source_for("<{}@example.invalid>".format(stem), body=body))
        fn("hybrid-sign-carrier", principal, edp, eds, mlpub, mlpriv, src, out)
        src.unlink()
        return out.read_bytes()
    t0 = time.perf_counter()
    pre = work / "preload"; pre.mkdir()
    preload = {(i * a.n) // max(1, a.signed): carrier("spl-pre-{}".format(i), pre) for i in range(a.signed)}
    for k in range(a.probes):
        carrier("spl-probe-s-{}".format(k), probes)
        (probes / "spl-probe-u-{}.eml".format(k)).write_bytes(
            source_for("<spl-probe-u-{}@example.invalid>".format(k), body=body))
    sign_s = time.perf_counter() - t0
    store = work / "store"
    config, port = write_config(work, store)
    fn("operator", config, "init", "--profile", "scale", "--max-transactions", "1048576",
       "--max-article-octets", "16384", "fn.test")
    proc = owner(work, config)
    try:
        fn("hybrid-enroll", work / "control.sock", "1", principal, edp, mlpub)
        t0 = time.perf_counter(); s, f = connect(port); st = []
        for i in range(a.n):
            if i in preload:
                st.append(post_on(f, preload[i]))
            else:
                post_on(f, source_for("<spl-load-{}@example.invalid>".format(i), body=body))
        f.write(b"QUIT\r\n"); s.close()
        out = {"mode": "load", "n": a.n, "signed": a.signed, "probes": a.probes, "sign_s": sign_s,
               "load_s": time.perf_counter() - t0, "preload_signed_s": st, "loadavg": box()}
    finally:
        print(stop_and_diagnostics(proc, timeout=600)[-400:])
    print("RESULT " + json.dumps(out), flush=True)
else:
    run = work / a.tag
    shutil.rmtree(run, ignore_errors=True); run.mkdir()
    shutil.copytree(work / "store", run / "store", symlinks=True)
    config, port = write_config(run, run / "store")
    probes = work / "probes"
    sp = run / "sprof"
    extra = {}
    if a.sprof:
        sp.mkdir(); extra["FN_SPROF_DIR"] = str(sp)
    t0 = time.perf_counter()
    proc = owner(run, config, extra)
    out = {"mode": "run", "tag": a.tag, "image": str(image), "open_s": time.perf_counter() - t0,
           "k": a.k, "loadavg_before": box()}
    try:
        us = [(probes / "spl-probe-u-{}.eml".format(i)).read_bytes() for i in range(a.k + 1)]
        ss = [(probes / "spl-probe-s-{}-carried.eml".format(i)).read_bytes() for i in range(a.k + 1)]
        post(port, us[0]); post(port, ss[0])
        # One connection per batch, opened before the batch: the greeting is
        # not in the figure (f314a5a3's greeting still ran fn-statep).
        s, f = connect(port)
        c0 = cpu_s(proc.pid)
        ut = [post_on(f, u) for u in us[1:]]
        c1 = cpu_s(proc.pid)
        f.write(b"QUIT\r\n"); s.close()
        s, f = connect(port)
        if a.sprof:
            (sp / "start").write_text("1"); time.sleep(0.3)
        c2 = cpu_s(proc.pid)
        stt = [post_on(f, x) for x in ss[1:]]
        c3 = cpu_s(proc.pid)
        f.write(b"QUIT\r\n"); s.close()
        if a.sprof:
            (sp / "stop").write_text("1")
            t = time.perf_counter()
            while not (sp / "done").exists() and time.perf_counter() - t < 900:
                time.sleep(0.1)
            out["sprof_error"] = (sp / "error.txt").read_text() if (sp / "error.txt").exists() else None
        out.update({"unsigned_median_s": med(ut), "signed_median_s": med(stt),
                    "unsigned_owner_cpu_ms": 1000 * (c1 - c0) / a.k,
                    "signed_owner_cpu_ms": 1000 * (c3 - c2) / a.k,
                    "unsigned_s": ut, "signed_s": stt, "loadavg_after": box()})
    finally:
        print(stop_and_diagnostics(proc, timeout=600)[-400:])
    print("RESULT " + json.dumps(out), flush=True)
