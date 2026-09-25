#!/usr/bin/env python3
"""Scratch (signed-path lane): time and profile signing and signed POSTs.

usage: prof_signed.py TREE IMAGE WORK [--sign-prof-seconds N] [--no-sign-prof]
Signs 64 KiB and 200 KiB sources with hybrid-sign-carrier (timed), optionally
profiles the first N seconds of a 200 KiB signing, then runs an owner (plain
NNTP, profile A = 4 MiB), enrolls, and POSTs unsigned/signed at both sizes
(timed); the signed 200 KiB POST is sampled with sb-sprof."""
import argparse, os, socket, subprocess, sys, threading, time
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument("tree"); p.add_argument("image"); p.add_argument("work")
p.add_argument("--sign-prof-seconds", type=float, default=60.0)
p.add_argument("--no-sign-prof", action="store_true")
p.add_argument("--sizes", default="65536,204800")
a = p.parse_args()
tree, image, work = Path(a.tree), Path(a.image).resolve(), Path(a.work)
sys.path.insert(0, str(tree))
from tests.test_fn_verify import big_body, source_for, dot_stuff
from tests.native_process import wait_for_announcement, stop_and_diagnostics
OPENSSL = "/tank/fn/toolchains/openssl-3.5.8/bin/openssl"
work.mkdir(parents=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
def fn(*args, extra=None, timeout=1800):
    e = dict(env, **(extra or {}))
    t0 = time.perf_counter()
    r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=tree, env=e,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    el = time.perf_counter() - t0
    if r.returncode != 0:
        raise SystemExit("{} -> {}: {}".format(args[:2], r.returncode, r.stderr.decode()[-2000:]))
    return r, el
principal = work / "principal.bin"; principal.write_bytes(bytes([0x55]) * 32)
edp, eds = work / "ed-public.bin", work / "ed-secret.bin"
edp.write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
eds.write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                              "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
mlpriv, mlpub = work / "ml-private.pem", work / "ml-public.pem"
subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(mlpriv)], check=True, env=env)
subprocess.run([OPENSSL, "pkey", "-in", str(mlpriv), "-pubout", "-out", str(mlpub)], check=True, env=env)
sizes = [int(x) for x in a.sizes.split(",")]
signed, unsigned = {}, {}
for n in sizes:
    src = source_for("<sp-signed-{}@example.invalid>".format(n), body=big_body(n))
    (work / "src-{}.eml".format(n)).write_bytes(src)
    unsigned[n] = source_for("<sp-unsigned-{}@example.invalid>".format(n), body=big_body(n))
    out = work / "carried-{}.eml".format(n)
    _, el = fn("hybrid-sign-carrier", principal, edp, eds, mlpub, mlpriv, work / "src-{}.eml".format(n), out)
    signed[n] = out.read_bytes()
    print("SIGN size={} source={} carried={} wall={:.2f}s".format(n, len(src), len(signed[n]), el), flush=True)
if not a.no_sign_prof:
    n = sizes[-1]; sp = work / "sign-sprof"; sp.mkdir(); (sp / "start").write_text("x")
    out = work / "carried-prof-{}.eml".format(n)
    proc = subprocess.Popen([str(image), "--fn", "hybrid-sign-carrier", principal, edp, eds, mlpub, mlpriv,
                             work / "src-{}.eml".format(n), out], cwd=tree,
                            env=dict(env, FN_SPROF_DIR=str(sp)), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        proc.wait(timeout=a.sign_prof_seconds)
        print("SIGN-PROF finished before the window", flush=True)
    except subprocess.TimeoutExpired:
        (sp / "stop").write_text("x")
        for _ in range(600):
            if (sp / "done").exists(): break
            time.sleep(0.5)
        print("SIGN-PROF window {}s done={}".format(a.sign_prof_seconds, (sp / "done").exists()), flush=True)
        proc.wait(timeout=1800)
with socket.socket() as probe:
    probe.bind(("127.0.0.1", 0)); port = probe.getsockname()[1]
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
                  % (store, port, control), encoding="ascii")
fn("operator", config, "init", "--max-article-octets", "4194304", "fn.test")
sp = work / "post-sprof"; sp.mkdir()
err = open(work / "owner.stderr", "wb")
owner = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], cwd=tree,
                         env=dict(env, FN_SPROF_DIR=str(sp)), stdout=subprocess.PIPE, stderr=err)
def post(octets):
    s = socket.create_connection(("127.0.0.1", port), timeout=1800)
    f = s.makefile("rwb", buffering=0)
    assert f.readline().startswith(b"20")
    f.write(b"POST\r\n"); l = f.readline(); assert l.startswith(b"340"), l
    t0 = time.perf_counter()
    f.write(dot_stuff(octets) + b".\r\n"); reply = f.readline().decode().strip()
    el = time.perf_counter() - t0
    f.write(b"QUIT\r\n"); s.close()
    return reply, el
try:
    line = wait_for_announcement(owner, b"LISTENING "); assert line.startswith(b"LISTENING "), line
    fn("hybrid-enroll", control, "1", principal, edp, mlpub)
    for n in sizes:
        r, el = post(unsigned[n]); print("POST unsigned size={} octets={} wall={:.2f}s reply={}".format(n, len(unsigned[n]), el, r[:90]), flush=True)
        last = n == sizes[-1]
        if last:
            (sp / "start").write_text("x"); time.sleep(0.3)
        r, el = post(signed[n]); print("POST signed size={} octets={} wall={:.2f}s reply={}".format(n, len(signed[n]), el, r[:90]), flush=True)
        if last:
            (sp / "stop").write_text("x")
            for _ in range(600):
                if (sp / "done").exists(): break
                time.sleep(0.5)
    for n in sizes:
        r, _ = fn("hybrid-verify-carrier", work / "carried-{}.eml".format(n), mlpub)
        print("VERIFY-CARRIER size={} {}".format(n, r.stdout.decode().split()[0]), flush=True)
finally:
    print(stop_and_diagnostics(owner, timeout=120)[-400:])
