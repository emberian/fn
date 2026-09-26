#!/usr/bin/env python3
"""Signed POST cost against retained history (lane signed-history-index).

usage: measure_signed.py TREE IMAGE WORK --n N [--signed S] [--rounds R]

One scratch store (operator init, profile `scale`, 2 KiB articles), one
owner.  Enrolls one hybrid author, then loads N articles over one NNTP
connection: S of them hybrid-signed carriers (spread evenly), N - S
unsigned, all about 2 KiB.  Then R rounds, each one unsigned and one signed
POST on a fresh connection, timed from the article's last octet to the
reply line (the owner's whole commit, prepare to durable reply).  Prints one
ROUND line per round and one SUMMARY line with the medians.  Carriers are
signed before the owner starts, by the image's own hybrid-sign-carrier."""
import argparse, json, os, socket, subprocess, sys, time
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument("tree"); p.add_argument("image"); p.add_argument("work")
p.add_argument("--n", type=int, required=True)
p.add_argument("--signed", type=int, default=32)
p.add_argument("--rounds", type=int, default=7)
p.add_argument("--octets", type=int, default=2048)
a = p.parse_args()
tree, image, work = Path(a.tree), Path(a.image).resolve(), Path(a.work)
sys.path.insert(0, str(tree))
from tests.test_fn_verify import big_body, source_for, dot_stuff
from tests.native_process import wait_for_announcement, stop_and_diagnostics
OPENSSL = "/tank/fn/toolchains/openssl-3.5.8/bin/openssl"
work.mkdir(parents=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE"); env.pop("ACL2_SYSTEM_BOOKS", None)
def fn(*args, timeout=1800):
    r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=tree, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if r.returncode != 0:
        raise SystemExit("{} -> {}: {}".format(args[:2], r.returncode, r.stderr.decode()[-2000:]))
    return r
principal = work / "principal.bin"; principal.write_bytes(bytes([0x55]) * 32)
edp, eds = work / "ed-public.bin", work / "ed-secret.bin"
edp.write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
eds.write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                              "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
mlpriv, mlpub = work / "ml-private.pem", work / "ml-public.pem"
subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(mlpriv)], check=True, env=env)
subprocess.run([OPENSSL, "pkey", "-in", str(mlpriv), "-pubout", "-out", str(mlpub)], check=True, env=env)
body = big_body(max(0, a.octets - 400))
def carrier(stem):
    src = work / (stem + ".eml"); out = work / (stem + "-carried.eml")
    src.write_bytes(source_for("<{}@example.invalid>".format(stem), body=body))
    fn("hybrid-sign-carrier", principal, edp, eds, mlpub, mlpriv, src, out)
    return out.read_bytes()
t0 = time.perf_counter()
preload_signed = {(i * a.n) // max(1, a.signed): carrier("shi-pre-{}".format(i)) for i in range(a.signed)}
probe_signed = [carrier("shi-probe-{}".format(r)) for r in range(a.rounds)]
print("SIGNED {} preload + {} probe carriers in {:.1f}s".format(len(preload_signed), len(probe_signed),
                                                          time.perf_counter() - t0), flush=True)
with socket.socket() as probe:
    probe.bind(("127.0.0.1", 0)); port = probe.getsockname()[1]
store, control, config = work / "store", work / "control.sock", work / "fn.toml"
config.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n'
                  % (store, port, control), encoding="ascii")
fn("operator", config, "init", "--profile", "scale", "--max-transactions", "1048576",
   "--max-article-octets", "65536", "fn.test")
err = open(work / "owner.stderr", "wb")
owner = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], cwd=tree,
                         env=env, stdout=subprocess.PIPE, stderr=err)
def connect():
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
def post(octets):
    s, f = connect()
    try:
        return post_on(f, octets)
    finally:
        f.write(b"QUIT\r\n"); s.close()
def med(xs):
    xs = sorted(xs); return xs[len(xs) // 2]
try:
    line = wait_for_announcement(owner, b"LISTENING "); assert line.startswith(b"LISTENING "), line
    fn("hybrid-enroll", control, "1", principal, edp, mlpub)
    t0 = time.perf_counter(); s, f = connect(); signed_times = []
    for i in range(a.n):
        if i in preload_signed:
            signed_times.append(post_on(f, preload_signed[i]))
        else:
            post_on(f, source_for("<shi-load-{}@example.invalid>".format(i), body=body))
    f.write(b"QUIT\r\n"); s.close()
    print("LOAD n={} signed={} in {:.1f}s; preload signed POST first={:.3f}s last={:.3f}s".format(
        a.n, a.signed, time.perf_counter() - t0, signed_times[0], signed_times[-1]), flush=True)
    us, ss = [], []
    for r in range(a.rounds):
        u = post(source_for("<shi-probe-u-{}@example.invalid>".format(r), body=body))
        g = post(probe_signed[r]); us.append(u); ss.append(g)
        print("ROUND {} unsigned={:.4f}s signed={:.4f}s".format(r, u, g), flush=True)
    print("SUMMARY " + json.dumps({"n": a.n, "signed_in_history": a.signed, "rounds": a.rounds,
          "octets": a.octets, "median_unsigned_s": med(us), "median_signed_s": med(ss),
          "preload_signed_s": signed_times}), flush=True)
finally:
    print(stop_and_diagnostics(owner, timeout=300)[-400:])
