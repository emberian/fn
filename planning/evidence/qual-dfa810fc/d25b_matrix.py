#!/usr/bin/env python3
"""D25 injection-inverse matrix on a native developer image (lane d25-injection-inverse).

Rows of planning/review-2026-09-24-gpt6-direction.md D25: Date present and
absent, one changed authored byte, an authored Date changed or removed, a lost
reply then restart then retry, a recipe v1 record (an older image) then retry
on this image, another injecting identity, and a second identical post under
a new Message-ID; unsigned and signed (FN-Authorship carriers).
Usage: d25b_matrix.py BRANCH_IMAGE V1_IMAGE WORKDIR PORT OPENSSL
Writes WORKDIR/rows.json and prints one line per row.
"""
import json, os, signal, socket, subprocess, sys, time
from pathlib import Path

BRANCH, V1, WORK, PORT, OPENSSL = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
WORK.mkdir(parents=True, exist_ok=True)
ROWS = []
DUP = b"441 posting failed; this article is already stored here"
CONFLICT = b"441 posting failed; a different article with this Message-ID is stored here"


def run(image, *args, timeout=180):
    return subprocess.run([str(image), "--fn", *map(str, args)], stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=False)


def config(store, name):
    cfg = WORK / (name + ".toml")
    cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                   '[control]\npath = "%s"\n' % (store, PORT, WORK / (name + ".sock")))
    return cfg


def start(image, cfg, label):
    err = open(WORK / ("owner-%s.err" % label), "wb")
    out = open(WORK / ("owner-%s.out" % label), "wb")
    proc = subprocess.Popen([str(image), "--fn", "operator", str(cfg), "run"], stdout=out, stderr=err)
    for _ in range(240):
        if b"LISTENING" in (WORK / ("owner-%s.out" % label)).read_bytes():
            return proc
        time.sleep(0.5)
    raise SystemExit("owner %s did not listen" % label)


def stop(proc, sig=signal.SIGTERM):
    proc.send_signal(sig)
    return proc.wait(timeout=120)


def session(lines):
    with socket.create_connection(("127.0.0.1", PORT), timeout=60) as sock:
        f = sock.makefile("rwb", buffering=0)
        assert f.readline().startswith(b"200")
        out = []
        for line in lines:
            f.write(line + b"\r\n")
            out.append(f.readline().rstrip(b"\r\n"))
        return out


def post(octets, read_reply=True):
    with socket.create_connection(("127.0.0.1", PORT), timeout=60) as sock:
        f = sock.makefile("rwb", buffering=0)
        assert f.readline().startswith(b"200")
        f.write(b"POST\r\n")
        assert f.readline().startswith(b"340")
        body = b"".join((b"." + l if l.startswith(b".") else l) for l in octets.splitlines(keepends=True))
        f.write(body + b".\r\n")
        if not read_reply:
            return None
        return f.readline().rstrip(b"\r\n")


def stat(msgid):
    return session([b"STAT " + msgid])[0]


def group():
    return session([b"GROUP fn.letters"])[0]


def article(msgid, body=b"d25b body", date=b"Thu, 24 Sep 2026 20:00:00 +0000", extra=b""):
    head = (b"From: d25b@example.invalid\r\nNewsgroups: fn.letters\r\nSubject: d25b\r\n")
    if date:
        head += b"Date: " + date + b"\r\n"
    return head + extra + b"Message-ID: " + msgid + b"\r\n\r\n" + body + b"\r\n"


def row(name, expect, got, **facts):
    ok = got is not None and got.startswith(expect)
    ROWS.append(dict(row=name, expect=expect.decode(), got=(got or b"").decode(), ok=ok,
                     at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), **facts))
    print(("PASS " if ok else "FAIL ") + name + " -> " + (got or b"").decode(), flush=True)


# --- keys for the signed rows (the test vectors of tests/test_native_hybrid_author.py)
keys = WORK / "keys"; keys.mkdir(exist_ok=True)
principal, edp, eds = keys / "principal.bin", keys / "ed-public.bin", keys / "ed-secret.bin"
principal.write_bytes(bytes([85]) * 32)
edp.write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
eds.write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                              "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
mlk, mlp = keys / "ml-private.pem", keys / "ml-public.pem"
subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(mlk)], check=True)
subprocess.run([OPENSSL, "pkey", "-in", str(mlk), "-pubout", "-out", str(mlp)], check=True)


def signed(stem, source):
    src, out = keys / (stem + ".eml"), keys / (stem + "-carried.eml")
    src.write_bytes(source)
    r = run(BRANCH, "hybrid-sign-carrier", principal, edp, eds, mlp, mlk, src, out)
    if r.returncode != 0:
        raise SystemExit("sign %s: %s" % (stem, r.stderr.decode()))
    return out.read_bytes()


# === Phase A: this branch's image, fresh store
s1 = WORK / "store1"
assert run(BRANCH, "store", s1, "init", "fn.letters").returncode == 0
cfg1 = config(s1, "s1")
owner = start(BRANCH, cfg1, "a")
enrolled = run(BRANCH, "hybrid-enroll", WORK / "s1.sock", "1", principal, edp, mlp)
print("enroll rc", enrolled.returncode, enrolled.stderr.decode()[-200:], flush=True)

dated, dateless = b"<d25b-dated@example.invalid>", b"<d25b-dateless@example.invalid>"
row("U1 Date present: original", b"240", post(article(dated)))
n_dated = stat(dated)
time.sleep(1.2)
row("U1 Date present: resend 1.2 s later", DUP, post(article(dated)), stat_before=n_dated.decode(), stat_after=stat(dated).decode())
row("U2 Date absent: original", b"240", post(article(dateless, date=None)))
n_dateless = stat(dateless)
time.sleep(1.2)
row("U2 Date absent: resend 1.2 s later", DUP, post(article(dateless, date=None)), stat_before=n_dateless.decode(), stat_after=stat(dateless).decode())
row("U3 one changed authored byte", CONFLICT, post(article(dateless, body=b"d25b bodY", date=None)))
row("U4 authored Date changed", CONFLICT, post(article(dated, date=b"Thu, 24 Sep 2026 20:00:01 +0000")))
row("U5 authored Date removed", CONFLICT, post(article(dated, date=None)))
g_before_new = group()
row("U6 identical text, new Message-ID", b"240", post(article(b"<d25b-dated-second@example.invalid>")), group_before=g_before_new.decode(), group_after=group().decode())

sd = signed("sd", article(b"<d25b-signed-dated@example.invalid>", body=b"signed body"))
# A Date-less source is outside the portable FN-Authorship profile: the
# signing tool refuses it, so the signed rows all carry a Date.
src_sn = keys / "sn.eml"; src_sn.write_bytes(article(b"<d25b-signed-dateless@example.invalid>", body=b"signed body", date=None))
r_sn = run(BRANCH, "hybrid-sign-carrier", principal, edp, eds, mlp, mlk, src_sn, keys / "sn-carried.eml")
ROWS.append(dict(row="S2 signed, Date absent: the signer refuses the source", ok=r_sn.returncode != 0,
                 got=r_sn.stderr.decode().strip(), expect="refused by hybrid-sign-carrier"))
print("S2 signed Date-less:", r_sn.returncode, r_sn.stderr.decode().strip(), flush=True)
sx = signed("sx", article(b"<d25b-signed-dated@example.invalid>", body=b"signed bodY"))
row("S1 signed, Date present: original", b"240", post(sd))
time.sleep(1.2)
row("S1 signed, Date present: resend", DUP, post(sd))
row("S3 signed, changed byte, same Message-ID", CONFLICT, post(sx))

lost = b"<d25b-lost-reply@example.invalid>"
post(article(lost, date=None), read_reply=False)
time.sleep(1.5)
g_before_kill = group()
killed = stop(owner, signal.SIGKILL)
print("owner killed", killed, flush=True)

# === Phase B: restart on the same store, retry
owner = start(BRANCH, cfg1, "b")
g_after_restart = group()
row("R1 lost reply, restart, retry", DUP, post(article(lost, date=None)), group_before_kill=g_before_kill.decode(),
    group_after_restart=g_after_restart.decode(), group_after_retry=group().decode(), stat=stat(lost).decode())
row("R2 Date absent: resend after restart", DUP, post(article(dateless, date=None)), stat_after=stat(dateless).decode(), stat_before=n_dateless.decode())
row("R3 signed: resend after restart", DUP, post(sd))
print("owner stop", stop(owner), flush=True)

# === Phase D: another injecting identity on the same store
pol = run(BRANCH, "operator", cfg1, "policy", "set", "path-identity", "other-agent.example.invalid")
print("policy set rc", pol.returncode, pol.stdout.decode()[-200:], pol.stderr.decode()[-200:], flush=True)
owner = start(BRANCH, cfg1, "d")
row("I1 another path identity: resend of the Date-present article", CONFLICT, post(article(dated)))
row("I2 another path identity: resend of the Date-absent article", CONFLICT, post(article(dateless, date=None)))
print("owner stop", stop(owner), flush=True)

# === Phase C: recipe v1 records written by an older image, then this image
s2 = WORK / "store2"
assert run(V1, "store", s2, "init", "fn.letters").returncode == 0
cfg2 = config(s2, "s2")
v1d, v1n = b"<d25b-v1-dated@example.invalid>", b"<d25b-v1-dateless@example.invalid>"
owner = start(V1, cfg2, "c-v1")
row("V0 v1 image: Date present original", b"240", post(article(v1d)))
row("V0 v1 image: Date absent original", b"240", post(article(v1n, date=None)))
print("v1 owner stop", stop(owner), flush=True)
owner = start(BRANCH, cfg2, "c-v2")
row("V1 v1 record, Date present: resend on this image (read under v1)", DUP, post(article(v1d)))
row("V2 v1 record, Date absent: resend on this image (ambiguous, compared exactly)", CONFLICT, post(article(v1n, date=None)))
print("owner stop", stop(owner), flush=True)

(WORK / "rows.json").write_text(json.dumps(ROWS, indent=1))
print("ROWS %d PASS %d" % (len(ROWS), sum(r["ok"] for r in ROWS)))
