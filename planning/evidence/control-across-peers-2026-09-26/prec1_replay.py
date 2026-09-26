"""PKT-154 replay probe: a pre-C1 image stores a signed cancel under its
Newsgroups; the current image replays a copy of that store.
Usage: python3 prec1_replay.py OLD_TREE NEW_TREE WORK"""
import json, os, shutil, socket, subprocess, sys, time
from pathlib import Path
OLD, NEW, WORK = (Path(a) for a in sys.argv[1:4])
CONTROL_ONLY = len(sys.argv) > 4 and sys.argv[4] == "ordinary-only"
OPENSSL = "/tank/fn/toolchains/openssl-3.5.8/bin/openssl"
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
WORK.mkdir(parents=True, exist_ok=True)
out = {}

def run(image, args, cwd):
    r = subprocess.run([str(image), "--fn", *map(str, args)], cwd=cwd, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
    return r.returncode, r.stdout.decode("utf-8", "replace"), r.stderr.decode("utf-8", "replace")[-600:]

def port():
    s = socket.socket(); s.bind(("127.0.0.1", 0)); p = s.getsockname()[1]; s.close(); return p

def start(image, cwd, config, log):
    p = subprocess.Popen([str(image), "--fn", "operator", str(config), "run"], cwd=cwd, env=env,
                         stdout=subprocess.PIPE, stderr=open(log, "wb"))
    deadline = time.time() + 180
    while time.time() < deadline:
        line = p.stdout.readline()
        if not line: break
        if line.startswith(b"LISTENING "): return p
    p.kill(); p.wait(); return None

def ask(p_, lines):
    with socket.create_connection(("127.0.0.1", p_), timeout=30) as c:
        f = c.makefile("rwb", buffering=0); f.readline(); res = []
        for l in lines:
            f.write(l.encode() + b"\r\n"); r = f.readline().decode().strip(); res.append(r)
            if r[:3] in ("211", "220") and l.startswith(("ARTICLE", "LISTGROUP")):
                while f.readline() not in (b".\r\n", b""): pass
        return res

old_img, new_img = OLD / "build/fn-host-developer", NEW / "build/fn-host-developer"
store = WORK / "store"; ctl = WORK / "control.sock"; pp = port()
cfg = WORK / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (store, pp, ctl))
out["old-init"] = run(old_img, ["store", store, "init", "fn.test", "control.cancel"], OLD)
keys = WORK / "keys"; keys.mkdir(exist_ok=True)
(keys / "principal.bin").write_bytes(bytes([0x55]) * 32)
edpub = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
(keys / "ed-public.bin").write_bytes(bytes.fromhex(edpub))
(keys / "ed-secret.bin").write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60" + edpub))
subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", keys / "ml.pem"], check=True)
subprocess.run([OPENSSL, "pkey", "-in", keys / "ml.pem", "-pubout", "-out", keys / "ml-public.pem"], check=True)
node = start(old_img, OLD, cfg, WORK / "old-node.log")
out["old-started"] = node is not None
out["old-enroll"] = run(old_img, ["hybrid-enroll", ctl, "1", keys / "principal.bin", keys / "ed-public.bin", keys / "ml-public.pem"], OLD)

def author(image, cwd, stem, extra):
    src = WORK / (stem + ".eml")
    src.write_bytes(("From: poster@example.invalid\r\nNewsgroups: fn.test\r\nSubject: pre-C1 %s\r\n"
                     "Date: Fri, 25 Sep 2026 03:00:00 +0000\r\nMessage-ID: <prec1-%s@example.invalid>\r\n%s\r\nbody\r\n"
                     % (stem, stem, extra)).encode())
    rc, so, se = run(image, ["hybrid-sign", keys / "principal.bin", keys / "ed-public.bin", keys / "ed-secret.bin",
                            keys / "ml-public.pem", keys / "ml.pem", src], cwd)
    parts = dict(l.split() for l in so.splitlines() if len(l.split()) == 2)
    (WORK / (stem + ".ed")).write_bytes(bytes.fromhex(parts["ed25519"]))
    (WORK / (stem + ".ml")).write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
    rc2, so2, se2 = run(image, ["hybrid-author", ctl, "1", src, WORK / (stem + ".ed"), WORK / (stem + ".ml"), keys / "ml-public.pem"], cwd)
    return rc2, so2[-300:], se2

out["old-author-target"] = author(old_img, OLD, "target", "")
out["old-author-cancel"] = None if CONTROL_ONLY else author(old_img, OLD, "cancel", "Control: cancel <prec1-target@example.invalid>\r\n")
out["old-answers"] = ask(pp, ["LISTGROUP fn.test", "LISTGROUP control.cancel", "ARTICLE <prec1-target@example.invalid>",
                               "ARTICLE <prec1-cancel@example.invalid>"])
node.terminate(); node.wait(timeout=60)
copy = WORK / "store-copy"; shutil.copytree(store, copy, ignore=shutil.ignore_patterns("*.sock", "*.lock"))
pp2 = port(); cfg2 = WORK / "fn-new.toml"
cfg2.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (copy, pp2, WORK / "new.sock"))
new = start(new_img, NEW, cfg2, WORK / "new-node.log")
out["new-started"] = new is not None
if new:
    out["new-answers"] = ask(pp2, ["LISTGROUP fn.test", "LISTGROUP control.cancel", "ARTICLE <prec1-target@example.invalid>",
                                    "ARTICLE <prec1-cancel@example.invalid>"])
    new.terminate(); new.wait(timeout=60)
out["new-node-log-tail"] = (WORK / "new-node.log").read_text("utf-8", "replace")[-1500:]
print("PREC1-REPLAY-WITNESS " + json.dumps(out, default=str, sort_keys=True))
