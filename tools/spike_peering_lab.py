#!/usr/bin/env python3
"""The spike/peering three-node lab: two fn nodes and an INN (SPIKE, D28).

    FN_NATIVE_HOST=IMAGE FN_OPENSSL=... python3 tools/spike_peering_lab.py \\
        --work /tank/fn/scratch/spike-peering/lab-RUN --inn-src /tank/fn/inn/2.7.4

A invites B; B (behind NAT: nothing dials it) accepts, enrolling the inviter
and one introduced author and carrying the other under a budget; A confirms.
B pulls from A with NEWNEWS.  A key succession (the node key) and an author
succession (a carried author) and a revocation propagate as signed articles
in fn.keys.  INN is a stranger: A pulls its fn.* and control.* by NEWNEWS
from nnrpd and feeds it by IHAVE; INN's control articles are filed on A in
control.*, never executed.  Every check is printed as `CHECK name ok|FAIL
observed`, and the run ends with a JSON summary.  Only PIDs this script
started are ever signalled.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fn_peering as fp  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
PORTS = {"A": 21191, "B": 21192, "innd": 21193, "nnrpd": 21194}
PATH_IDS = {"A": "a.spike.test", "B": "b.spike.test", "inn": "inn.spike.test"}
GROUPS_A = ["fn.test", "fn.keys", "fn.peering", "control", "control.cancel",
            "control.newgroup", "control.rmgroup"]
GROUPS_B = ["fn.test", "fn.keys", "fn.peering"]
CHECKS: list = []
STARTED: dict = {}


def check(name, ok, observed=""):
    CHECKS.append({"name": name, "ok": bool(ok), "observed": str(observed)[:400]})
    print("CHECK {} {} {}".format(name, "ok" if ok else "FAIL", str(observed)[:400]), flush=True)


def run(*argv, env=None, timeout=300):
    result = subprocess.run([str(a) for a in argv], stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, env=env, timeout=timeout)
    print("$ {}\n{}".format(" ".join(str(a) for a in argv)[:300], result.stdout[-1500:]),
          flush=True)
    return result


def tool(*argv):
    return run(sys.executable, ROOT / "tools" / "fn_peering.py", *argv)


def img(*argv, timeout=300):
    return run(fp.image_path(), "--fn", *argv, timeout=timeout)


# ------------------------------------------------------------------ fn nodes

def node_config(work, name):
    base = work / name
    base.mkdir(parents=True, exist_ok=True)
    config = base / "fn.toml"
    config.write_text(
        '[store]\npath = "{s}"\n[listener]\nhost = "127.0.0.1"\nport = {p}\n'
        '[control]\npath = "{c}"\n[log]\npath = "{l}"\n'.format(
            s=base / "store", p=PORTS[name], c=base / "control.sock", l=base / "fn.log"))
    return config


def start_node(work, name):
    config = work / name / "fn.toml"
    out = open(work / name / "run.out", "ab")
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    proc = subprocess.Popen([fp.image_path(), "--fn", "operator", str(config), "run"],
                            stdout=out, stderr=subprocess.STDOUT, env=env)
    STARTED[name] = proc
    for _ in range(240):
        if port_open(PORTS[name]) and (work / name / "control.sock").exists():
            print("node {} up pid={}".format(name, proc.pid), flush=True)
            return proc
        if proc.poll() is not None:
            break
        time.sleep(0.5)
    raise SystemExit("node {} did not start; see {}".format(name, work / name / "run.out"))


def stop(name):
    proc = STARTED.pop(name, None)
    if proc is None:
        return
    if isinstance(proc, int):
        try:
            os.kill(proc, signal.SIGTERM)
        except ProcessLookupError:
            pass
        return
    proc.send_signal(signal.SIGTERM)
    try:
        proc.wait(timeout=60)
    except subprocess.TimeoutExpired:
        proc.kill()


def port_open(port):
    with socket.socket() as s:
        s.settimeout(1)
        return s.connect_ex(("127.0.0.1", port)) == 0


def post(port, octets):
    with fp.Nntp("127.0.0.1", port) as n:
        status = n.command("POST")
        if not status.startswith("340"):
            return status
        body = b"".join((b"." + l if l.startswith(b".") else l)
                        for l in octets.splitlines(keepends=True))
        n.file.write(body + b".\r\n")
        return n.line()


def ihave(port, bind, msgid, octets):
    with fp.Nntp("127.0.0.1", port, bind=bind) as n:
        return n.ihave(msgid, octets)


def relayed(octets, path):
    """The relay fields a neighbour adds; the carrier binds only the source."""
    return b"Path: " + path.encode() + b"!not-for-mail\r\n" + octets


def verdict(port, msgid):
    with fp.Nntp("127.0.0.1", port) as n:
        return n.verdict(msgid)


def fetch(port, msgid):
    with fp.Nntp("127.0.0.1", port) as n:
        return n.article(msgid)


def signed_article(keys, group, msgid, subject, body, work):
    source = ("From: author@spike.test\r\nDate: {}\r\nNewsgroups: {}\r\nSubject: {}\r\n"
              "Message-ID: {}\r\n\r\n{}\r\n").format(fp.rfc5322_date(), group, subject,
                                                   msgid, body).encode()
    return keys.sign(source, msgid.strip("<>").replace("@", "_"))


def pull(work, source, into, bind, groups, state):
    return tool("pull", "--from", "127.0.0.1:{}".format(source),
                "--into", "127.0.0.1:{}".format(into), "--bind", bind,
                "--groups", groups, "--state", work / state, "--rounds", "1")


def log_lines(work, name, needle):
    try:
        return [l for l in (work / name / "fn.log").read_text(errors="replace").splitlines()
                if needle in l]
    except FileNotFoundError:
        return []


# ------------------------------------------------------------------ INN

INN_CONF = """pathhost:               {pid}
domain:                 spike.test
organization:           "fn spike peering lab"
server:                 127.0.0.1
mta:                    "/bin/true %s"
port:                   {innd}
bindaddress:            127.0.0.1
hismethod:              hisv6
ovmethod:               tradindexed
enableoverview:         true
allownewnews:           true
maxartsize:             1000000
artcutoff:              0
wanttrash:              false
nnrpdposthost:          none
runasuser:              {user}
runasgroup:             {group}
pathnews:               {prefix}
logipaddr:              true
xrefslave:              false
"""
INCOMING_CONF = """streaming: true
max-connections: 8
peer fn {{
    hostname: 127.0.0.1
    patterns: fn.*
    streaming: true
}}
"""
NEWSFEEDS = "ME/{pid}:*::\n"
READERS_CONF = """auth "localhost" {{
    hosts: "localhost, 127.0.0.1, ::1"
    default: "<localhost>"
}}
access "localhost" {{
    users: "<localhost>"
    newsgroups: "*"
    access: RPA
}}
"""


def inn_setup(work, src):
    prefix = work / "inn"
    if prefix.exists():
        shutil.rmtree(prefix)
    for sub in ("bin", "lib", "etc", "share", "doc"):
        if (Path(src) / sub).exists():
            shutil.copytree(Path(src) / sub, prefix / sub, symlinks=True)
    for sub in ("spool/articles", "spool/incoming", "spool/outgoing", "spool/overview",
                "spool/tmp", "spool/innfeed", "spool/archive", "db", "log", "run", "tmp",
                "http"):
        (prefix / sub).mkdir(parents=True, exist_ok=True)
    who = dict(user=os.environ.get("USER") or subprocess.check_output(["id", "-un"], text=True).strip(),
               group=subprocess.check_output(["id", "-gn"], text=True).strip())
    (prefix / "etc/inn.conf").write_text(INN_CONF.format(pid=PATH_IDS["inn"],
                                                          innd=PORTS["innd"],
                                                          prefix=prefix, **who))
    (prefix / "etc/incoming.conf").write_text(INCOMING_CONF.format())
    (prefix / "etc/newsfeeds").write_text(NEWSFEEDS.format(pid=PATH_IDS["inn"]))
    (prefix / "etc/readers.conf").write_text(READERS_CONF.format())
    db = prefix / "db"
    (db / "history").write_text("")
    env = inn_env(prefix)
    run(prefix / "bin/makedbz", "-i", "-f", db / "history", env=env)
    for ext in ("dir", "hash", "index"):
        if (db / "history.n.{}".format(ext)).exists():
            (db / "history.n.{}".format(ext)).rename(db / "history.{}".format(ext))
    (db / "active").write_text("control 0000000000 0000000001 y\njunk 0000000000 0000000001 n\n")
    (db / "active.times").write_text("")
    (db / "newsgroups").write_text("")
    return prefix


def inn_env(prefix):
    return dict(os.environ, INNCONF=str(prefix / "etc/inn.conf"))


def inn_start(prefix):
    env = inn_env(prefix)
    out = open(prefix / "log/innd-stdout.log", "ab")
    proc = subprocess.Popen([str(prefix / "bin/innd"), "-d"], stdout=out,
                            stderr=subprocess.STDOUT, env=env)
    STARTED["innd"] = proc
    for _ in range(60):
        r = subprocess.run([str(prefix / "bin/ctlinnd"), "-t", "2", "mode"], env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if "Server running" in r.stdout:
            break
        time.sleep(1)
    for group in ("fn.test", "fn.keys", "control.cancel", "control.newgroup"):
        run(prefix / "bin/ctlinnd", "newgroup", group, "y", "lab", env=env)
    out2 = open(prefix / "log/nnrpd-stdout.log", "ab")
    nnrpd = subprocess.Popen([str(prefix / "bin/nnrpd"), "-D", "-p", str(PORTS["nnrpd"])],
                             stdout=out2, stderr=subprocess.STDOUT, env=env)
    STARTED["nnrpd"] = nnrpd
    for _ in range(30):
        if port_open(PORTS["nnrpd"]):
            break
        time.sleep(1)
    return port_open(PORTS["innd"]) and port_open(PORTS["nnrpd"])


def unsigned(group, msgid, subject, body, extra=""):
    return ("From: inn-user@inn.spike.test\r\nNewsgroups: {}\r\nSubject: {}\r\n"
            "Message-ID: {}\r\n{}\r\n{}\r\n").format(group, subject, msgid, extra, body).encode()


# ------------------------------------------------------------------ the lab

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", required=True)
    ap.add_argument("--inn-src", default="/tank/fn/inn/2.7.4")
    ap.add_argument("--no-inn", action="store_true")
    args = ap.parse_args()
    work = Path(args.work)
    work.mkdir(parents=True, exist_ok=True)
    started = time.time()
    try:
        lab(work, args)
    finally:
        for name in list(STARTED):
            stop(name)
        summary = {"checks": CHECKS, "passed": sum(c["ok"] for c in CHECKS),
                   "failed": sum(not c["ok"] for c in CHECKS),
                   "elapsed_seconds": round(time.time() - started, 1),
                   "image": fp.image_path(),
                   "image_sha256": sha256(fp.image_path()),
                   "image_core_sha256": sha256(fp.image_path() + ".core")}
        for name in ("A", "B"):
            summary["log_sha256_" + name] = sha256(work / name / "fn.log")
        (work / "summary.json").write_text(json.dumps(summary, indent=1))
        print("SUMMARY passed={passed} failed={failed}".format(**summary), flush=True)


def sha256(path):
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return None


def lab(work, args):
    keys = {}
    for name in ("nodeA", "nodeB", "alice", "carol"):
        tool("keygen", work / "keys" / name)
        keys[name] = fp.Keys(work / "keys" / name)
    # Successor key directories keep the principal.
    for old, new in (("nodeA", "nodeA2"), ("carol", "carol2")):
        tool("keygen", work / "keys" / new, "--principal", keys[old].principal)
        keys[new] = fp.Keys(work / "keys" / new)

    configs = {n: node_config(work, n) for n in ("A", "B")}
    for n, groups in (("A", GROUPS_A), ("B", GROUPS_B)):
        r = img("operator", configs[n], "init", *groups)
        check("init-" + n, r.returncode == 0, r.stdout[-200:])
        r = img("operator", configs[n], "policy", "set", "path-identity", PATH_IDS[n])
        check("path-identity-" + n, r.returncode == 0, r.stdout[-200:])
    for n in ("A", "B"):
        start_node(work, n)
    # Each node enrols its own node principal; A enrols its two authors by hand.
    nodeA, nodeB = fp.Node(configs["A"]), fp.Node(configs["B"])
    for node, who in ((nodeA, "nodeA"), (nodeA, "alice"), (nodeA, "carol"), (nodeB, "nodeB")):
        check("enrol-{}-{}".format(node.config.parent.name, who),
              node.enroll(keys[who]) == 0, who)

    # ---------------------------------------------------------- invite/accept
    inv, acc = work / "invitation.eml", work / "acceptance.eml"
    r = tool("invite", "--node", configs["A"], "--keys", keys["nodeA"].dir, "--name", "B",
             "--path-id", PATH_IDS["A"], "--groups", "fn.*", "--host", "127.0.0.1",
             "--port", PORTS["A"], "--author", keys["alice"].dir, "--author",
             keys["carol"].dir, "--out", inv)
    check("invite", r.returncode == 0 and inv.exists(), r.stdout.strip()[-200:])
    # A tampered invitation is refused before anything is enrolled.
    bad = work / "invitation-tampered.eml"
    bad.write_bytes(inv.read_bytes().replace(b"Groups: fn.*", b"Groups: *\x20\x20", 1))
    r = tool("accept", bad, "--node", configs["B"], "--keys", keys["nodeB"].dir,
             "--path-id", PATH_IDS["B"], "--out", work / "never.eml")
    check("accept-refuses-tampered-invitation", r.returncode == 1, r.stdout.strip()[-200:])
    r = tool("accept", inv, "--node", configs["B"], "--keys", keys["nodeB"].dir,
             "--path-id", PATH_IDS["B"], "--as-name", "A", "--out", acc,
             "--enrol-author", keys["alice"].principal, "--inbound-source", "127.0.0.2",
             "--connects-from", "127.0.0.1", "--feed", "--carry-budget", "1000000", "3")
    check("accept", r.returncode == 0 and acc.exists(), r.stdout.strip()[-300:])
    r = tool("accept", inv, "--node", configs["B"], "--keys", keys["nodeB"].dir,
             "--path-id", PATH_IDS["B"], "--out", work / "again.eml")
    check("accept-refuses-replayed-invitation", r.returncode == 1, r.stdout.strip()[-200:])
    r = tool("confirm", acc, "--node", configs["A"], "--keys", keys["nodeA"].dir,
             "--invitation", inv, "--inbound-source", "127.0.0.1")
    check("confirm", r.returncode == 0, r.stdout.strip()[-300:])
    r = tool("confirm", acc, "--node", configs["A"], "--keys", keys["nodeA"].dir,
             "--invitation", inv)
    check("confirm-is-once", r.returncode == 1, r.stdout.strip()[-200:])

    # ---------------------------------------------------------- articles, pull
    x1 = signed_article(keys["alice"], "fn.test", "<x1@spike.test>", "alice before",
                        "signed by alice", work)
    y = [signed_article(keys["carol"], "fn.test", "<y{}@spike.test>".format(i),
                        "carol {}".format(i), "carried by B", work) for i in (1, 2)]
    w0 = signed_article(keys["nodeA"], "fn.test", "<w0@spike.test>", "node key before",
                        "old node key", work)
    for msgid, art in (("<x1@spike.test>", x1), ("<w0@spike.test>", w0),
                       ("<y1@spike.test>", y[0]), ("<y2@spike.test>", y[1])):
        check("post-A " + msgid, post(PORTS["A"], art).startswith("240"), msgid)
    r = pull(work, PORTS["A"], PORTS["B"], "127.0.0.2", "fn.*", "pull-B-from-A.json")
    check("pull-B-from-A", r.returncode == 0 and "accepted pull" in r.stdout,
          r.stdout.strip()[-400:])
    vx1 = verdict(PORTS["B"], "<x1@spike.test>")
    check("B-verifies-introduced-author", vx1.startswith("verified " + keys["alice"].principal),
          vx1)
    vy1 = verdict(PORTS["B"], "<y1@spike.test>")
    check("B-carries-unenrolled-author", vy1.startswith("carried " + keys["carol"].principal),
          vy1)
    vw0 = verdict(PORTS["B"], "<w0@spike.test>")
    check("B-verifies-inviter-node-key", vw0.startswith("verified " + keys["nodeA"].principal),
          vw0)

    # ---------------------------------------------------------- succession
    for old, new, stem in (("nodeA", "nodeA2", "succ-node"), ("carol", "carol2", "succ-carol")):
        out = work / (stem + ".eml")
        tool("succession", "--old", keys[old].dir, "--new", keys[new].dir, "--out", out)
        msgid = fp.body_fields(out.read_bytes()).get("Message-ID") or \
            [l for l in out.read_text(errors="replace").splitlines()
             if l.startswith("Message-ID:")][-1].split(": ", 1)[1]
        check("post-A " + stem, post(PORTS["A"], out.read_bytes()).startswith("240"), msgid)
    r = tool("keys-process", "--node", configs["A"])
    check("A-acts-on-successions", r.stdout.count("accepted key-statement") == 2,
          r.stdout.strip()[-400:])
    pull(work, PORTS["A"], PORTS["B"], "127.0.0.2", "fn.*", "pull-B-from-A.json")
    r = tool("keys-process", "--node", configs["B"])
    check("B-enrols-node-successor", "enrol-successor" in r.stdout
          and "accepted key-statement" in r.stdout, r.stdout.strip()[-500:])
    check("B-declines-carried-succession", "carrying is not authority" in r.stdout,
          r.stdout.strip()[-500:])
    z1 = signed_article(keys["nodeA2"], "fn.test", "<z1@spike.test>", "node key after",
                        "new node key", work)
    check("post-A z1 (successor key)", post(PORTS["A"], z1).startswith("240"), "")
    w1 = signed_article(keys["nodeA"], "fn.test", "<w1@spike.test>", "old key after",
                        "superseded", work)
    check("A-refuses-superseded-key-post", not post(PORTS["A"], w1).startswith("240"), "")
    pull(work, PORTS["A"], PORTS["B"], "127.0.0.2", "fn.*", "pull-B-from-A.json")
    # Budget: y1, y2 and carol's succession statement used B's count of 3 for
    # the boundary to A; carol's next article is refused there by name.
    y3 = signed_article(keys["carol2"], "fn.test", "<y3@spike.test>", "carol 3",
                        "over budget at B", work)
    check("post-A y3 (carol successor key)", post(PORTS["A"], y3).startswith("240"), "")
    pull(work, PORTS["A"], PORTS["B"], "127.0.0.2", "fn.*", "pull-B-from-A.json")
    vy3 = verdict(PORTS["B"], "<y3@spike.test>")
    check("B-budget-refuses-fourth-carried", not vy3.startswith("carried"), vy3)
    check("B-budget-refusal-named",
          any("carried-count-exhausted" in l for l in log_lines(work, "B", "y3@spike.test")),
          log_lines(work, "B", "y3@spike.test")[-1:])
    vz1 = verdict(PORTS["B"], "<z1@spike.test>")
    check("B-verifies-successor-key", vz1.startswith("verified " + keys["nodeA"].principal), vz1)
    vw0b = verdict(PORTS["B"], "<w0@spike.test>")
    check("B-old-key-verdict-unchanged", vw0b == vw0, "{} / {}".format(vw0, vw0b))

    # ---------------------------------------------------------- revocation
    # R1 is signed by alice BEFORE her revocation and delivered after it.
    r1 = signed_article(keys["alice"], "fn.test", "<r1@spike.test>", "delayed",
                        "signed before the revocation, delivered after", work)
    rev = work / "revocation-alice.eml"
    tool("revocation", "--keys", keys["alice"].dir, "--out", rev)
    check("post-A revocation", post(PORTS["A"], rev.read_bytes()).startswith("240"), "")
    r = tool("keys-process", "--node", configs["A"])
    check("A-revokes", "accepted revoke" in r.stdout or "accepted key-statement" in r.stdout,
          r.stdout.strip()[-300:])
    pull(work, PORTS["A"], PORTS["B"], "127.0.0.2", "fn.*", "pull-B-from-A.json")
    r = tool("keys-process", "--node", configs["B"])
    check("B-revokes", "revoke" in r.stdout and "accepted key-statement" in r.stdout,
          r.stdout.strip()[-300:])
    served = post(PORTS["A"], r1)
    check("A-served-post-after-revocation-refused", not served.startswith("240"), served)
    t = ihave(PORTS["A"], "127.0.0.1", "<r1@spike.test>", relayed(r1, PATH_IDS["B"]))   # as peer B
    check("A-transit-after-revocation-stored", t.startswith("235"), t)
    vr1 = verdict(PORTS["A"], "<r1@spike.test>")
    check("A-verdict-revoked", vr1.startswith("revoked " + keys["alice"].principal), vr1)
    t = ihave(PORTS["B"], "127.0.0.2", "<r1@spike.test>", relayed(r1, PATH_IDS["A"]))   # as peer A
    vr1b = verdict(PORTS["B"], "<r1@spike.test>")
    check("B-verdict-revoked", vr1b.startswith("revoked " + keys["alice"].principal),
          "{} {}".format(t, vr1b))
    vx1a = verdict(PORTS["A"], "<x1@spike.test>")
    check("A-pre-revocation-verdict-stays-verified",
          vx1a.startswith("verified " + keys["alice"].principal), vx1a)
    check("B-pre-revocation-verdict-stays-verified",
          verdict(PORTS["B"], "<x1@spike.test>") == vx1, vx1)

    # ---------------------------------------------------------- refusal classes
    dave = fp.keygen(work / "keys" / "dave")
    d1 = signed_article(dave, "fn.test", "<d1@spike.test>", "stranger", "no binding", work)
    t = ihave(PORTS["A"], "127.0.0.1", "<d1@spike.test>", relayed(d1, PATH_IDS["B"]))
    check("A-refuses-no-local-binding", not t.startswith("235")
          and any("no-local-binding" in l for l in log_lines(work, "A", "d1@spike.test")),
          "{} {}".format(t, log_lines(work, "A", "d1@spike.test")[-1:]))
    z2 = signed_article(keys["nodeA2"], "fn.test", "<z2@spike.test>", "tampered", "orig", work)
    z2 = z2.replace(b"orig", b"ORIG")
    t = ihave(PORTS["A"], "127.0.0.1", "<z2@spike.test>", relayed(z2, PATH_IDS["B"]))
    check("A-refuses-signature-failed", not t.startswith("235")
          and any("signature-failed" in l for l in log_lines(work, "A", "z2@spike.test")),
          "{} {}".format(t, log_lines(work, "A", "z2@spike.test")[-1:]))

    # ---------------------------------------------------------- fn_verify
    keyring = work / "keyring.json"
    entries = []
    for who in ("alice",):
        r = run(sys.executable, ROOT / "tools/fn_verify.py", "keyring-entry",
                keys[who].principal_path, keys[who].ed_public_path, keys[who].ml_public_path)
        if r.returncode == 0:
            try:
                entries.append(json.loads(r.stdout.strip().splitlines()[-1]))
            except (ValueError, IndexError):
                pass
    keyring.write_text(json.dumps({"format": "fn-verify-keyring-v1", "principals": entries}))
    for msgid, want in (("<x1@spike.test>", 0), ("<r1@spike.test>", 1)):
        r = run(sys.executable, ROOT / "tools/fn_verify.py", "--node",
                "127.0.0.1:{}".format(PORTS["A"]), "--plain", "--keyring", keyring, msgid)
        check("fn_verify " + msgid, r.returncode == want, r.stdout.strip()[-300:])

    # ---------------------------------------------------------- INN, a stranger
    if args.no_inn:
        return
    try:
        inn_lab(work, args, configs, keys)
    except OSError as error:
        check("inn-section-completed", False, repr(error))


def inn_lab(work, args, configs, keys):
    prefix = inn_setup(work, args.inn_src)
    check("inn-up", inn_start(prefix), prefix)
    # A's peer record for INN: A pulls it (inbound from 127.0.0.3) and feeds it.
    stop("A")
    r = img("operator", configs["A"], "peer", "add", "inn", PATH_IDS["inn"], "127.0.0.1",
            PORTS["innd"], "fn.*,control,control.*", "fn.*", "source-address", "127.0.0.3",
            "false")
    check("A-peer-add-inn", r.returncode == 0, r.stdout[-200:])
    start_node(work, "A")
    j1 = unsigned("fn.test", "<j1@inn.spike.test>", "from INN", "an INN reader's post",
                  "Date: {}\r\n".format(fp.rfc5322_date()))
    check("inn-post-j1", post(PORTS["nnrpd"], j1).startswith("240"), "")
    time.sleep(2)
    r = pull(work, PORTS["nnrpd"], PORTS["A"], "127.0.0.3", "fn.*,control.*", "pull-A-from-INN.json")
    check("A-pulls-inn-newnews", "<j1@inn.spike.test>" in r.stdout, r.stdout.strip()[-300:])
    cancel = unsigned("fn.test", "<cancel-j1@inn.spike.test>", "cmsg cancel <j1@inn.spike.test>",
                      "cancel", "Control: cancel <j1@inn.spike.test>\r\nDate: {}\r\n".format(
                          fp.rfc5322_date()))
    check("inn-post-cancel", post(PORTS["nnrpd"], cancel).startswith("240"), "")
    newgroup = unsigned("fn.test", "<newgroup@inn.spike.test>", "cmsg newgroup fn.innnew",
                        "newgroup", "Control: newgroup fn.innnew\r\nApproved: lab@inn.spike.test\r\n"
                        "Date: {}\r\n".format(fp.rfc5322_date()))
    check("inn-post-newgroup", post(PORTS["nnrpd"], newgroup).startswith("240"), "")
    time.sleep(2)
    r = pull(work, PORTS["nnrpd"], PORTS["A"], "127.0.0.3", "fn.*,control.*", "pull-A-from-INN.json")
    check("A-pulls-inn-control", "<cancel-j1@inn.spike.test>" in r.stdout, r.stdout.strip()[-400:])
    status, octets = fetch(PORTS["A"], "<j1@inn.spike.test>")
    check("A-cancel-filed-not-executed", octets is not None, status)
    with fp.Nntp("127.0.0.1", PORTS["A"]) as n:
        g = n.command("GROUP control.cancel")
    check("A-control-cancel-group-holds-it", g.startswith("211") and g.split()[1] != "0", g)
    status, octets = fetch(PORTS["A"], "<newgroup@inn.spike.test>")
    with fp.Nntp("127.0.0.1", PORTS["A"]) as n:
        g2 = n.command("GROUP fn.innnew")
    check("A-newgroup-filed-not-executed", octets is not None and not g2.startswith("211"),
          "{} / {}".format(status, g2))
    # A feeds INN: alice's signed X1 reaches nnrpd with its carrier intact.
    t = ihave(PORTS["innd"], "127.0.0.1", "<x1@spike.test>", fetch(PORTS["A"], "<x1@spike.test>")[1])
    status, octets = fetch(PORTS["nnrpd"], "<x1@spike.test>")
    check("inn-holds-signed-article-with-carrier",
          octets is not None and b"FN-Authorship:" in octets, "{} {}".format(t, status))
    z3 = signed_article(keys["nodeA2"], "fn.test", "<z3@spike.test>", "after inn peering",
                        "fed by A's owner feed", work)
    check("post-A z3", post(PORTS["A"], z3).startswith("240"), "")
    for _ in range(20):
        status, octets = fetch(PORTS["nnrpd"], "<z3@spike.test>")
        if octets is not None:
            break
        time.sleep(3)
    check("A-owner-feed-reaches-inn", octets is not None, status)


if __name__ == "__main__":
    main()
