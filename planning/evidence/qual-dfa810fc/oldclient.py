#!/usr/bin/env python3
"""qual-dfa810fc item 5 (PKT-372): the b6759850 clients against a dfa810fc node.
A scratch node on the production image (fresh store, fn.test, loopback, plain).
For CONFLICT (a changed article under a stored Message-ID) and UNKNOWN-GROUP (a
post to a group the node lacks), each of: tools/fn_client.py at b6759850 (the
gate's copy) and at dfa810fc over NNTP; `operator CONFIG post` through the
control socket with the b6759850 image and the dfa810fc image.  Prints what each
says and its exit code.  Nothing here decides; the node and each client do."""
import os, signal, socket, subprocess, sys, time
from pathlib import Path

NEWIMG = Path(sys.argv[1]); OLDIMG = Path(sys.argv[2]); OLDTREE = Path(sys.argv[3]); NEWTREE = Path(sys.argv[4]); W = Path(sys.argv[5])
W.mkdir(parents=True, exist_ok=False)
ENV = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
for k in [k for k in ENV if k.startswith("FN_NATIVE_")]:
    ENV.pop(k)


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0)); return s.getsockname()[1]


def run(label, argv, stdin=None):
    r = subprocess.run([str(a) for a in argv], env=ENV, input=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").strip()
    print("CASE %-58s exit=%d | %s" % (label, r.returncode, " / ".join(out.splitlines()[-3:])[:300]), flush=True)
    return r.returncode


port = free_port()
cfg = W / "fn.toml"
cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n[control]\npath = "%s"\n' % (W / "store", port, W / "control.sock"))
run("init fn.test", [NEWIMG, "--fn", "operator", cfg, "init", "fn.test"])
owner = subprocess.Popen([str(NEWIMG), "--fn", "operator", str(cfg), "run"], env=ENV, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
while not owner.stdout.readline().startswith(b"LISTENING"):
    pass
try:
    node = "127.0.0.1:%d" % port
    mid = "<oldclient-conflict@example.invalid>"
    body = W / "body.txt"; body.write_text("the first body\n")
    run("new fn_client post (the original)", [sys.executable, NEWTREE / "tools/fn_client.py", "post", "fn.test", "--subject", "s", "--from", "q <q@example.invalid>",
                                              "--message-id", mid, "--body-file", body, "--node", node, "--plain", "--state", W / "st.json"])
    body2 = W / "body2.txt"; body2.write_text("a changed body\n")
    for label, tree in (("b6759850", OLDTREE), ("dfa810fc", NEWTREE)):
        run("%s fn_client CONFLICT (changed body, same Message-ID)" % label,
            [sys.executable, tree / "tools/fn_client.py", "post", "fn.test", "--subject", "s", "--from", "q <q@example.invalid>",
             "--message-id", mid, "--body-file", body2, "--node", node, "--plain", "--state", W / "st.json"])
        run("%s fn_client UNKNOWN-GROUP (no.such.group)" % label,
            [sys.executable, tree / "tools/fn_client.py", "post", "no.such.group", "--subject", "s", "--from", "q <q@example.invalid>",
             "--message-id", "<oldclient-ug-%s@example.invalid>" % label, "--body-file", body, "--node", node, "--plain", "--state", W / "st.json"])
    art = W / "orig.eml"
    art.write_bytes(b"From: q <q@example.invalid>\r\nNewsgroups: fn.test\r\nSubject: op\r\nMessage-ID: <oldclient-op@example.invalid>\r\n\r\nexact payload\r\n")
    chg = W / "changed.eml"
    chg.write_bytes(art.read_bytes().replace(b"exact payload", b"changed payload"))
    ug = W / "ug.eml"
    ug.write_bytes(b"From: q <q@example.invalid>\r\nNewsgroups: no.such.group\r\nSubject: op\r\nMessage-ID: <oldclient-opug@example.invalid>\r\n\r\nx\r\n")
    run("dfa810fc operator post (the original)", [NEWIMG, "--fn", "operator", cfg, "post", "--message-id", "<oldclient-op@example.invalid>", "--payload", art, "--group", "fn.test"])
    for label, img in (("b6759850", OLDIMG), ("dfa810fc", NEWIMG)):
        run("%s image operator post CONFLICT" % label, [img, "--fn", "operator", cfg, "post", "--message-id", "<oldclient-op@example.invalid>", "--payload", chg, "--group", "fn.test"])
        run("%s image operator post UNKNOWN-GROUP" % label, [img, "--fn", "operator", cfg, "post", "--message-id", "<oldclient-opug@example.invalid>", "--payload", ug, "--group", "no.such.group"])
    # hybrid-author: the author-refusal words (UNKNOWN-GROUP) and CONFLICT through the control socket
    OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
    k = W / "keys"; k.mkdir()
    (k / "p.bin").write_bytes(bytes([85]) * 32)
    (k / "ed.pub").write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
    (k / "ed.sec").write_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                                             "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
    subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(k / "ml.pem")], check=True, env=ENV)
    subprocess.run([OPENSSL, "pkey", "-in", str(k / "ml.pem"), "-pubout", "-out", str(k / "ml.pub")], check=True, env=ENV)
    control = W / "control.sock"
    run("dfa810fc hybrid-enroll P generation 1", [NEWIMG, "--fn", "hybrid-enroll", control, "1", k / "p.bin", k / "ed.pub", k / "ml.pub"])

    def signed(stem, group, payload):
        src = W / (stem + ".eml")
        src.write_bytes(("From: q <q@example.invalid>\r\nNewsgroups: %s\r\nSubject: ha\r\nDate: Sat, 26 Sep 2026 09:00:00 +0000\r\nMessage-ID: <oldclient-ha-%s@example.invalid>\r\n\r\n%s\r\n"
                         % (group, stem.split("-")[0], payload)).encode())
        r = subprocess.run([str(NEWIMG), "--fn", "hybrid-sign", str(k / "p.bin"), str(k / "ed.pub"), str(k / "ed.sec"), str(k / "ml.pub"), str(k / "ml.pem"), str(src)],
                           env=ENV, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
        parts = dict(l.split() for l in r.stdout.decode().splitlines() if len(l.split()) == 2)
        (W / (stem + ".ed")).write_bytes(bytes.fromhex(parts["ed25519"]))
        (W / (stem + ".ml")).write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        return [src, W / (stem + ".ed"), W / (stem + ".ml"), k / "ml.pub"]
    orig = signed("c-orig", "fn.test", "exact")
    chg = signed("c-changed", "fn.test", "changed")
    ugs = signed("ug-x", "no.such.group", "x")
    run("dfa810fc hybrid-author (the original)", [NEWIMG, "--fn", "hybrid-author", control, "1", *orig])
    for label, img in (("b6759850", OLDIMG), ("dfa810fc", NEWIMG)):
        run("%s image hybrid-author CONFLICT" % label, [img, "--fn", "hybrid-author", control, "1", *chg])
        run("%s image hybrid-author UNKNOWN-GROUP" % label, [img, "--fn", "hybrid-author", control, "1", *ugs])
finally:
    owner.send_signal(signal.SIGTERM)
    owner.wait(60)
    print("OWNER exit", owner.returncode)
doc = (NEWTREE / "docs/agents.md").read_text()
i = doc.find("Upgrade the client with the node")
print("QUOTE-AGENTS " + " ".join(doc[i:i + 420].split()))
