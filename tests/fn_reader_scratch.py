#!/usr/bin/env python3
"""A scratch node and the friends' reader in front of it (SCN-173, WEB-003).

Run on the box that holds a native image; it stays in the foreground until
SIGTERM (run it under `systemd-run --user`), stopping both children then.

    python3 tests/fn_reader_scratch.py --image .../build/fn-host --dir DIR --web-port 8943

The node: an implicit-TLS listener plus a STARTTLS listener on loopback,
`[auth] protected_only`, groups fn.friends (described), fn.private.club,
fn.mod (moderated by alice; queue fn.mod.moderation) and control.cancel.
Three invitation accounts are redeemed over TLS exactly as a friend would
(`account invite`, `XREDEEM CODE LOGIN`, `XREDEEM PASS`): alice (moderates
fn.mod), bob (`account access bob --read 'fn.*,!fn.private.*' --post
'fn.*,!fn.private.*'`), carol (no rule). Their passwords go to DIR/logins
(mode 0600) for the browser driver. alice seeds one post in fn.friends and
one in fn.private.club; carol posts to fn.mod, which the node holds in the
queue. Then tools/fn_reader.py serves HTTPS on 127.0.0.1:WEB_PORT, verifying
the node's certificate. Every decision is the node's; this file only sets
up and calls, and writes DIR/ready when both are listening.
"""
import argparse
import json
import os
from pathlib import Path
import re
import secrets
import select
import signal
import socket
import ssl
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent.parent


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--image", required=True)
    parser.add_argument("--dir", required=True)
    parser.add_argument("--web-port", type=int, required=True)
    parser.add_argument("--openssl", default="openssl")
    args = parser.parse_args()
    root = Path(args.dir).resolve()
    root.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    env.pop("ACL2_SYSTEM_BOOKS", None)
    log = open(root / "scratch.log", "a", buffering=1)

    def say(*words):
        log.write(" ".join(str(w) for w in words) + "\n")

    def cert(name, cn):
        subprocess.run([args.openssl, "req", "-x509", "-newkey", "rsa:2048", "-nodes",
                        "-sha256", "-days", "30", "-subj", "/CN=" + cn, "-addext",
                        "subjectAltName=IP:127.0.0.1,DNS:localhost",
                        "-keyout", str(root / (name + "-key.pem")),
                        "-out", str(root / (name + "-cert.pem"))],
                       check=True, capture_output=True)
        return root / (name + "-cert.pem"), root / (name + "-key.pem")

    node_cert, node_key = cert("node", "localhost")
    web_cert, web_key = cert("web", "localhost")
    port, tls_port = free_port(), free_port()
    config = root / "fn.toml"
    config.write_text(
        '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
        'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
        '[auth]\nprotected_only = true\n'.format(
            root / "store", port, tls_port, node_cert, node_key, root / "control.sock"),
        encoding="ascii")

    def operator(*words, check=True):
        result = subprocess.run([args.image, "--fn", "operator", str(config), *words],
                                cwd=ROOT, env=env, capture_output=True, timeout=300)
        say("operator", " ".join(words[:3]), "->", result.returncode,
            (result.stdout + result.stderr).decode("utf-8", "replace")[-200:].replace("\n", " | "))
        if check and result.returncode != 0:
            raise SystemExit("operator %s failed" % " ".join(words))
        return result.stdout.decode("utf-8", "replace")

    operator("init", "fn.friends")
    for group in ("fn.private.club", "fn.mod", "fn.mod.moderation", "control.cancel"):
        operator("group", "create", group)
    operator("group", "moderate", "fn.mod", "--moderators", "alice")
    owner = subprocess.Popen([args.image, "--fn", "operator", str(config), "run"],
                             cwd=ROOT, env=env, stdout=subprocess.PIPE,
                             stderr=open(root / "owner.err", "ab"), bufsize=0)
    seen = 0
    while seen < 2:
        if not select.select([owner.stdout], [], [], 300)[0]:
            raise SystemExit("owner did not start")
        line = owner.stdout.readline()
        say("owner:", line.decode("utf-8", "replace").rstrip())
        if not line:
            raise SystemExit("owner exited")
        if line.startswith(b"LISTENING"):
            seen += 1
    def drain():
        for raw in owner.stdout:
            say("owner:", raw.decode("utf-8", "replace").rstrip())
    threading.Thread(target=drain, daemon=True).start()
    operator("group", "describe", "fn.friends", "Say hello, share news, chat about anything.")
    operator("group", "describe", "fn.private.club", "The club's own room.")
    operator("group", "describe", "fn.mod", "Announcements. A moderator checks each post.")

    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.load_verify_locations(str(node_cert))

    def tls():
        raw = socket.create_connection(("127.0.0.1", tls_port), timeout=60)
        stream = context.wrap_socket(raw, server_hostname="localhost").makefile("rwb", buffering=0)
        stream.readline()
        return stream

    def line(stream, command):
        stream.write(command.encode("utf-8") + b"\r\n")
        return stream.readline().decode("utf-8", "replace").rstrip("\r\n")

    logins = {}
    for user in ("alice", "bob", "carol"):
        code = re.findall(r"^[0-9a-f]{32}$", operator("account", "invite", "--expires", "3600"),
                          re.M)[0]
        password = "pw-%s-%s" % (user, secrets.token_hex(6))
        stream = tls()
        first = line(stream, "XREDEEM %s %s" % (code, user))
        second = line(stream, "XREDEEM PASS " + password)
        say("redeem", user, first, second)
        if not second.startswith("281"):
            raise SystemExit("redeem failed for " + user)
        logins[user] = password
    operator("account", "access", "bob", "--read", "fn.*,!fn.private.*",
             "--post", "fn.*,!fn.private.*")
    descriptor = os.open(root / "logins", os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "w") as handle:
        json.dump(logins, handle)

    def post(user, groups, subject, body):
        stream = tls()
        assert line(stream, "AUTHINFO USER " + user).startswith("381")
        assert line(stream, "AUTHINFO PASS " + logins[user]).startswith("281")
        assert line(stream, "POST").startswith("340")
        msgid = "<seed.%s@friends.example>" % secrets.token_hex(6)
        article = ["From: %s <%s@friends.example>" % (user.title(), user),
                   "Newsgroups: " + groups, "Subject: " + subject, "Message-ID: " + msgid,
                   ""] + body.split("\n")
        stream.write(("".join(("." + r if r.startswith(".") else r) + "\r\n" for r in article)
                      + ".\r\n").encode("utf-8"))
        answer = stream.readline().decode().rstrip()
        say("seed", user, groups, answer)
        return answer

    post("alice", "fn.friends", "Welcome, everyone!",
         "Hi all,\n\nThis is our little news server. Say hello below!\n\n-- Alice")
    post("alice", "fn.private.club", "Club night on Friday",
         "Only club members can read this group.")
    post("carol", "fn.mod", "Garden party next Sunday",
         "Everyone welcome. Bring a chair.")

    reader = subprocess.Popen(
        [sys.executable, str(ROOT / "tools" / "fn_reader.py"), "--node",
         "127.0.0.1:%d" % port, "--tls-cert", str(node_cert), "--state",
         str(root / "reader-state"), "--listen", "127.0.0.1:%d" % args.web_port,
         "--https-cert", str(web_cert), "--https-key", str(web_key),
         "--site", "Friends' news", "--mail-domain", "friends.example"],
        stdout=open(root / "reader.log", "ab"), stderr=subprocess.STDOUT)
    for _ in range(100):
        try:
            socket.create_connection(("127.0.0.1", args.web_port), timeout=1).close()
            break
        except OSError:
            time.sleep(0.1)
    (root / "ready").write_text(json.dumps({"web_port": args.web_port, "nntp_port": port,
                                            "tls_port": tls_port}))
    say("ready")

    def stop(*_):
        for child in (reader, owner):
            if child.poll() is None:
                child.send_signal(signal.SIGTERM)
        for child in (reader, owner):
            try:
                child.wait(timeout=60)
            except subprocess.TimeoutExpired:
                child.kill()
        sys.exit(0)
    signal.signal(signal.SIGTERM, stop)
    while True:
        if owner.poll() is not None or reader.poll() is not None:
            say("a child exited", owner.poll(), reader.poll())
            stop()
        time.sleep(2)


if __name__ == "__main__":
    main()
