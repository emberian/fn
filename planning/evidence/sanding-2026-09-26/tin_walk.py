#!/usr/bin/env python3
"""tin 2.6.2 (NNTPS) against a scratch node's implicit-TLS listener (SCN-092).

    python3 tin_walk.py IMAGE WORKDIR PLAIN_PORT TLS_PORT TIN

On hbox, loopback only.  Builds a scratch node (certificate with SAN
localhost/127.0.0.1, [auth] required and protected_only, tls_port), enrols
`guest` with posting, starts the owner as a systemd --user unit, seeds one
root article over TLS, then drives tin in tmux: log in, read the root,
follow up, post a new article, cancel it.  Every screen is captured to
WORKDIR/screens/NN.txt; the owner's log is WORKDIR/owner.log; after tin
quits a Python TLS client reads the group back (OVER, HDR References) into
WORKDIR/readback.txt.  Never touches /tank/fn/node.
"""
import os
import pathlib
import socket
import ssl
import subprocess
import sys
import time

image, work, plain, tport, tin = sys.argv[1], pathlib.Path(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
unit = "sanding-tin-owner"
password = "tin-walk-" + os.urandom(6).hex()
work.mkdir(parents=True, exist_ok=True)
node = work / "node"
node.mkdir(exist_ok=True)
screens = work / "screens"
screens.mkdir(exist_ok=True)
home = work / "tinhome"
(home / ".tin").mkdir(parents=True, exist_ok=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
log = open(work / "walk.log", "a", buffering=1)


def say(text):
    log.write(time.strftime("%H:%M:%S ") + text + "\n")


def run(argv, stdin=None, check=True):
    r = subprocess.run(argv, input=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       env=env, timeout=300)
    say("$ {} -> {}\n{}{}".format(" ".join(map(str, argv)), r.returncode,
                                  r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace")))
    if check and r.returncode != 0:
        raise SystemExit("step failed: {}".format(argv))
    return r


cert, key = node / "cert.pem", node / "key.pem"
if not cert.exists():
    run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key), "-out", str(cert),
         "-sha256", "-days", "2", "-nodes", "-subj", "/CN=localhost",
         "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1"])
config = node / "fn.toml"
config.write_text("\n".join([
    "[store]", 'path = "{}"'.format(node / "store"), "",
    "[listener]", 'host = "127.0.0.1"', "port = {}".format(plain),
    'tls_cert = "{}"'.format(cert), 'tls_key = "{}"'.format(key), "tls_port = {}".format(tport), "",
    "[auth]", "required = true", "protected_only = true", "",
    "[log]", 'path = "{}"'.format(work / "owner.log"), ""]), encoding="ascii")
op = [image, "--fn", "operator", str(config)]
if not (node / "store").exists():
    run(op + ["init", "fn.test", "fn.letters", "control.cancel"])
    run(["setsid", "-w"] + op + ["principal", "set-password", "guest", "--posting"],
        stdin=(password + "\n" + password + "\n").encode())
run(["systemctl", "--user", "stop", unit], check=False)
run(["systemctl", "--user", "reset-failed", unit], check=False)
run(["systemd-run", "--user", "--unit", unit, "-p", "MemoryMax=24G",
     "--setenv=ACL2_CUSTOMIZATION=NONE",
     "--setenv=LD_LIBRARY_PATH=" + env.get("LD_LIBRARY_PATH", ""),
     "sh", "-c", "exec {} > {} 2>&1".format(" ".join(op + ["run"]), work / "owner.stdout")])
for _ in range(240):
    text = (work / "owner.stdout").read_text() if (work / "owner.stdout").exists() else ""
    if "LISTENING-TLS" in text:
        break
    time.sleep(0.5)
say("owner: " + (work / "owner.stdout").read_text())

context = ssl.create_default_context(cafile=str(cert))


class Tls:
    def __init__(self):
        self.s = context.wrap_socket(socket.create_connection(("127.0.0.1", tport), timeout=20),
                                     server_hostname="localhost")
        self.buf = b""
        self.transcript = []
        self.line()

    def line(self):
        while b"\r\n" not in self.buf:
            piece = self.s.recv(65536)
            if not piece:
                raise EOFError
            self.buf += piece
        line, self.buf = self.buf.split(b"\r\n", 1)
        self.transcript.append("S: " + line.decode(errors="replace"))
        return line.decode(errors="replace")

    def ask(self, text, secret=False):
        self.transcript.append("C: " + ("AUTHINFO PASS [password]" if secret else text))
        self.s.sendall(text.encode() + b"\r\n")
        return self.line()

    def block(self):
        out = []
        while True:
            line = self.line()
            if line == ".":
                return out
            out.append(line)


seed = Tls()
seed.ask("AUTHINFO USER guest")
seed.ask("AUTHINFO PASS " + password, secret=True)
if seed.ask("POST").startswith("340"):
    seed.s.sendall(("From: ember <ember@fn.example.invalid>\r\nNewsgroups: fn.test\r\n"
                    "Subject: tin over TLS, the root\r\nMessage-ID: <tin-tls-root@fn.example.invalid>\r\n"
                    "\r\nA root for tin to follow up.\r\n.\r\n").encode())
    seed.line()
seed.ask("QUIT")
(work / "seed.txt").write_text("\n".join(seed.transcript) + "\n")

# tin's home: the CA, the login, the one group, an editor that appends a body.
(home / ".newsauth").write_text("localhost {} guest\n".format(password))
os.chmod(home / ".newsauth", 0o600)
(home / ".newsrc").write_text("fn.test:\n")
(home / ".tin" / "tinrc").write_text("\n".join([
    "tls_ca_cert_file={}".format(cert), "show_only_unread_arts=OFF", "confirm_choice=0",
    "auto_reconnect=OFF", "thread_articles=0", "use_mouse=OFF",
    ""]))
(home / "editor.sh").write_text('#!/bin/sh\nsleep 1\nfor a; do f=$a; done\ncat "$HOME/next-body" >> "$f"\n')
os.chmod(home / "editor.sh", 0o755)

session = "sanding-tin"
subprocess.run(["tmux", "kill-session", "-t", session], stderr=subprocess.DEVNULL)
count = [0]


def shot(label):
    count[0] += 1
    text = subprocess.run(["tmux", "capture-pane", "-p", "-t", session], stdout=subprocess.PIPE).stdout.decode()
    (screens / "{:02d}-{}.txt".format(count[0], label)).write_text(text)
    return text


def keys(*k, wait=1.5):
    subprocess.run(["tmux", "send-keys", "-t", session] + list(k))
    time.sleep(wait)


def until(needle, label, seconds=30):
    end = time.time() + seconds
    while time.time() < end:
        text = subprocess.run(["tmux", "capture-pane", "-p", "-t", session], stdout=subprocess.PIPE).stdout.decode()
        if needle in text:
            return shot(label)
        time.sleep(0.5)
    shot(label + "-TIMEOUT")
    say("timeout waiting for {!r} at {}".format(needle, label))
    return None


tin_cmd = ("env HOME={h} NNTPSERVER=localhost DOMAINNAME=fn.example.invalid TIN_HOMEDIR={h} EDITOR={e} VISUAL={e} "
           "{tin} -r -T -A -q -p {p} -g localhost"
           .format(h=home, e=home / "editor.sh", tin=tin, p=tport))
subprocess.run(["tmux", "new-session", "-d", "-s", session, "-x", "132", "-y", "40", tin_cmd])
until("fn.test", "groups", 60)
keys("Enter")
until("tin over TLS", "group-index")
keys("Enter")
until("A root for tin", "read-root")
(home / "next-body").write_text("A follow-up from tin over TLS.\nIt logged in, read the root and replied.\nThree lines of its own.\n")
keys("f")
until("p=post", "followup-prompt", 40)
keys("p", wait=0.2)
for i in range(8):
    shot("followup-after-p")
    time.sleep(0.4)
keys("q")
time.sleep(1)
shot("back-to-index")
(home / "next-body").write_text("A new article from tin over TLS.\n")
keys("w")
until("ubject", "post-subject")
keys("tin over TLS, a new post", "Enter")
until("p=post", "post-prompt", 40)
keys("p", wait=0.2)
for i in range(8):
    shot("post-after-p")
    time.sleep(0.4)
keys("q", wait=1)
text = shot("group-after")
if "Group Selection" in text:
    keys("Enter", wait=2)
    shot("group-index-again")
# Cancel tin's own new post: the last thread, read it, D, delete.
keys("Home", wait=1)
keys("/", wait=1)
keys("a new post", "Enter", wait=2)
shot("own-post-selected")
keys("D", wait=2)
text = shot("cancel-prompt")
keys("d", wait=2)
text = shot("cancel-after-d")
if "d=delete (cancel)" in text:
    keys("d", wait=0.2)
for i in range(6):
    shot("cancel-after")
    time.sleep(0.4)
keys("q", wait=1)
subprocess.run(["tmux", "send-keys", "-t", session, "q"])
time.sleep(1)
subprocess.run(["tmux", "send-keys", "-t", session, "q"])
time.sleep(1)
shot("quit")
subprocess.run(["tmux", "kill-session", "-t", session], stderr=subprocess.DEVNULL)

rb = Tls()
rb.ask("AUTHINFO USER guest")
rb.ask("AUTHINFO PASS " + password, secret=True)
rb.ask("GROUP fn.test")
if rb.ask("OVER 1-20").startswith("224"):
    rb.block()
if rb.ask("HDR References 1-20").startswith("225"):
    rb.block()
if rb.ask("GROUP control.cancel").startswith("211"):
    if rb.ask("OVER 1-20").startswith("224"):
        rb.block()
rb.ask("QUIT")
(work / "readback.txt").write_text("\n".join(rb.transcript) + "\n")
say("done")
