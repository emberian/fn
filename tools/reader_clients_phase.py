#!/usr/bin/env python3
"""The v0 matrix's pan and Thunderbird client phase, on the execution host.

    python3 tools/reader_clients_phase.py --image IMAGE --work DIR
        [--group G] [--thunderbird BIN] [--openssl-prefix P]

Test tool (reader-clients lane).  It stands up one scratch owner from the
packaged image (`packaging/fn-native operator CONFIG ...`, FN_NATIVE_HOST =
IMAGE) whose only listeners are loopback: a clear port and an implicit-TLS
port whose certificate a scratch CA issued for IP 127.0.0.1, with
`[auth] required = true` and `protected_only = true` (AUTHINFO and XREDEEM
only over TLS), and `init GROUP control.cancel` so a cancel is filed, as
docs/human-web-client.md sets up the node for tin.  Then, for each client:

  1. `account invite --expires 3600` prints one code;
  2. the preliminary step (this file, stdlib ssl verifying the scratch CA)
     sends `XREDEEM CODE LOGIN` and `XREDEEM PASS PASSWORD` over TLS, and on
     a new connection `AUTHINFO USER/PASS` and one seed POST so the group
     has an article that is not the client's own;
  3. the client driver runs against the TLS port with that login
     (tools/thunderbird_drive.py; pan has no driver: see v0_matrix
     PAN_BLOCKER);
  4. a check over TLS as the same login: HEAD of the followup Thunderbird
     posted (its References as the node serves them), of the article it
     cancelled (still served: an unsigned cancel carries no authority, C2)
     and of the seed.

Every line of 2 and 4 is appended to the client's wire log in
tools/nntp_wire_log.py's format (XREDEEM PASS and AUTHINFO PASS arguments
redacted), and the client's own transcript between `--- action NAME`
markers.  The rows are read from those reply lines by
`v0_matrix.client_wire_outcomes`; nothing here decides a verdict.  Prints
one JSON object with the log paths, their SHA-256 and the per-client driver
results.  The owner is stopped (SIGTERM) before it returns.
"""
import argparse
import hashlib
import json
import os
import re
import secrets
import select
import signal
import socket
import ssl
import subprocess
import sys
import threading
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def run(command, **kwargs):
    return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          timeout=kwargs.pop("timeout", 300), check=False, **kwargs)


def scratch_ca(work: Path):
    """A CA and a server certificate for IP 127.0.0.1 and localhost."""
    ca_key, ca, key, csr, cert = (work / n for n in (
        "ca.key", "ca.pem", "node.key", "node.csr", "node.pem"))
    ext = work / "node.ext"
    ext.write_text("basicConstraints=CA:FALSE\nkeyUsage=digitalSignature,keyEncipherment\n"
                   "extendedKeyUsage=serverAuth\nsubjectAltName=IP:127.0.0.1,DNS:localhost\n")
    for command in (
            ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-keyout",
             str(ca_key), "-out", str(ca), "-days", "3", "-subj",
             "/CN=fn v0 matrix scratch CA", "-addext",
             "basicConstraints=critical,CA:TRUE", "-addext",
             "keyUsage=critical,keyCertSign,cRLSign"],
            ["openssl", "req", "-newkey", "rsa:2048", "-nodes", "-keyout", str(key),
             "-out", str(csr), "-subj", "/CN=127.0.0.1"],
            ["openssl", "x509", "-req", "-in", str(csr), "-CA", str(ca), "-CAkey",
             str(ca_key), "-CAcreateserial", "-out", str(cert), "-days", "2",
             "-extfile", str(ext)]):
        result = run(command)
        if result.returncode:
            raise RuntimeError("{} exited {}: {}".format(
                command[:2], result.returncode, result.stderr.decode()[-300:]))
    return ca, cert, key


class Wire:
    """Lines in tools/nntp_wire_log.py's format, appended to one log."""

    def __init__(self, path):
        self.out = open(path, "a", buffering=1, encoding="utf-8")
        self.conn = 100

    def mark(self, name):
        self.out.write("%.3f 0 --- action %s\n" % (time.time(), name))

    def line(self, conn, tag, text):
        if tag == "C":
            for secret in ("AUTHINFO PASS ", "XREDEEM PASS "):
                if text.upper().startswith(secret):
                    text = secret + "[password]"
            words = text.split(" ")
            if len(words) == 3 and words[0].upper() == "XREDEEM" and words[1] != "PASS":
                text = "XREDEEM [code] " + words[2]
        self.out.write("%.3f %d %s: %s\n" % (time.time(), conn, tag, text[:300]))


class Session:
    """One TLS session to the node, verifying the scratch CA, every line logged."""

    def __init__(self, wire, port, cafile):
        context = ssl.create_default_context(cafile=str(cafile))
        raw = socket.create_connection(("127.0.0.1", port), timeout=120)
        self.stream = context.wrap_socket(raw, server_hostname="127.0.0.1").makefile(
            "rwb", buffering=0)
        wire.conn += 1
        self.wire, self.conn = wire, wire.conn
        wire.out.write("%.3f %d --- connection (TLS, verified against the scratch CA)\n"
                       % (time.time(), self.conn))
        self.greeting = self.read()

    def read(self):
        text = self.stream.readline().decode("utf-8", "replace").rstrip("\r\n")
        self.wire.line(self.conn, "S", text)
        return text

    def send(self, text):
        self.wire.line(self.conn, "C", text)
        self.stream.write(text.encode("utf-8") + b"\r\n")

    def command(self, text):
        self.send(text)
        return self.read()

    def block(self):
        lines = []
        while True:
            one = self.read()
            if one == ".":
                return lines
            lines.append(one)

    def close(self):
        try:
            self.command("QUIT")
        except (OSError, ssl.SSLError):
            pass
        self.stream.close()


class Relay:
    """A loopback TLS-terminating relay: the client's transcript, both ways.

    It presents the node's own certificate (issued by the scratch CA, so the
    client verifies it against the CA it trusts) and opens a TLS connection
    to the node's TLS port verifying the same CA.  Every line either way goes
    to the client's wire log in tools/nntp_wire_log.py's format, secrets
    redacted by `Wire.line`, with a per-connection number.  Test tool only:
    it decides nothing and rewrites no octet.
    """

    def __init__(self, wire, node_port, cafile, cert, key):
        self.wire, self.node_port, self.cafile = wire, node_port, cafile
        self.server_context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.server_context.load_cert_chain(str(cert), str(key))
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(16)
        self.port = self.listener.getsockname()[1]
        self.lock = threading.Lock()
        self.closed = False
        threading.Thread(target=self.accept, daemon=True).start()

    def log(self, conn, tag, text):
        with self.lock:
            if not self.closed:
                self.wire.line(conn, tag, text)

    def accept(self):
        while True:
            try:
                raw, _ = self.listener.accept()
            except OSError:
                return
            with self.lock:
                self.wire.conn += 1
                conn = self.wire.conn
            threading.Thread(target=self.serve, args=(raw, conn), daemon=True).start()

    def serve(self, raw, conn):
        try:
            client = self.server_context.wrap_socket(raw, server_side=True)
        except (OSError, ssl.SSLError) as error:
            with self.lock:
                if not self.closed:
                    self.wire.out.write("%.3f %d --- client TLS handshake failed: %s\n"
                                        % (time.time(), conn, error))
            raw.close()
            return
        context = ssl.create_default_context(cafile=str(self.cafile))
        try:
            upstream = context.wrap_socket(
                socket.create_connection(("127.0.0.1", self.node_port), timeout=600),
                server_hostname="127.0.0.1")
        except (OSError, ssl.SSLError) as error:
            client.close()
            with self.lock:
                if not self.closed:
                    self.wire.out.write("%.3f %d --- relay could not reach the node: %s\n"
                                        % (time.time(), conn, error))
            return
        with self.lock:
            if not self.closed:
                self.wire.out.write("%.3f %d --- connection (client TLS to the relay, relay "
                                    "TLS to the node, both verified against the scratch "
                                    "CA)\n" % (time.time(), conn))
        for src, dst, tag in ((client, upstream, "C"), (upstream, client, "S")):
            threading.Thread(target=self.pump, args=(src, dst, tag, conn),
                             daemon=True).start()

    def pump(self, src, dst, tag, conn):
        pending = b""
        try:
            while True:
                chunk = src.recv(65536)
                if not chunk:
                    break
                dst.sendall(chunk)
                pending += chunk
                while b"\r\n" in pending:
                    line, pending = pending.split(b"\r\n", 1)
                    self.log(conn, tag, line.decode("utf-8", "replace"))
        except (OSError, ssl.SSLError):
            pass
        finally:
            for sock in (dst, src):
                try:
                    sock.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass

    def close(self):
        with self.lock:
            self.closed = True
        self.listener.close()


class Node:
    def __init__(self, args, work):
        self.work, self.args = work, args
        self.env = dict(os.environ, FN_NATIVE_HOST=str(Path(args.image).resolve()),
                        ACL2_CUSTOMIZATION="NONE")
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        if args.openssl_prefix:
            self.env["FN_OPENSSL_PREFIX"] = args.openssl_prefix
        self.ca, cert, key = scratch_ca(work)
        self.cert, self.key = cert, key
        self.port, self.tls_port = free_port(), free_port()
        self.config = work / "fn.toml"
        # A Unix socket path is at most 104 to 108 octets (sun_path); a deep
        # scratch tree overflows it and the owner cannot bind its control
        # socket (batch AR's image tree), so the socket lives in a short
        # private directory.
        self.control = Path(tempfile.mkdtemp(prefix="fnrc-", dir="/tmp")) / "control.sock"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\n'.format(
                work / "store", self.port, self.tls_port, cert, key,
                self.control), encoding="ascii")
        self.process = None

    def operator(self, *words, timeout=300):
        return run([str(ROOT / "packaging" / "fn-native"), "operator", str(self.config),
                    *words], cwd=str(ROOT), env=self.env, timeout=timeout)

    def start(self):
        self.log = open(self.work / "owner.stderr", "wb")
        self.process = subprocess.Popen(
            [str(ROOT / "packaging" / "fn-native"), "operator", str(self.config), "run"],
            cwd=str(ROOT), env=self.env, stdout=subprocess.PIPE, stderr=self.log,
            bufsize=0)
        seen, deadline = 0, time.monotonic() + 300
        while seen < 2 and time.monotonic() < deadline:
            if select.select([self.process.stdout], [], [], 5)[0]:
                line = self.process.stdout.readline()
                if not line:
                    break
                if line.startswith(b"LISTENING"):
                    seen += 1
        if seen < 2:
            raise RuntimeError("the owner did not report both listeners (exit {})".format(
                self.process.poll()))

    def stop(self):
        if self.process and self.process.poll() is None:
            self.process.send_signal(signal.SIGTERM)
            try:
                self.process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=30)
        return self.process.returncode if self.process else None


def prelude(node, wire, login, password, group, client, newsgroups=None, extra=()):
    """Invite, redeem over TLS, log in on a new connection and post a seed.

    `newsgroups` is the seed's Newsgroups field (default the one group; slrn
    gets a cross-post to exercise Xref), `extra` more header lines (pan's
    seed carries a Sender, which is what pan 0.162 matches when it cancels).
    """
    wire.mark("invite")
    invite = node.operator("account", "invite", "--expires", "3600")
    codes = re.findall(rb"^[0-9a-f]{32}$", invite.stdout, re.M)
    wire.out.write("%.3f 0 --- account invite exited %d with %d code(s)\n"
                   % (time.time(), invite.returncode, len(codes)))
    if len(codes) != 1:
        return {"error": "account invite exited {}: {}".format(
            invite.returncode, (invite.stdout + invite.stderr).decode()[-300:])}
    code = codes[0].decode()
    wire.mark("redeem")
    one = Session(wire, node.tls_port, node.ca)
    first = one.command("XREDEEM {} {}".format(code, login))
    second = one.command("XREDEEM PASS " + password) if first.startswith("381") else ""
    one.close()
    wire.mark("seed")
    two = Session(wire, node.tls_port, node.ca)
    user = two.command("AUTHINFO USER " + login)
    passed = two.command("AUTHINFO PASS " + password)
    seed_id = "<seed-{}-{}@matrix.example.invalid>".format(client, secrets.token_hex(4))
    posted = ""
    if passed.startswith("281") and two.command("POST").startswith("340"):
        for text in ("From: {} <{}@matrix.example.invalid>".format(login, login),
                     "Newsgroups: " + (newsgroups or group),
                     "Subject: seed for {}".format(client), "Message-ID: " + seed_id,
                     *extra, "", "a seed article for {} to read".format(client), "."):
            two.send(text)
        posted = two.read()
    two.close()
    return {"redeem": [first, second], "login": [user, passed], "seed": posted,
            "seed_id": seed_id}


def check(node, wire, login, password, mids):
    """HEAD of each Message-ID the client reported, as the same login."""
    wire.mark("check")
    session = Session(wire, node.tls_port, node.ca)
    session.command("AUTHINFO USER " + login)
    session.command("AUTHINFO PASS " + password)
    out = {}
    for name, mid in mids.items():
        if not mid:
            continue
        mid = mid if mid.startswith("<") else "<{}>".format(mid)
        status = session.command("HEAD " + mid)
        head = session.block() if status.startswith("221") else []
        out[name] = {"status": status, "references": next(
            (h for h in head if h.lower().startswith("references:")), ""),
            "subject": next((h for h in head if h.lower().startswith("subject:")), "")}
    # SEC-006: the cancelled article is gone from the reader's view: ARTICLE
    # answers 430 and OVER over the group does not list it.
    cancelled = out.get("cancelled")
    if cancelled is not None:
        mid = mids["cancelled"] if mids["cancelled"].startswith("<") else \
            "<{}>".format(mids["cancelled"])
        article = session.command("ARTICLE " + mid)
        if article.startswith("220"):
            session.block()
        cancelled["article"] = article
        group = session.command("GROUP " + node.args.group)
        listed = None
        if group.startswith("211"):
            over = session.command("OVER 1-")
            if over.startswith("224"):
                listed = any(line.split("\t")[4:5] == [mid] for line in session.block())
        cancelled["in_over"] = listed
    session.close()
    return out


# The group the slrn row creates live before the NEWGROUPS probe (PKT-665).
LATER_GROUP = "local.later"


def probe_new(node, wire, login, password, groups):
    """NEWGROUPS and NEWNEWS as the clients use them, and the RFC's other forms.

    slrn sends `NEWGROUPS yymmdd hhmmss GMT` from its newsrc.time stamp
    (group.c) and Thunderbird the four-digit form; neither slrn nor pan
    sends NEWNEWS, so its lines are RFC 3977 section 7.4's own forms.  The
    instants: a day before this run (every group and article here is newer)
    and a day after (nothing is).  Only the reply lines are recorded; the
    comparison with the RFC is the test's.
    """
    wire.mark("newgroups-newnews")
    session = Session(wire, node.tls_port, node.ca)
    session.command("AUTHINFO USER " + login)
    session.command("AUTHINFO PASS " + password)
    before, after = time.gmtime(time.time() - 86400), time.gmtime(time.time() + 86400)
    lines = [
        ("date", "DATE"),
        ("active_times", "LIST ACTIVE.TIMES"),
        ("newgroups_slrn", time.strftime("NEWGROUPS %y%m%d %H%M%S GMT", before)),
        ("newgroups_4digit", time.strftime("NEWGROUPS %Y%m%d %H%M%S GMT", before)),
        ("newgroups_future", time.strftime("NEWGROUPS %Y%m%d %H%M%S GMT", after)),
        ("newnews_all", time.strftime("NEWNEWS * %Y%m%d %H%M%S GMT", before)),
        ("newnews_group", time.strftime("NEWNEWS " + groups[0] + " %y%m%d %H%M%S", before)),
        ("newnews_future", time.strftime("NEWNEWS * %Y%m%d %H%M%S GMT", after)),
    ]
    out = {}
    for name, text in lines:
        status = session.command(text)
        block = session.block() if status[:3] in ("215", "230", "231") else []
        out[name] = {"command": text, "status": status, "lines": block}
    session.close()
    return out


def run_container(args, work, client, login, secret, wire_log):
    """The slrn or pan driver in the newsreader container, on the host network."""
    image = args.container
    built = run([args.docker, "build", "-q", "-t", image,
                 str(ROOT / "tools" / "reader_clients")], timeout=1800)
    if built.returncode:
        raise RuntimeError("docker build exited {}: {}".format(
            built.returncode, built.stderr.decode()[-300:]))
    command = [args.docker, "run", "--rm", "--network", "host",
               "-e", "FN_HOST_UID={}".format(os.getuid()),
               "-e", "FN_HOST_GID={}".format(os.getgid()),
               "-v", "{}:/work".format(work),
               "-v", "{}:/drive:ro".format(ROOT / "tools" / "reader_clients"),
               image, "python3", "/drive/drive.py", client,
               "--port", str(args.relay_port), "--user", login,
               "--password-file", "/work/" + secret.name, "--group", args.group,
               "--wire", "/work/" + wire_log.name, "--out", "/work/" + client]
    if client == "slrn":
        command += ["--second-group", args.second_group]
    version = run([args.docker, "run", "--rm", "--entrypoint", "dpkg-query", image, "-W",
                   "-f", "${Package} ${Version} ", "slrn", "pan"], timeout=120)
    step = run(command, timeout=900)
    return step, version.stdout.decode().strip(), built.stdout.decode().strip()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest() if Path(path).exists() else ""


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--image", required=True)
    parser.add_argument("--work", required=True)
    parser.add_argument("--clients", default="thunderbird")
    parser.add_argument("--group", default="local.general")
    parser.add_argument("--second-group", default="local.crosspost",
                        help="slrn's seed is cross-posted here (the Xref row)")
    parser.add_argument("--container", default="fn-reader-clients",
                        help="the image tools/reader_clients/Dockerfile builds")
    parser.add_argument("--docker", default="docker")
    parser.add_argument("--thunderbird", default="thunderbird")
    parser.add_argument("--openssl-prefix", default="")
    args = parser.parse_args(argv)
    work = Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    node = Node(args, work)
    report = {"image": str(args.image), "image_core_sha256": sha256(str(args.image) + ".core"),
              "group": args.group, "tls_port": node.tls_port, "clients": {}}
    init = node.operator("init", args.group, args.second_group, "control.cancel")
    report["init"] = [init.returncode, (init.stdout + init.stderr).decode()[-200:]]
    try:
        node.start()
        for client in [c for c in args.clients.split(",") if c]:
            log = work / "{}-wire.log".format(client)
            wire = Wire(log)
            login, password = "{}-friend".format(client), secrets.token_hex(12)
            secret = work / "{}.password".format(client)
            secret.write_text(password + "\n")
            secret.chmod(0o600)
            entry = {"log": str(log), "login": login}
            try:
                newsgroups, extra = None, ()
                if client == "slrn":
                    newsgroups = "{},{}".format(args.group, args.second_group)
                if client == "pan":
                    extra = ("Sender: {} <{}@matrix.example.invalid>".format(login, login),)
                entry["prelude"] = prelude(node, wire, login, password, args.group, client,
                                           newsgroups, extra)
                wire.out.flush()
                if client in ("slrn", "pan"):
                    relay = Relay(wire, node.tls_port, node.ca, node.cert, node.key)
                    args.relay_port = relay.port
                    try:
                        step, versions, image_id = run_container(args, work, client, login,
                                                                 secret, log)
                    finally:
                        relay.close()
                    text = step.stdout.decode("utf-8", "replace").strip()
                    entry.update(driver_exit=step.returncode, versions=versions,
                                 container_image=image_id,
                                 driver_stderr=step.stderr.decode("utf-8", "replace")[-600:])
                    try:
                        entry["driver"] = json.loads(text.splitlines()[-1]) if text else {}
                    except ValueError:
                        entry["driver"] = {"raw": text[-600:]}
                    wire.out.flush()
                    targets = re.findall(r" C: Control: cancel (<[^>]+>)",
                                         log.read_text(encoding="utf-8"))
                    entry["check"] = check(node, wire, login, password,
                                           {"seed": entry["prelude"].get("seed_id", ""),
                                            "cancelled": targets[0] if targets else ""})
                    if client == "slrn":
                        # PKT-665: a group created on the running node after
                        # the clients' first contact; NEWGROUPS must list it.
                        made = node.operator("group", "create", LATER_GROUP)
                        entry["group_create"] = {
                            "group": LATER_GROUP, "exit": made.returncode,
                            "stdout": made.stdout.decode("utf-8", "replace")[-300:]}
                    entry["new"] = probe_new(node, wire, login, password,
                                             [args.group, args.second_group])
                else:
                    if client != "thunderbird":
                        raise RuntimeError("no driver for client {!r}".format(client))
                    step = run([sys.executable, str(ROOT / "tools" / "thunderbird_drive.py"),
                                "--thunderbird", args.thunderbird, "--work", str(work),
                                "--port", str(node.tls_port), "--cafile", str(node.ca),
                                "--group", args.group, "--user", login, "--password-file",
                                str(secret), "--email",
                                "{}@matrix.example.invalid".format(login),
                                "--log", str(log)], timeout=900)
                    text = step.stdout.decode("utf-8", "replace").strip()
                    entry["driver_exit"] = step.returncode
                    entry["driver_stderr"] = step.stderr.decode("utf-8", "replace")[-600:]
                    try:
                        entry["driver"] = json.loads(text.splitlines()[-1]) if text else {}
                    except ValueError:
                        entry["driver"] = {"raw": text[-600:]}
                    actions = entry["driver"].get("actions", {}) if isinstance(
                        entry["driver"], dict) else {}
                    cancel = actions.get("cancel") or {}
                    mids = {"reply": cancel.get("reply_mid", ""), "cancelled": cancel.get("mid", ""),
                            "seed": entry["prelude"].get("seed_id", "")}
                    wire.out.flush()
                    entry["check"] = check(node, wire, login, password, mids)
            except Exception as error:                  # noqa: BLE001
                entry["error"] = "{}: {}".format(type(error).__name__, error)
            finally:
                wire.out.close()
            entry["sha256"] = sha256(log)
            report["clients"][client] = entry
    except Exception as error:                          # noqa: BLE001
        report["error"] = "{}: {}".format(type(error).__name__, error)
    finally:
        report["owner_exit"] = node.stop()
    try:
        from v0_matrix import client_wire_outcomes
        for client, entry in report["clients"].items():
            entry["outcomes"] = client_wire_outcomes(Path(entry["log"]).read_text(
                encoding="utf-8"))
    except Exception as error:                          # noqa: BLE001
        report["outcomes_error"] = "{}: {}".format(type(error).__name__, error)
    print(json.dumps(report, default=str))
    return 0 if not report.get("error") else 3


if __name__ == "__main__":
    sys.exit(main())
