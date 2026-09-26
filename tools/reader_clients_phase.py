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


class Node:
    def __init__(self, args, work):
        self.work, self.args = work, args
        self.env = dict(os.environ, FN_NATIVE_HOST=str(Path(args.image).resolve()),
                        ACL2_CUSTOMIZATION="NONE")
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        if args.openssl_prefix:
            self.env["FN_OPENSSL_PREFIX"] = args.openssl_prefix
        self.ca, cert, key = scratch_ca(work)
        self.port, self.tls_port = free_port(), free_port()
        self.config = work / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\n'.format(
                work / "store", self.port, self.tls_port, cert, key,
                work / "control.sock"), encoding="ascii")
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


def prelude(node, wire, login, password, group, client):
    """Invite, redeem over TLS, log in on a new connection and post a seed."""
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
                     "Newsgroups: " + group, "Subject: seed for {}".format(client),
                     "Message-ID: " + seed_id, "", "a seed article for {} to read".format(
                         client), "."):
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
    session.close()
    return out


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest() if Path(path).exists() else ""


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--image", required=True)
    parser.add_argument("--work", required=True)
    parser.add_argument("--clients", default="thunderbird")
    parser.add_argument("--group", default="local.general")
    parser.add_argument("--thunderbird", default="thunderbird")
    parser.add_argument("--openssl-prefix", default="")
    args = parser.parse_args(argv)
    work = Path(args.work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    node = Node(args, work)
    report = {"image": str(args.image), "image_core_sha256": sha256(str(args.image) + ".core"),
              "group": args.group, "tls_port": node.tls_port, "clients": {}}
    init = node.operator("init", args.group, "control.cancel")
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
                entry["prelude"] = prelude(node, wire, login, password, args.group, client)
                wire.out.flush()
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
