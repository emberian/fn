#!/usr/bin/env python3
"""Two-Store end-to-end join harness: fn A -> fn B -> Mini -> fn B -> fn A -> Mini.

The goal it serves: fresh signed peering into Mini consumption across two
isolated native Stores, run as ONE exchange, optionally with a crash cut:

  R authored at A  ->  A durable  ->  protected A->B peering  ->  B receiver
  verdict durable  ->  Mini consumes R at B (poll, Mini transaction, cursor
  ACK)  ->  Mini's signed reply Q posted at B  ->  B->A peering  ->  restart A
  and B from the same Stores  ->  Mini reads Q at A (poll, Mini result, ACK).

Two halves, one file.  `run` executes on the Mini host (the Mac, where the
Darwin Mini binary lives); it copies this file into SCRATCH on the fn host and
calls `fn <subcommand>` there over ssh for every native step.  Mini reaches fn
only through Mini's own transport bridge (`scripts/fn-e1e2/fn_bridge.sh`), the
same one its retained evidence names.  Every decision about articles, verdicts,
cursors and replies is made by the fn image or by Mini; this file sequences,
records and compares bytes.

Every step writes `logs/NN-<step>.log` and `.exit`, prints one verdict line,
and is exactly one of ACCEPTED, REFUSED or UNCERTAIN (AGENTS.md: the three
outcomes stay distinct).  The run stops at the first step that is not
ACCEPTED; a cut's deliberately uncertain step is recorded as UNCERTAIN and
settled by a separate step, never relabelled.

Exit codes of `fn` subcommands mirror the native host: 0 accepted, 1 refused,
3 uncertain, 4 harness fault, 5 usage.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import shlex
import shutil
import signal
import socket
import ssl
import subprocess
import sys
import time

ACCEPTED, REFUSED, UNCERTAIN, FAULT = "ACCEPTED", "REFUSED", "UNCERTAIN", "FAULT"
EXIT = {ACCEPTED: 0, REFUSED: 1, UNCERTAIN: 3, FAULT: 4}
R_ID = "<mini-e1-1bea29c16a63e8722f156770@example.invalid>"
R_SOURCE_SHA256 = "fca9c81e8cd02281b3703df4e931ae82c55a0bda63b3cf3447c8e32e13199000"
GROUP = "fn.test"
CONSUMER = "worker"  # Mini's bridge settles an ACK against consumer "worker".
CUTS = ("none", "a-accepted", "b-verdict", "ack-response", "reply-at-b")
SAFE = re.compile(r"/[A-Za-z0-9_./-]+")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


# ---------------------------------------------------------------------------
# fn side: runs ON the fn host (hbox), inside SCRATCH.
# ---------------------------------------------------------------------------

class Outcome(Exception):
    def __init__(self, outcome, detail, **facts):
        super().__init__(detail)
        self.outcome, self.detail, self.facts = outcome, detail, facts


class FnSide:
    def __init__(self, scratch):
        self.scratch = Path(scratch)
        self.state_path = self.scratch / "state.json"
        self.state = (json.loads(self.state_path.read_text())
                      if self.state_path.exists() else {})

    def save(self):
        tmp = self.state_path.with_suffix(".tmp")
        tmp.write_text(json.dumps(self.state, sort_keys=True, indent=2) + "\n")
        tmp.replace(self.state_path)

    # -- environment and native invocation --------------------------------

    def env(self):
        env = dict(os.environ)
        env["ACL2_CUSTOMIZATION"] = "NONE"
        for name in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "SBCL_USER_ARGS"):
            env.pop(name, None)
        prefix = self.state["openssl_prefix"]
        env["FN_OPENSSL_PREFIX"] = prefix
        env["LD_LIBRARY_PATH"] = prefix + "/lib"
        return env

    def native(self, *args, stdin=None, timeout=240, image=None):
        argv = [str(image or self.state["image"]), "--fn", *map(str, args)]
        print("$ " + " ".join(shlex.quote(a) for a in argv), flush=True)
        try:
            result = subprocess.run(argv, input=stdin, capture_output=True,
                                    env=self.env(), cwd=self.scratch, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            raise Outcome(UNCERTAIN, "native {} timed out after {}s".format(args[0], timeout),
                          argv=argv) from error
        sys.stdout.write("  exit={}\n  stdout={!r}\n  stderr={!r}\n".format(
            result.returncode, result.stdout[-4000:], result.stderr[-4000:]))
        sys.stdout.flush()
        return result

    def native_ok(self, *args, **kw):
        """A native command whose non-zero exit is carried as fn's own class."""
        result = self.native(*args, **kw)
        if result.returncode == 0:
            return result
        klass = {1: REFUSED, 3: UNCERTAIN}.get(result.returncode, FAULT)
        raise Outcome(klass, "native {} exit {}".format(args[0], result.returncode),
                      stderr=result.stderr[-2000:].decode("utf-8", "replace"))

    def openssl(self, *args):
        tool = self.state["openssl_prefix"] + "/bin/openssl"
        result = subprocess.run([tool, *map(str, args)], capture_output=True,
                                env=self.env(), timeout=60)
        if result.returncode != 0:
            raise Outcome(FAULT, "openssl {} failed: {}".format(args[0], result.stderr[-500:]))
        return result

    def node(self, name):
        return self.state["nodes"][name]

    # -- provisioning ------------------------------------------------------

    @staticmethod
    def free_ports(count, low=11201, high=11399):
        listening = subprocess.run(["ss", "-ltnH"], capture_output=True, text=True,
                                   timeout=30).stdout
        busy = {int(m) for m in re.findall(r":(\d+)\s", listening)}
        chosen = []
        for port in range(low, high):
            if port in busy:
                continue
            with socket.socket() as probe:
                try:
                    probe.bind(("127.0.0.1", port))
                except OSError:
                    continue
            chosen.append(port)
            if len(chosen) == count:
                return chosen
        raise Outcome(FAULT, "no free ports in {}..{}".format(low, high))

    def image_pair(self, image_dir, manifest):
        image_dir = Path(image_dir)
        files = {n: image_dir / n for n in ("fn-host", "fn-host.core", "fn-host-developer",
                                             "fn-host-developer.core")}
        missing = [str(files[n]) for n in ("fn-host", "fn-host.core") if not files[n].is_file()]
        if missing:
            raise Outcome(REFUSED, "production image incomplete: " + " ".join(missing))
        developer = files["fn-host-developer"].is_file() and \
            files["fn-host-developer.core"].is_file()
        if not developer:
            files = {n: files[n] for n in ("fn-host", "fn-host.core")}
        actual = {n: sha(p) for n, p in files.items()}
        if not manifest:
            for candidate in (image_dir / "image.sha256",
                              image_dir / "freeze" / "image-pair.sha256"):
                if candidate.is_file():
                    manifest = candidate
                    break
        manifest = Path(manifest) if manifest else image_dir / "image.sha256"
        if not manifest.is_file():
            raise Outcome(REFUSED, "no image-pair manifest at {}; refusing to run with "
                                   "hashes read from mutable launchers".format(manifest))
        expected = {}
        for line in manifest.read_text().splitlines():
            if line.strip():
                digest, name = line.split(None, 1)
                name = name.strip().lstrip("*")
                expected[Path(name).name] = digest
        for name, digest in actual.items():
            if expected.get(name) != digest:
                raise Outcome(REFUSED, "{} sha256 {} differs from manifest {}".format(
                    name, digest, expected.get(name)))
        runtime = None
        text = files["fn-host"].read_text(errors="replace")
        match = re.search(r'exec "([^"]+)"', text)
        if match and Path(match.group(1)).is_file():
            runtime = match.group(1)
        return {"image": str(files["fn-host"]),
                "developer": str(files["fn-host-developer"]) if developer else None,
                "hashes": actual, "manifest": str(manifest), "manifest_sha256": sha(manifest),
                "runtime": runtime, "runtime_sha256": sha(runtime) if runtime else None}

    def certificate(self, root, name):
        cert, key = root / (name + "-certificate.pem"), root / (name + "-key.pem")
        result = subprocess.run(
            ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
             "-days", "2", "-subj", "/CN=localhost", "-keyout", str(key), "-out", str(cert)],
            capture_output=True, timeout=60)
        if result.returncode != 0:
            raise Outcome(FAULT, "TLS certificate generation failed")
        key.chmod(0o600)
        return cert

    def initialize(self, name, port, login):
        root = self.scratch / name
        root.mkdir()
        store, control = root / "store", root / "control.sock"
        cert = self.certificate(root, name)
        password = secrets.token_urlsafe(24)
        password_file = root / "password"
        password_file.write_text(password + "\n")
        password_file.chmod(0o600)
        self.native_ok("store", store, "init", GROUP)
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n'.format(
                store, port, cert, root / (name + "-key.pem"), control, root / "auth.toml"))
        self.native_ok("operator", config, "principal", "set-password", login, "--posting",
                       stdin=(password + "\n" + password + "\n").encode())
        listed = self.native_ok("operator", config, "principal", "list").stdout.decode()
        principals = re.findall(r"[0-9a-f]{64}", listed)
        if len(principals) != 1:
            raise Outcome(FAULT, "expected one principal at {}: {}".format(name, listed))
        return {"name": name, "root": str(root), "store": str(store), "control": str(control),
                "config": str(config), "port": port, "certificate": str(cert),
                "principal": principals[0], "login": login,
                "password_file": str(password_file), "pid": None, "starts": []}

    def peer(self, source, target):
        profile = Path(source["root"]) / (target["name"] + ".fnauth")
        password = Path(target["password_file"]).read_text().strip()
        profile.write_bytes("FNAUTH1\n{}\n{}\n".format(target["login"], password).encode())
        profile.chmod(0o600)
        self.native_ok("operator", source["config"], "peer", "add", target["name"],
                       target["name"] + ".example.invalid", "127.0.0.1", target["port"],
                       "fn.*", "fn.*", "principal", source["principal"], profile,
                       "false", "true", "starttls", "localhost", target["certificate"])

    def signer(self, root, label, principal_byte):
        from cryptography.hazmat.primitives import serialization
        from cryptography.hazmat.primitives.asymmetric import ed25519
        root = Path(root)
        key = ed25519.Ed25519PrivateKey.generate()
        seed = key.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw,
                                 serialization.NoEncryption())
        ed = key.public_key().public_bytes(serialization.Encoding.Raw,
                                           serialization.PublicFormat.Raw)
        paths = {k: str(root / (label + suffix)) for k, suffix in (
            ("principal", "-principal.bin"), ("ed_public", "-ed-public.bin"),
            ("ed_secret", "-ed-secret.bin"), ("ml_private", "-ml-private.pem"),
            ("ml_public", "-ml-public.pem"), ("ml_raw", "-ml-public.raw"))}
        Path(paths["principal"]).write_bytes(bytes([principal_byte]) * 32)
        Path(paths["ed_public"]).write_bytes(ed)
        Path(paths["ed_secret"]).write_bytes(seed + ed)
        Path(paths["ed_secret"]).chmod(0o600)
        self.openssl("genpkey", "-algorithm", "ML-DSA-65", "-out", paths["ml_private"])
        Path(paths["ml_private"]).chmod(0o600)
        self.openssl("pkey", "-in", paths["ml_private"], "-pubout", "-out", paths["ml_public"])
        self.openssl("asn1parse", "-inform", "PEM", "-in", paths["ml_public"], "-strparse",
                     "17", "-noout", "-out", paths["ml_raw"])
        if len(Path(paths["ml_raw"]).read_bytes()) != 1952:
            raise Outcome(FAULT, "ML-DSA-65 raw public key is not 1952 bytes")
        return paths

    def cmd_provision(self, args):
        if self.state:
            raise Outcome(REFUSED, "SCRATCH already provisioned; use a fresh directory")
        prefix = args.openssl_prefix
        if not Path(prefix, "bin", "openssl").is_file():
            raise Outcome(REFUSED, "no OpenSSL at " + prefix)
        self.state = {"version": 1, "openssl_prefix": prefix, "cut": args.cut}
        self.state.update(self.image_pair(args.image_dir, args.manifest))
        r_source = Path(args.r_source).read_bytes()
        if hashlib.sha256(r_source).hexdigest() != R_SOURCE_SHA256 or \
                ("Message-ID: " + R_ID).encode() not in r_source:
            raise Outcome(REFUSED, "R source is not the retained Mini E1 report source")
        port_a, port_b = self.free_ports(2)
        a = self.initialize("a", port_a, "b-at-a")
        b = self.initialize("b", port_b, "a-at-b")
        self.state["nodes"] = {"a": a, "b": b}
        self.save()
        self.peer(a, b)
        self.peer(b, a)
        self.state["r"] = self.signer(a["root"], "r", 0x52)
        self.state["q"] = self.signer(b["root"], "q", 0x51)
        (Path(a["root"]) / "r.source").write_bytes(r_source)
        self.state["r_source"] = str(Path(a["root"]) / "r.source")
        self.save()
        return {"ports": [port_a, port_b], "image_hashes": self.state["hashes"],
                "runtime": self.state["runtime"], "runtime_sha256": self.state["runtime_sha256"]}

    # -- owner processes ---------------------------------------------------

    def alive(self, node):
        pid = node.get("pid")
        if not pid:
            return False
        try:
            cmdline = Path("/proc/{}/cmdline".format(pid)).read_bytes().split(b"\0")
            status = Path("/proc/{}/status".format(pid)).read_text()
        except OSError:
            return False
        if "State:\tZ" in status:
            return False
        # PID-reuse guard: it must still be our owner of this config.
        return node["config"].encode() in cmdline

    def proc_state(self, node):
        try:
            for line in Path("/proc/{}/status".format(node["pid"])).read_text().splitlines():
                if line.startswith("State:"):
                    return line.split()[1]
        except OSError:
            return None
        return None

    def cmd_start(self, args):
        node = self.node(args.node)
        if self.alive(node):
            raise Outcome(FAULT, "{} already running as {}".format(args.node, node["pid"]))
        developer = bool(args.developer)
        if developer and not self.state.get("developer"):
            raise Outcome(REFUSED, "this cut needs the developer image, absent from IMAGE_DIR")
        image = self.state["developer"] if developer else self.state["image"]
        env = self.env()
        selectors = dict(item.split("=", 1) for item in args.selector or ())
        if selectors and not developer:
            raise Outcome(FAULT, "developer selectors need --developer")
        env.update(selectors)
        root = Path(node["root"])
        stdout_path = root / "owner-{}.stdout".format(len(node["starts"]))
        with open(stdout_path, "wb") as out, open(root / "owner.stderr", "ab") as err:
            process = subprocess.Popen([image, "--fn", "operator", node["config"], "run"],
                                       stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                                       env=env, cwd=self.scratch, start_new_session=True)
        node["pid"] = process.pid
        start = {"pid": process.pid, "image": image, "selectors": selectors,
                 "at": time.time(), "stdout": str(stdout_path)}
        node["starts"].append(start)
        self.save()
        with open(self.scratch / "pids.log", "a") as log:
            log.write("start {} pid={} image={} selectors={}\n".format(
                args.node, process.pid, image, selectors))
        deadline = time.monotonic() + args.timeout
        expected = "LISTENING {}".format(node["port"]).encode()
        while time.monotonic() < deadline:
            if expected in stdout_path.read_bytes():
                break
            if process.poll() is not None:
                raise Outcome(REFUSED, "{} owner exited {} before LISTENING".format(
                    args.node, process.returncode),
                    stdout=stdout_path.read_bytes()[-2000:].decode("utf-8", "replace"))
            time.sleep(0.1)
        else:
            raise Outcome(UNCERTAIN, "{} owner did not announce LISTENING in {}s".format(
                args.node, args.timeout))
        exe = os.readlink("/proc/{}/exe".format(process.pid))
        cmdline = Path("/proc/{}/cmdline".format(process.pid)).read_bytes().split(b"\0")
        core = Path(image + ".core")
        if str(core).encode() not in cmdline:
            raise Outcome(FAULT, "owner cmdline does not name the image core")
        start.update(exe=exe, exe_sha256=sha(exe), core_sha256=sha(core))
        self.save()
        return {"pid": process.pid, "image": image, "core_sha256": start["core_sha256"],
                "runtime_sha256": start["exe_sha256"], "selectors": selectors}

    def cmd_stop(self, args):
        node = self.node(args.node)
        if not self.alive(node):
            raise Outcome(FAULT, "{} has no live owner started by this harness".format(args.node))
        pid = node["pid"]
        sig = {"TERM": signal.SIGTERM, "KILL": signal.SIGKILL}[args.signal]
        os.kill(pid, sig)
        if args.signal == "TERM" and self.proc_state(node) == "T":
            os.kill(pid, signal.SIGCONT)
        with open(self.scratch / "pids.log", "a") as log:
            log.write("{} {} pid={}\n".format(args.signal, args.node, pid))
        deadline = time.monotonic() + args.timeout
        while time.monotonic() < deadline and self.alive(node):
            time.sleep(0.1)
        if self.alive(node):
            raise Outcome(UNCERTAIN, "{} pid {} still alive after SIG{}".format(
                args.node, pid, args.signal))
        node["pid"] = None
        node["starts"][-1]["stopped"] = {"signal": args.signal, "at": time.time()}
        self.save()
        return {"pid": pid, "signal": args.signal}

    def cmd_wait_stopped(self, args):
        """Wait for the developer feed cut's SIGSTOP (group stop, state T)."""
        node = self.node(args.node)
        deadline = time.monotonic() + args.timeout
        while time.monotonic() < deadline:
            if not self.alive(node):
                raise Outcome(REFUSED, "{} exited instead of stopping at the cut".format(args.node))
            if self.proc_state(node) == "T":
                return {"pid": node["pid"], "state": "T"}
            time.sleep(0.05)
        raise Outcome(UNCERTAIN, "{} did not reach the developer cut in {}s".format(
            args.node, args.timeout))

    # -- protected NNTP observation ----------------------------------------

    MULTILINE = (b"100", b"101", b"215", b"220", b"221", b"222", b"224", b"225",
                 b"230", b"231")

    def nntp(self, node, command):
        """One protected command; a silent or broken server is UNCERTAIN."""
        try:
            return self.nntp_once(node, command)
        except OSError as error:
            raise Outcome(UNCERTAIN, "{} NNTP {}: {}".format(
                node["name"], command.split()[0].decode(), error)) from error

    def nntp_once(self, node, command):
        """One protected command; returns (status line, body bytes or None)."""
        password = Path(node["password_file"]).read_text().strip()
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=15) as raw:
            def line():
                data = bytearray()
                while not data.endswith(b"\n"):
                    chunk = raw.recv(1)
                    if not chunk:
                        break
                    data.extend(chunk)
                return bytes(data)
            if not line().startswith((b"200 ", b"201 ")):
                raise Outcome(UNCERTAIN, "no NNTP greeting from " + node["name"])
            raw.sendall(b"STARTTLS\r\n")
            if not line().startswith(b"382 "):
                raise Outcome(REFUSED, node["name"] + " refused STARTTLS")
            context = ssl.create_default_context(cafile=node["certificate"])
            with context.wrap_socket(raw, server_hostname="localhost") as tls:
                with tls.makefile("rwb", buffering=0) as stream:
                    stream.write(b"AUTHINFO USER " + node["login"].encode() + b"\r\n")
                    if not stream.readline().startswith(b"381 "):
                        raise Outcome(REFUSED, node["name"] + " refused AUTHINFO USER")
                    stream.write(b"AUTHINFO PASS " + password.encode() + b"\r\n")
                    if not stream.readline().startswith(b"281 "):
                        raise Outcome(REFUSED, node["name"] + " refused AUTHINFO PASS")
                    stream.write(command + b"\r\n")
                    status = stream.readline()
                    if status[:3] not in self.MULTILINE:
                        return status, None
                    body = bytearray()
                    while True:
                        row = stream.readline()
                        if row == b"":
                            raise Outcome(UNCERTAIN, "EOF inside multi-line reply")
                        if row == b".\r\n":
                            return status, bytes(body)
                        body.extend(row[1:] if row.startswith(b"..") else row)

    def article(self, node, message_id):
        status, body = self.nntp(node, b"ARTICLE " + message_id.encode())
        if status.startswith(b"430 "):
            return None
        if not status.startswith(b"220 "):
            raise Outcome(UNCERTAIN, "ARTICLE answered {!r}".format(status))
        return body

    def cmd_await(self, args):
        node = self.node(args.node)
        message_id = self.message_id(args.message)
        deadline = time.monotonic() + args.timeout
        while time.monotonic() < deadline:
            body = self.article(node, message_id)
            if body is not None:
                out = Path(node["root"]) / args.out
                out.write_bytes(body)
                return {"message_id": message_id, "bytes": len(body), "sha256": sha(out),
                        "path": str(out)}
            time.sleep(0.2)
        # Absence at a deadline is not a definitive refusal: the feed may retry.
        raise Outcome(UNCERTAIN, "{} absent at {} after {}s".format(
            message_id, args.node, args.timeout))

    def cmd_absent(self, args):
        node = self.node(args.node)
        message_id = self.message_id(args.message)
        deadline = time.monotonic() + args.seconds
        while time.monotonic() < deadline:
            if self.article(node, message_id) is not None:
                raise Outcome(REFUSED, "{} already present at {}".format(message_id, args.node))
            time.sleep(0.2)
        return {"message_id": message_id, "absent_for_seconds": args.seconds}

    def cmd_same(self, args):
        a, b = Path(self.node(args.node)["root"]) / args.first, \
            Path(self.node(args.node)["root"]) / args.second
        if a.read_bytes() != b.read_bytes():
            raise Outcome(REFUSED, "{} and {} differ".format(a, b))
        return {"sha256": sha(a)}

    def cmd_count(self, args):
        """Live article count in the group (NNTP GROUP) on both Stores."""
        out = {}
        for name in ("a", "b"):
            status, _ = self.nntp(self.node(name), b"GROUP " + GROUP.encode())
            if not status.startswith(b"211 "):
                raise Outcome(UNCERTAIN, "GROUP at {} answered {!r}".format(name, status))
            out[name] = int(status.split()[1])
        if any(v != args.expect for v in out.values()):
            raise Outcome(REFUSED, "group counts {} != {} each".format(out, args.expect), **out)
        return out

    def message_id(self, token):
        if token == "R":
            return R_ID
        if token == "Q":
            return self.state["q_message_id"]
        return token

    # -- authorship, verdicts and consumers ---------------------------------

    def cmd_setup(self, args):
        a, b = self.node("a"), self.node("b")
        out = {}
        for name, node in (("a", a), ("b", b)):
            self.native_ok("consumer", "bootstrap", node["control"])
            registered = Path(node["root"]) / "registered.fncu"
            self.native_ok("consumer", "register", node["control"], CONSUMER, GROUP, registered)
            out[name + "_registered_sha256"] = sha(registered)
        for node in (a, b):
            self.enroll(node, 1, self.state["r"])
        return out

    def enroll(self, node, generation, keys):
        self.native_ok("hybrid-enroll", node["control"], generation, keys["principal"],
                       keys["ed_public"], keys["ml_public"])

    def cmd_enroll_q(self, args):
        for name in ("a", "b"):
            self.enroll(self.node(name), 2, self.state["q"])
        return {"generation": 2}

    def cmd_author_r(self, args):
        a, r = self.node("a"), self.state["r"]
        signed = self.native_ok("hybrid-sign", r["principal"], r["ed_public"], r["ed_secret"],
                                r["ml_public"], r["ml_private"], self.state["r_source"])
        values = dict(line.split() for line in signed.stdout.decode().splitlines())
        root = Path(a["root"])
        (root / "r-ed.sig").write_bytes(bytes.fromhex(values["ed25519"]))
        (root / "r-ml.sig").write_bytes(bytes.fromhex(values["ml-dsa-65"]))
        answer = self.native("hybrid-author", a["control"], 1, self.state["r_source"],
                             root / "r-ed.sig", root / "r-ml.sig", r["ml_public"])
        if answer.returncode == 3:
            raise Outcome(UNCERTAIN, "A hybrid-author answered uncertain (exit 3)")
        if answer.returncode != 0:
            raise Outcome(REFUSED, "A hybrid-author exit {}".format(answer.returncode))
        return {"hybrid_author_stdout": answer.stdout.decode("utf-8", "replace").strip()}

    def cmd_verify(self, args):
        node = self.node(args.node)
        keys = self.state[args.signer]
        carrier = Path(node["root"]) / args.carrier
        source = Path(args.source if args.source.startswith("/") else
                      Path(node["root"]) / args.source).read_bytes()
        answer = self.native_ok("hybrid-verify-source", carrier, keys["ml_public"])
        fields = answer.stdout.decode().strip().split()
        want = [Path(keys["principal"]).read_bytes().hex(),
                Path(keys["ed_public"]).read_bytes().hex(),
                Path(keys["ml_raw"]).read_bytes().hex()]
        if len(fields) != 6 or fields[0] != "fn-portable-v1" or \
                [fields[1], fields[3], fields[4]] != want or bytes.fromhex(fields[5]) != source:
            raise Outcome(REFUSED, "native verifier tuple does not match signer/source")
        return {"source_identity": fields[2]}

    def header(self, node, message_id):
        status, body = self.nntp(node, b"HDR :fn-verified " + message_id.encode())
        if not status.startswith(b"225 "):
            return status
        return body

    def cmd_verdict(self, args):
        """B's acceptance-time verdict: HDR :fn-verified, then poll + project.

        All observations are made and logged; the step is ACCEPTED only if all
        hold.  A missing verdict is fn's definitive answer (REFUSED)."""
        node = self.node(args.node)
        keys = self.state[args.signer]
        message_id = self.message_id(args.message)
        expected = "0 verified {} keyring {}\r\n".format(
            Path(keys["principal"]).read_bytes().hex(), args.generation).encode()
        header = self.header(node, message_id)
        facts = {"hdr": header.decode("utf-8", "replace"), "hdr_expected":
                 expected.decode()}
        problems = []
        if header != expected:
            problems.append("HDR :fn-verified {!r} != {!r}".format(header, expected))
        if args.poll:
            projection = self.poll_project(node, args.poll)
            facts["projection"] = projection
            if projection["status"] != "projected":
                problems.append("consumer-project " + projection["status"])
            else:
                source = Path(self.state["r_source"] if args.message == "R"
                              else node["root"] + "/" + args.expect_source).read_bytes()
                if bytes.fromhex(projection["fields"][14]) != source:
                    problems.append("projected source differs")
                if bytes.fromhex(projection["fields"][13]).decode() != message_id:
                    problems.append("projected Message-ID differs")
        if problems:
            raise Outcome(REFUSED, "; ".join(problems), **facts)
        return facts

    def poll_project(self, node, prefix):
        root = Path(node["root"])
        cursor, event = root / (prefix + ".fncu"), root / (prefix + ".fn-e")
        self.native_ok("consumer", "poll", node["control"], CONSUMER, cursor, event)
        answer = self.native("consumer-project", cursor, event)
        text = (answer.stdout + answer.stderr).decode("utf-8", "replace").strip()
        fields = answer.stdout.decode("ascii", "replace").strip().split()
        out = {"cursor_sha256": sha(cursor), "event_sha256": sha(event),
               "event_bytes": event.stat().st_size, "exit": answer.returncode}
        if answer.returncode == 0 and len(fields) == 18 and fields[0] == "fn-consumer-project-v1":
            out.update(status="projected", fields=fields)
        else:
            out.update(status="refused", answer=text[-600:])
        return out

    def cmd_poll(self, args):
        node = self.node(args.node)
        projection = self.poll_project(node, args.prefix)
        if projection["status"] != "projected":
            raise Outcome(REFUSED, "consumer-project refused", **projection)
        message_id = bytes.fromhex(projection["fields"][13]).decode()
        if args.message and message_id != self.message_id(args.message):
            raise Outcome(REFUSED, "poll returned {} not {}".format(message_id, args.message))
        if args.ack:
            self.native_ok("consumer", "ack", node["control"],
                           Path(node["root"]) / (args.prefix + ".fncu"))
        return {"message_id": message_id, "acked": bool(args.ack),
                "cursor_sha256": projection["cursor_sha256"],
                "event_sha256": projection["event_sha256"]}

    def cmd_position(self, args):
        node = self.node(args.node)
        out = Path(node["root"]) / args.out
        self.native_ok("consumer", "position", node["control"], CONSUMER, out)
        facts = {"sha256": sha(out)}
        if args.equals:
            other = Path(node["root"]) / args.equals
            if other.read_bytes() != out.read_bytes():
                raise Outcome(REFUSED, "position differs from " + args.equals, **facts)
        return facts

    def cmd_set_q(self, args):
        if not re.fullmatch(r"<[!-~]+>", args.message_id):
            raise Outcome(FAULT, "bad Q Message-ID")
        self.state["q_message_id"] = args.message_id
        self.state["q_source"] = args.source
        self.save()
        return {"q_message_id": args.message_id, "q_source_sha256": sha(args.source)}

    def cmd_status(self, args):
        """Article counts from the stopped Stores (operator status)."""
        out = {}
        for name in ("a", "b"):
            node = self.node(name)
            if self.alive(node):
                raise Outcome(FAULT, name + " must be stopped for operator status")
            text = self.native_ok("operator", node["config"], "status").stdout.decode()
            match = re.search(r"articles=(\d+)", text)
            out[name] = int(match.group(1)) if match else None
        if args.expect is not None and any(v != args.expect for v in out.values()):
            raise Outcome(REFUSED, "article counts {} != {} each".format(out, args.expect), **out)
        return out

    def cmd_ready(self, args):
        """Public (and hbox-local secret-path) handoff for the Mini half."""
        a, b, r, q = self.node("a"), self.node("b"), self.state["r"], self.state["q"]
        return {"image": self.state["image"], "a_control": a["control"],
                "b_control": b["control"], "a_root": a["root"], "b_root": b["root"],
                "r": r, "q": {k: q[k] for k in ("principal", "ed_public", "ml_public",
                                                "ml_raw", "ed_secret", "ml_private")},
                "r_source": self.state["r_source"],
                "pids": {n: self.node(n)["pid"] for n in ("a", "b")}}

    def cmd_cleanup(self, args):
        stopped = {}
        for name in ("a", "b"):
            node = self.node(name)
            if self.alive(node):
                if self.proc_state(node) == "T":
                    os.kill(node["pid"], signal.SIGKILL)
                    stopped[name] = "KILL"
                else:
                    os.kill(node["pid"], signal.SIGTERM)
                    stopped[name] = "TERM"
                with open(self.scratch / "pids.log", "a") as log:
                    log.write("cleanup {} {} pid={}\n".format(stopped[name], name, node["pid"]))
                deadline = time.monotonic() + 60
                while time.monotonic() < deadline and self.alive(node):
                    time.sleep(0.1)
                if self.alive(node):
                    os.kill(node["pid"], signal.SIGKILL)
                node["pid"] = None
        self.save()
        return {"stopped": stopped}


def fn_main(argv):
    parser = argparse.ArgumentParser(prog="two_store_join.py fn")
    parser.add_argument("--scratch", required=True)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("provision")
    p.add_argument("--image-dir", required=True)
    p.add_argument("--manifest")
    p.add_argument("--openssl-prefix", required=True)
    p.add_argument("--r-source", required=True)
    p.add_argument("--cut", default="none")
    p = sub.add_parser("start")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("--developer", action="store_true")
    p.add_argument("--selector", action="append")
    p.add_argument("--timeout", type=int, default=180)
    p = sub.add_parser("stop")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("--signal", choices=("TERM", "KILL"), default="TERM")
    p.add_argument("--timeout", type=int, default=60)
    p = sub.add_parser("wait-stopped")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("--timeout", type=int, default=60)
    p = sub.add_parser("await")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("message")
    p.add_argument("out")
    p.add_argument("--timeout", type=int, default=120)
    p = sub.add_parser("absent")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("message")
    p.add_argument("--seconds", type=int, default=3)
    p = sub.add_parser("same")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("first")
    p.add_argument("second")
    sub.add_parser("setup")
    sub.add_parser("enroll-q")
    sub.add_parser("author-r")
    p = sub.add_parser("verify")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("carrier")
    p.add_argument("signer", choices=("r", "q"))
    p.add_argument("source")
    p = sub.add_parser("verdict")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("message")
    p.add_argument("signer", choices=("r", "q"))
    p.add_argument("generation", type=int)
    p.add_argument("--poll")
    p.add_argument("--expect-source")
    p = sub.add_parser("poll")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("prefix")
    p.add_argument("--message")
    p.add_argument("--ack", action="store_true")
    p = sub.add_parser("position")
    p.add_argument("node", choices=("a", "b"))
    p.add_argument("out")
    p.add_argument("--equals")
    p = sub.add_parser("set-q")
    p.add_argument("message_id")
    p.add_argument("source")
    p = sub.add_parser("status")
    p.add_argument("--expect", type=int)
    sub.add_parser("ready")
    p = sub.add_parser("count")
    p.add_argument("--expect", type=int, required=True)
    sub.add_parser("cleanup")
    args = parser.parse_args(argv)
    side = FnSide(args.scratch)
    handler = getattr(side, "cmd_" + args.cmd.replace("-", "_"))
    try:
        facts = handler(args) or {}
        outcome, detail = ACCEPTED, args.cmd
    except Outcome as error:
        outcome, detail, facts = error.outcome, error.detail, error.facts
    except Exception as error:  # a harness defect, never an fn outcome
        outcome, detail, facts = FAULT, "{}: {}".format(type(error).__name__, error), {}
    print("RESULT " + json.dumps({"outcome": outcome, "detail": detail, "facts": facts},
                                 sort_keys=True, default=str), flush=True)
    return EXIT[outcome]


# ---------------------------------------------------------------------------
# Orchestrator: runs on the Mini host.
# ---------------------------------------------------------------------------

class Stop(Exception):
    pass


class Run:
    def __init__(self, args):
        self.args = args
        self.host = args.fn_host
        self.scratch = args.scratch
        self.out = Path(args.local_out).resolve()
        self.logs = self.out / "logs"
        self.n = 0
        self.steps = []
        self.cut = args.cut
        self.mini_bin = Path(args.mini_bin).resolve()
        self.mini_client = Path(args.mini_client).resolve()
        self.bridge = Path(args.mini_repo) / "scripts" / "fn-e1e2" / "fn_bridge.sh"
        self.benv = dict(os.environ)

    # -- step machinery ----------------------------------------------------

    def step(self, label, argv, classify=None, timeout=600, env=None):
        """Run one step; log and exit files; one verdict line; stop unless accepted."""
        self.n += 1
        name = "{:02d}-{}".format(self.n, label)
        log, code_file = self.logs / (name + ".log"), self.logs / (name + ".exit")
        started = time.monotonic()
        with log.open("wb") as handle:
            handle.write(("$ " + " ".join(shlex.quote(str(a)) for a in argv) + "\n").encode())
            handle.flush()
            try:
                result = subprocess.run([str(a) for a in argv], stdout=handle,
                                        stderr=subprocess.STDOUT, timeout=timeout,
                                        env=env or self.benv, cwd=self.out)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = None
        seconds = round(time.monotonic() - started, 3)
        code_file.write_text("{}\n".format("timeout" if code is None else code))
        text = log.read_text(errors="replace")
        facts = {}
        if code is None:
            outcome, detail = UNCERTAIN, "timed out after {}s".format(timeout)
        elif classify is not None:
            outcome, detail, facts = classify(code, text)
        else:
            outcome, detail = ((ACCEPTED, "exit 0") if code == 0 else
                               (REFUSED, "exit {}".format(code)))
        record = {"n": self.n, "step": label, "outcome": outcome, "detail": detail,
                  "exit": code, "seconds": seconds, "log": str(log.relative_to(self.out)),
                  "log_sha256": sha(log), "facts": facts}
        self.steps.append(record)
        (self.out / "steps.json").write_text(json.dumps(self.steps, indent=2, default=str) + "\n")
        print("{:>2} {:<28} {:<10} {}".format(self.n, label, outcome, detail), flush=True)
        return record

    def require(self, record, want=ACCEPTED):
        if record["outcome"] != want:
            raise Stop("{} was {}, not {}".format(record["step"], record["outcome"], want))
        return record

    def fn(self, label, *args, timeout=600, want=ACCEPTED):
        argv = ["ssh", self.host, " ".join(shlex.quote(str(a)) for a in (
            "python3", self.scratch + "/harness/two_store_join.py", "fn",
            "--scratch", self.scratch, *args))]

        def classify(code, text):
            rows = [l for l in text.splitlines() if l.startswith("RESULT ")]
            if not rows:  # ssh/transport lost: not an fn answer
                return UNCERTAIN, "no RESULT line (exit {})".format(code), {}
            result = json.loads(rows[-1][len("RESULT "):])
            return result["outcome"], result["detail"], result["facts"]
        return self.require(self.step(label, argv, classify, timeout), want)

    def mini(self, label, argv, check=None, expected=0, timeout=600, env=None, want=ACCEPTED):
        def classify(code, text):
            try:
                held = check is None or bool(check())
            except (OSError, ValueError, KeyError, TypeError) as error:
                held = False
                print("postcondition error: {!r}".format(error))
            if code == expected and held:
                return ACCEPTED, "exit {}".format(code), {}
            if code == expected:
                return REFUSED, "exit {} but postcondition failed".format(code), {}
            return REFUSED, "exit {} (expected {})".format(code, expected), {}
        return self.require(self.step(label, argv, classify, timeout, env), want)

    def ack(self, label, argv, result, env=None, want=ACCEPTED):
        """Mini's ACK outcome word, kept in its own class."""
        def classify(code, text):
            try:
                word = self.json(result).get("fnAck")
            except (OSError, ValueError):
                word = None
            if code == 0 and word == "durable-accepted":
                return ACCEPTED, "fnAck durable-accepted", {"fnAck": word}
            if word in ("uncertain", "transport-fault"):
                return UNCERTAIN, "fnAck " + word, {"fnAck": word}
            return REFUSED, "exit {} fnAck {}".format(code, word), {"fnAck": word}
        return self.require(self.step(label, argv + [self.out / result], classify, env=env), want)

    def scp_from(self, label, remote, local):
        return self.require(self.step(label, ["scp", "-q", self.host + ":" + remote, local]))

    def json(self, name):
        return json.loads((self.out / name).read_text())

    # -- Mini deployments --------------------------------------------------

    def mini_deployment(self, side):
        root = self.out / ("mini-" + side)
        root.mkdir()
        config = json.loads(Path(self.args.mini_pinned_config).read_text())
        config["storageRoot"] = str(root / "store")
        (root / "config.json").write_text(json.dumps(config, sort_keys=True, indent=2) + "\n")
        self.mini("mini-{}-bootstrap".format(side),
                  [self.mini_bin, root / "config.json", "bootstrap", self.args.mini_genesis])
        birth = root / "birth"

        def confirmed():
            outcome = json.loads((birth / "outcome.json").read_text())
            return outcome.get("type") == "confirmed" and str(outcome.get("acceptedCount")) == "1"
        self.mini("mini-{}-birth".format(side),
                  [self.mini_client, "submit", "--host", self.mini_bin, "--config",
                   root / "config.json", "--intent", self.args.mini_birth_intent,
                   "--intent-kind", "birth-intent", "--key", self.args.mini_custody_key,
                   "--dir", birth], check=confirmed)
        return root / "config.json"

    def bridge_verify(self, label, carrier, ml_public):
        record = self.mini(label, [self.bridge, "--fn", "hybrid-verify-source", carrier,
                                   ml_public])
        fields = Path(self.logs / "{:02d}-{}.log".format(self.n, label)).read_text() \
            .splitlines()[-1].split()
        if len(fields) != 6 or fields[0] != "fn-portable-v1":
            raise Stop(label + " returned no verifier tuple")
        return fields

    @staticmethod
    def pin(bridge, keys):
        return {"fnBinary": str(bridge), "mlPublicKey": str(keys["ml_public"]),
                "principal": Path(keys["principal"]).read_bytes().hex(),
                "edPublicKey": Path(keys["ed_public"]).read_bytes().hex(),
                "mlPublicKeyHex": Path(keys["ml_raw"]).read_bytes().hex()}

    def fetch_keys(self, keys, label):
        local = {}
        for field in ("principal", "ed_public", "ml_public", "ml_raw"):
            target = self.out / "{}-{}".format(label, Path(keys[field]).name)
            self.scp_from("fetch-{}-{}".format(label, field), keys[field], target)
            local[field] = target
        return local

    def project(self, label, cursor, event):
        record = self.mini(label, [self.bridge, "--fn", "consumer-project", cursor, event])
        fields = (self.logs / "{:02d}-{}.log".format(self.n, label)).read_text() \
            .strip().splitlines()[-1].split(" ")
        if len(fields) != 18 or fields[0] != "fn-consumer-project-v1":
            raise Stop(label + " returned no projection")
        return fields

    @staticmethod
    def scope(fields):
        return {"history": fields[1], "incarnation": fields[2], "consumer": fields[3],
                "principal": fields[4], "query": fields[5], "queryVersion": int(fields[6]),
                "viewVersion": int(fields[7]), "registrationEpoch": int(fields[8])}

    # -- the exchange -------------------------------------------------------

    def preflight(self):
        self.out.mkdir(parents=True, exist_ok=False)
        self.logs.mkdir()
        facts = {"mini_bin": str(self.mini_bin), "mini_bin_sha256": sha(self.mini_bin),
                 "mini_client_sha256": sha(self.mini_client),
                 "bridge_sha256": sha(self.bridge), "harness_sha256": sha(__file__),
                 "cut": self.cut}
        if self.args.mini_sha256 and facts["mini_bin_sha256"] != self.args.mini_sha256:
            raise Stop("Mini executable sha256 {} is not the pinned {}".format(
                facts["mini_bin_sha256"], self.args.mini_sha256))
        (self.out / "inputs.json").write_text(json.dumps(facts, indent=2) + "\n")
        print("mini {} sha256 {}".format(self.mini_bin, facts["mini_bin_sha256"]), flush=True)
        if not SAFE.fullmatch(self.scratch) or not self.scratch.startswith("/tank/fn/scratch/"):
            raise Stop("SCRATCH must be a fresh directory under /tank/fn/scratch/")
        if not self.args.image_dir.startswith("/tank/fn/gates/"):
            raise Stop("Mini's bridge accepts only images under /tank/fn/gates/")
        self.require(self.step("scratch-fresh", ["ssh", self.host, "test ! -e {0} && mkdir -p {0}/harness {0}/logs".format(shlex.quote(self.scratch))]))
        self.require(self.step("stage-harness", ["scp", "-q", __file__, self.args.r_source,
                                                 "{}:{}/harness/".format(self.host, self.scratch)]))

    def exchange(self):
        a = self.args
        cut = self.cut
        self.benv["FN_B3_IMAGE"] = a.image_dir.rstrip("/") + "/fn-host"
        # Mini deployments first: fresh roots, genesis + birth only.
        mini_b = self.mini_deployment("b")
        mini_a = self.mini_deployment("a")

        self.fn("provision", "provision", "--image-dir", a.image_dir,
                "--openssl-prefix", a.openssl_prefix, "--cut", cut,
                "--r-source", self.scratch + "/harness/" + Path(a.r_source).name)
        # Cut a-accepted: A runs the developer image whose feed worker stops
        # (SIGSTOP) after the durable :feed-sent record and before the
        # article bytes reach B (FN_NATIVE_FEED_TEST_STOP_AFTER_SENT).
        if cut == "a-accepted":
            self.fn("start-a-developer", "start", "a", "--developer",
                    "--selector", "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT=1")
        else:
            self.fn("start-a", "start", "a")
        self.fn("start-b", "start", "b")
        self.fn("consumer-setup", "setup")
        ready = self.fn("ready", "ready")["facts"]
        (self.out / "fn-ready.json").write_text(json.dumps(ready, indent=2) + "\n")
        self.mini("bridge-position-a", [self.bridge, "--fn", "consumer", "position",
                                        ready["a_control"], CONSUMER, self.out / "a-registered-via-bridge.fncu"])

        self.fn("r-accept-at-a", "author-r")
        if cut == "a-accepted":
            # A is SIGSTOPped by its own feed worker; it cannot serve a read
            # until killed and restarted, so its durability is read afterwards.
            self.fn("cut-a-stopped-after-sent", "wait-stopped", "a")
            self.fn("cut-r-not-yet-at-b", "absent", "b", "R")
            self.fn("cut-kill-a", "stop", "a", "--signal", "KILL")
            self.fn("cut-restart-a", "start", "a")
        self.fn("r-durable-at-a", "await", "a", "R", "r-at-a.eml", "--timeout", "30")
        # Control: A's own acceptance carries the verdict B must later carry.
        self.fn("a-verdict-r-control", "verdict", "a", "R", "r", "1")
        self.fn("r-peered-to-b", "await", "b", "R", "r-at-b.eml")
        self.fn("r-verified-at-b", "verify", "b", "r-at-b.eml", "r", ready["r_source"])
        self.fn("r-exactly-once", "count", "--expect", "1")
        # The verdict must be in B's completed Store history, not the process.
        self.fn("b-restart-stop", "stop", "b")
        self.fn("b-restart-start", "start", "b")
        self.fn("r-at-b-after-restart", "await", "b", "R", "r-at-b-reopened.eml", "--timeout", "30")
        self.fn("r-at-b-bytes-stable", "same", "b", "r-at-b.eml", "r-at-b-reopened.eml")
        self.fn("b-verdict-gen1", "verdict", "b", "R", "r", "1", "--poll", "b-gen1-poll")
        self.fn("a-drain-own-r", "poll", "a", "a-r", "--message", "R", "--ack")
        self.fn("enroll-q-gen2", "enroll-q")
        self.fn("b-verdict-gen2-and-poll", "verdict", "b", "R", "r", "1", "--poll", "b-preview")

        # Mini consumes R at B.
        b_root = ready["b_root"]
        r_keys = self.fetch_keys(ready["r"], "r")
        for remote, local in ((ready["r_source"], "r.source"),
                              (b_root + "/r-at-b.eml", "r-at-b.eml"),
                              (b_root + "/b-preview.fncu", "b-preview.fncu"),
                              (b_root + "/b-preview.fn-e", "b-preview.fn-e")):
            self.scp_from("fetch-" + local, remote, self.out / local)
        if sha(self.out / "r.source") != R_SOURCE_SHA256:
            raise Stop("fetched R source digest changed")
        r_verified = self.bridge_verify("mini-verify-r-at-b", self.out / "r-at-b.eml",
                                        r_keys["ml_public"])
        r_pin = self.pin(self.bridge, r_keys)
        (self.out / "r-fn-pin.json").write_text(json.dumps(r_pin, sort_keys=True) + "\n")
        fields = self.project("mini-project-b-preview", self.out / "b-preview.fncu",
                              self.out / "b-preview.fn-e")
        (self.out / "b-scope-pin.json").write_text(json.dumps(self.scope(fields)) + "\n")
        L = self.out

        def fresh_decision():
            d = self.json("decision.json")
            return (d.get("storeAdmission") == "observed-control-poll"
                    and d["decision"]["type"] == "proposed-fresh"
                    and (L / "b-live.fncu").read_bytes() == (L / "b-preview.fncu").read_bytes()
                    and (L / "b-live.fn-e").read_bytes() == (L / "b-preview.fn-e").read_bytes())
        self.mini("mini-b-poll-decide", [self.mini_bin, mini_b, "consumer-poll-decide",
                  a.origin_pin, L / "r-fn-pin.json", L / "b-scope-pin.json", a.r_claim,
                  a.policy, ready["b_control"], L / "b-live.fncu", L / "b-live.fn-e",
                  L / "b-live.eml", L / "intent.bin", L / "decision.json"], check=fresh_decision)

        def installed():
            o = self.json("mini-b-attempt/outcome.json")
            return o.get("type") == "confirmed" and o.get("confirmation") == "installed"
        self.mini("mini-b-submit", [self.mini_client, "submit", "--host", self.mini_bin,
                  "--config", mini_b, "--intent", L / "intent.bin", "--intent-kind", "binary",
                  "--key", a.mini_custody_key, "--dir", L / "mini-b-attempt"], check=installed)
        tx = self.json("mini-b-attempt/outcome.json")["transactionId"]
        self.mini("mini-b-export-poll", [self.mini_bin, mini_b, "consumer-export-poll", tx,
                  L / "export.fncu", L / "export.fn-e", L / "export.json"],
                  check=lambda: (L / "export.fncu").read_bytes() == (L / "b-live.fncu").read_bytes())
        self.mini("mini-b-export-reply", [self.mini_bin, mini_b, "consumer-export-reply", tx,
                  L / "reply.bin"])
        # Cut b-verdict: B dies after its verdict is durable and Mini has
        # committed the poll in its own transaction, before Mini's ACK.  The
        # restarted Store must re-deliver the same event at the same cursor
        # (Mini checked b-live == b-preview byte for byte) and not advance.
        if cut == "b-verdict":
            self.fn("cut-kill-b", "stop", "b", "--signal", "KILL")
            self.fn("cut-restart-b", "start", "b")
            self.fn("cut-b-repoll", "poll", "b", "b-repoll", "--message", "R")
            self.fn("cut-b-repoll-cursor-same", "same", "b", "b-preview.fncu", "b-repoll.fncu")
            self.fn("cut-b-repoll-event-same", "same", "b", "b-preview.fn-e", "b-repoll.fn-e")
            self.fn("cut-b-position-unchanged", "position", "b", "b-pos-after-cut.fncu",
                    "--equals", "registered.fncu")
        ack = [self.mini_bin, mini_b, "consumer-ack-poll", L / "r-fn-pin.json",
               L / "b-scope-pin.json", ready["b_control"], tx, L / "b-live.fncu",
               L / "b-live.fn-e"]
        if cut == "ack-response":
            # fn commits the advancing ACK, the bridge loses its reply: Mini must
            # say transport-fault, which this harness records as UNCERTAIN.
            self.ack("cut-ack-response-lost", ack, "ack-lost.json",
                     env=dict(self.benv, FN_E1E2_DROP_ACK_REPLY="1"), want=UNCERTAIN)
            self.mini("cut-ack-settle-position", [self.bridge, "--fn", "consumer", "position",
                      ready["b_control"], CONSUMER, L / "b-position-settled.fncu"],
                      check=lambda: (L / "b-position-settled.fncu").read_bytes() == (L / "b-live.fncu").read_bytes())
        self.ack("mini-b-ack", ack, "ack.json")
        self.mini("b-position-after-ack", [self.bridge, "--fn", "consumer", "position",
                  ready["b_control"], CONSUMER, L / "b-position.fncu"],
                  check=lambda: (L / "b-position.fncu").read_bytes() == (L / "b-live.fncu").read_bytes())

        # Mini signs and posts its reply Q at B.
        q_keys = self.fetch_keys(ready["q"], "q")
        q_pin = self.pin(self.bridge, q_keys)
        (L / "q-fn-pin.json").write_text(json.dumps(q_pin, sort_keys=True) + "\n")
        (L / "q-signer.json").write_text(json.dumps({k: q_pin[k] for k in (
            "principal", "edPublicKey", "mlPublicKeyHex")}, sort_keys=True) + "\n")
        self.mini("mini-q-prepare", [self.mini_bin, mini_b, "consumer-stage-reply-plan",
                  L / "q-signer.json", tx, L / "q-prepared-store", L / "q-prepared-candidate.bin",
                  L / "q-prepared-readback.bin", L / "q-prepared.source", L / "q-prepared.json"],
                  check=lambda: self.json("q-prepared.json").get("stage") == "durable-accepted")
        self.mini("mini-q-sign", [self.mini_bin, mini_b, "consumer-stage-reply-sign",
                  L / "q-fn-pin.json", q_keys["principal"], q_keys["ed_public"],
                  ready["q"]["ed_secret"], ready["q"]["ml_private"], tx,
                  L / "q-prepared-store", L / "q-signed-store", L / "q-plan-readback.bin",
                  L / "q.source", L / "q-preflight-carrier.eml", L / "q-signed-candidate.bin",
                  L / "q-signed-readback.bin", L / "q-ed.sig", L / "q-ml.sig", L / "q-signed.json"],
                  check=lambda: self.json("q-signed.json").get("stage") == "durable-accepted")
        signed = self.json("q-signed.json")
        remote_q = self.scratch + "/harness/q.source"
        self.require(self.step("stage-q-source", ["scp", "-q", L / "q.source",
                                                  self.host + ":" + remote_q]))
        self.fn("register-q", "set-q", signed["messageId"], remote_q)
        if cut == "reply-at-b":
            # B's feed stops after Q's durable :feed-sent, before bytes reach A.
            self.fn("cut-b-to-developer-stop", "stop", "b")
            self.fn("cut-b-developer-start", "start", "b", "--developer",
                    "--selector", "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT=1")
        post = [self.bridge, "--fn", "hybrid-author", ready["b_control"], "2",
                L / "q.source", L / "q-ed.sig", L / "q-ml.sig", q_keys["ml_public"]]
        posted = self.step("q-post-at-b", post, lambda c, t: (
            (ACCEPTED, "exit 0", {}) if c == 0 else
            (UNCERTAIN, "exit {} (fn uncertain)".format(c), {}) if c == 3 else
            (REFUSED, "exit {}".format(c), {})), timeout=180)
        if cut == "reply-at-b":
            # The stop may race the control reply; an unanswered post is UNCERTAIN
            # and is settled only by a read of the restarted Store.
            if posted["outcome"] == REFUSED:
                raise Stop("q-post-at-b was REFUSED")
            self.fn("cut-b-stopped-after-sent", "wait-stopped", "b")
            self.fn("cut-q-not-yet-at-a", "absent", "a", "Q")
            self.fn("cut-kill-b", "stop", "b", "--signal", "KILL")
            self.fn("cut-restart-b", "start", "b")
            self.fn("q-settled-at-b", "await", "b", "Q", "q-at-b.eml", "--timeout", "30")
        else:
            self.require(posted)
            self.fn("q-durable-at-b", "await", "b", "Q", "q-at-b.eml", "--timeout", "30")
        self.fn("q-verified-at-b", "verify", "b", "q-at-b.eml", "q", remote_q)
        self.fn("q-peered-to-a", "await", "a", "Q", "q-at-a.eml")
        self.fn("q-exactly-once", "count", "--expect", "2")

        # Restart both from the same Stores; then Mini reads Q at A.
        for node in ("a", "b"):
            self.fn("restart-{}-stop".format(node), "stop", node)
            self.fn("restart-{}-start".format(node), "start", node)
        self.fn("q-at-a-after-restart", "await", "a", "Q", "q-at-a-reopened.eml", "--timeout", "30")
        self.fn("q-at-a-bytes-stable", "same", "a", "q-at-a.eml", "q-at-a-reopened.eml")
        self.fn("counts-after-restart", "count", "--expect", "2")
        self.fn("a-verdict-q", "verdict", "a", "Q", "q", "2", "--poll", "a-preview",
                "--expect-source", "../harness/q.source")
        a_root = ready["a_root"]
        for remote, local in ((a_root + "/q-at-a-reopened.eml", "q-at-a.eml"),
                              (a_root + "/r-at-a.eml", "r-at-a.eml"),
                              (a_root + "/a-preview.fncu", "a-preview.fncu"),
                              (a_root + "/a-preview.fn-e", "a-preview.fn-e")):
            self.scp_from("fetch-" + local, remote, L / local)
        a_fields = self.project("mini-project-a-preview", L / "a-preview.fncu",
                                L / "a-preview.fn-e")
        (L / "a-scope-pin.json").write_text(json.dumps(self.scope(a_fields)) + "\n")
        (L / "q-claim.json").write_text(json.dumps({
            "sourceIdentity": signed["sourceIdentity"], "messageId": signed["messageId"],
            "groups": GROUP}, sort_keys=True) + "\n")

        def a_fresh():
            d = self.json("a-decision.json")
            return (d.get("decision") == "proposed-fresh"
                    and (L / "a-live.fncu").read_bytes() == (L / "a-preview.fncu").read_bytes())
        self.mini("mini-a-reply-decide", [self.mini_bin, mini_a, "reply-consumer-poll-decide",
                  a.origin_pin, L / "r-fn-pin.json", a.r_claim, L / "r-at-a.eml",
                  L / "q-fn-pin.json", L / "a-scope-pin.json", L / "q-claim.json", a.policy,
                  ready["a_control"], L / "a-live.fncu", L / "a-live.fn-e", L / "a-live.eml",
                  L / "a-intent.bin", L / "a-decision.json"], check=a_fresh)

        def a_installed():
            o = self.json("mini-a-attempt/outcome.json")
            return o.get("type") == "confirmed"
        self.mini("mini-a-submit", [self.mini_client, "submit", "--host", self.mini_bin,
                  "--config", mini_a, "--intent", L / "a-intent.bin", "--intent-kind", "binary",
                  "--key", a.mini_custody_key, "--dir", L / "mini-a-attempt"], check=a_installed)
        a_tx = self.json("mini-a-attempt/outcome.json")["transactionId"]
        self.mini("mini-a-export-result", [self.mini_bin, mini_a, "reply-consumer-export-result",
                  a_tx, L / "a-result.bin", L / "a-inbox.bin", L / "a-export.fncu",
                  L / "a-export.fn-e"],
                  check=lambda: (L / "a-export.fncu").read_bytes() == (L / "a-live.fncu").read_bytes())
        self.ack("mini-a-ack", [self.mini_bin, mini_a, "reply-consumer-ack-poll",
                 L / "q-fn-pin.json", L / "a-scope-pin.json", ready["a_control"], a_tx,
                 L / "a-live.fncu", L / "a-live.fn-e"], "a-ack.json")
        self.mini("a-position-after-ack", [self.bridge, "--fn", "consumer", "position",
                  ready["a_control"], CONSUMER, L / "a-position.fncu"],
                  check=lambda: (L / "a-position.fncu").read_bytes() == (L / "a-live.fncu").read_bytes())
        # No loss, no duplicate: each Store holds exactly R and Q.
        self.fn("final-stop-a", "stop", "a")
        self.fn("final-stop-b", "stop", "b")
        self.fn("final-article-counts", "status", "--expect", "2")

    def finish(self, reason):
        last = next((s for s in reversed(self.steps) if s["outcome"] != ACCEPTED),
                    self.steps[-1] if self.steps else None)
        try:
            self.step("cleanup-owners", ["ssh", self.host, " ".join(shlex.quote(x) for x in (
                "python3", self.scratch + "/harness/two_store_join.py", "fn", "--scratch",
                self.scratch, "cleanup"))])
        except Exception as error:  # still write the summary
            print("cleanup failed: {}".format(error))
        cut_steps = [s["step"] for s in self.steps if s["step"].startswith("cut-")]
        summary = {"cut": self.cut, "cut_reached": bool(cut_steps), "cut_steps": cut_steps,
                   "stopped": reason, "reached": last and last["step"],
                   "reached_outcome": last and last["outcome"], "steps": self.steps}
        (self.out / "summary.json").write_text(json.dumps(summary, indent=2, default=str) + "\n")
        subprocess.run(["scp", "-q", "-r", str(self.logs), str(self.out / "steps.json"),
                        str(self.out / "summary.json"), "{}:{}/".format(self.host, self.scratch)],
                       check=False, timeout=120)
        print("VERDICT cut={} cut_reached={} {}".format(
            self.cut, "yes" if cut_steps else "no", reason), flush=True)


def run_main(argv):
    mini_default = "/Users/ember/dev/minidregg-wt/fn-evidence"
    e2 = "/tmp/mini-fn-e2-native-20260923"
    parser = argparse.ArgumentParser(prog="two_store_join.py run", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--image-dir", required=True,
                        help="frozen image pair dir on the fn host (fn-host, fn-host-developer, freeze/image-pair.sha256)")
    parser.add_argument("--mini-bin", required=True, help="Mini minidregg-host executable (local)")
    parser.add_argument("--mini-sha256", help="refuse unless the Mini executable has this digest")
    parser.add_argument("--scratch", required=True, help="fresh fn-host dir under /tank/fn/scratch/")
    parser.add_argument("--local-out", required=True, help="fresh local evidence dir")
    parser.add_argument("--cut", choices=CUTS, default="none")
    parser.add_argument("--fn-host", default="hbox")
    parser.add_argument("--openssl-prefix", default="/tank/fn/toolchains/openssl-3.5.8")
    parser.add_argument("--mini-repo", default=mini_default)
    parser.add_argument("--mini-client", default=mini_default + "/native/resource-client/target/debug/mini")
    parser.add_argument("--mini-pinned-config", default=e2 + "/live-deployment/pinned-config.json")
    parser.add_argument("--mini-genesis", default=e2 + "/live-deployment/genesis.bin")
    parser.add_argument("--mini-birth-intent", default=e2 + "/live-birth-attempt/intent.json")
    parser.add_argument("--mini-custody-key", default="/tmp/mini-fn-portable-inbox-native-20260923/consumer.key")
    parser.add_argument("--origin-pin", default=e2 + "/fn/origin-pin.json")
    parser.add_argument("--policy", default=e2 + "/policy.json")
    here = Path(__file__).resolve().parent.parent.parent
    parser.add_argument("--r-claim", default=str(here / "tests/fixtures/dregg-e1/portable-p2/source-claim.json"))
    parser.add_argument("--r-source", default=str(here / "tests/fixtures/dregg-e1/source.eml"))
    args = parser.parse_args(argv)
    run = Run(args)
    try:
        run.preflight()
        run.exchange()
        reason = "EXCHANGE COMPLETE"
    except Stop as stop:
        reason = "STOPPED: {}".format(stop)
    except KeyboardInterrupt:
        reason = "STOPPED: interrupted"
    if run.logs.is_dir():
        run.finish(reason)
    else:
        print("VERDICT {}".format(reason))
    return 0 if reason == "EXCHANGE COMPLETE" else 1


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "fn":
        sys.exit(fn_main(sys.argv[2:]))
    if len(sys.argv) > 1 and sys.argv[1] == "run":
        sys.exit(run_main(sys.argv[2:]))
    print("usage: two_store_join.py run --help | fn --scratch DIR <subcommand>", file=sys.stderr)
    sys.exit(5)
