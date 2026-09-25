#!/usr/bin/env python3
"""The mission lab (spike/mission, D28): four native fn nodes on one box.

    python3 tools/mission_lab.py up      provision (once) and start everything
    python3 tools/mission_lab.py status  one screen: nodes, obligations, pins, link
    python3 tools/mission_lab.py demo    tools/mission_demo.py (see --help there)
    python3 tools/mission_lab.py link up|down|state
    python3 tools/mission_lab.py down    stop every PID the lab started

Topology (all on 127.0.0.1; ports in NODES/RELAYS/LINK below):

    A <==NNTP==> B  ~~ r1 ~~[link]~~ r2 ~~  C <==NNTP==> D
                 |                          |
              B-bp store                 C-bp store

A-B and C-D peer over NNTP both ways (STARTTLS, AUTHINFO, streaming).  B and
C each run a second store served by the DTN developer image's `bp-node
serve`; r1 and r2 are dtn7-rs daemons; the link between them is two TCP
proxies that a state file switches (`link down` severs and refuses).

Everything runs from a frozen image directory (FN_MISSION_IMAGES) in a scratch
root (FN_MISSION_ROOT).  On hbox run it under `swarm-build`.  Read
docs/mission-lab.md.

;; SPIKE: defers K6 (one transit decision for NNTP and BP).  The NNTP owner
;; and the BP node each take a store's writer lock, so B and C carry two
;; stores and tools/mission_demo.py bridges them host-side.
"""
from __future__ import annotations

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
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
from nntp_session import Session  # noqa: E402

DTN_EPOCH_UNIX = 946684800
GROUPS = ("fn.mission", "control.cancel")
WILDMAT = "fn.*,control.*"
NODES = {
    "A": dict(nntp=12101, web=12111, peer_login="b-at-a", peers=("B",)),
    "B": dict(nntp=12102, web=12112, peer_login="a-at-b", peers=("A",),
              bp=dict(port=12122, eid="dtn://fn-b/", relay="r1", far="C", role="sender")),
    "C": dict(nntp=12103, web=12113, peer_login="d-at-c", peers=("D",),
              bp=dict(port=12123, eid="dtn://fn-c/", relay="r2", far="B", role="receiver")),
    "D": dict(nntp=12104, web=12114, peer_login="c-at-d", peers=("C",)),
}
RELAYS = {
    "r1": dict(cla=12131, web=12141, side="B", other="r2"),
    "r2": dict(cla=12132, web=12142, side="C", other="r1"),
}
# The link: r1 dials r2 through LINK["r1->r2"], r2 dials r1 through LINK["r2->r1"].
LINK = {"r1->r2": dict(listen=12151, target="r2"), "r2->r1": dict(listen=12152, target="r1")}
HUMAN = "ember"
BP_LIFETIME, BP_CRC, BP_HOPS, BP_MRU, BP_WALL_ERROR = "3600000", "2", "32", "1048576", "60000"


def sha256(data) -> str:
    if isinstance(data, (str, Path)):
        data = Path(data).read_bytes() if Path(data).exists() else b""
    return hashlib.sha256(data).hexdigest()


def dtn_wall_ms() -> str:
    return str(int((time.time() - DTN_EPOCH_UNIX) * 1000))


def utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


class LabError(RuntimeError):
    pass


class Lab:
    def __init__(self, root: Path, images: Path, dtn7: Path):
        self.root = root
        self.images = images
        self.dtn7 = dtn7
        self.state_path = root / "lab.json"
        self.state = json.loads(self.state_path.read_text()) if self.state_path.exists() else {}
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        for key in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "SBCL_USER_ARGS"):
            self.env.pop(key, None)
        # A production image refuses to start under any developer selector.
        for key in list(self.env):
            if key.startswith(("FN_NATIVE_", "FN_BP_TEST", "FN_TEST_")):
                self.env.pop(key)

    # -- persistence ----------------------------------------------------------
    def save(self):
        self.state_path.write_text(json.dumps(self.state, indent=1, sort_keys=True))

    def image(self, kind="developer") -> Path:
        name = {"production": "fn-host", "developer": "fn-host-developer",
                "dtn": "fn-host-dtn", "dtn-developer": "fn-host-dtn-developer"}[kind]
        path = self.images / name
        if not path.exists():
            raise LabError(f"no image {path}")
        return path

    def openssl(self) -> str:
        """An OpenSSL with ML-DSA-65 (>= 3.5).  The frozen image ships only
        the libraries, so the toolchain prefix supplies the binary; the
        binary needs its own libraries ahead of the system's 3.3."""
        for prefix in (os.environ.get("FN_OPENSSL_PREFIX"),
                       "/tank/fn/toolchains/openssl-3.5.8"):
            if prefix and (Path(prefix) / "bin" / "openssl").exists():
                self.env["LD_LIBRARY_PATH"] = "{0}/lib64:{0}/lib".format(prefix)
                return str(Path(prefix) / "bin" / "openssl")
        return "openssl"

    def run_openssl(self, *args):
        return subprocess.run([self.openssl(), *map(str, args)], check=True,
                              capture_output=True, timeout=120, env=self.env)

    def node_dir(self, name) -> Path:
        return self.root / name

    # -- running the image ----------------------------------------------------
    def fn(self, kind, *args, stdin=None, check=True, timeout=300, log=None):
        argv = [str(self.image(kind)), "--fn", *map(str, args)]
        result = subprocess.run(argv, input=stdin, capture_output=True, timeout=timeout,
                                env=self.env, cwd=str(ROOT))
        record = dict(argv=argv[1:], rc=result.returncode,
                      stdout=result.stdout.decode("utf-8", "replace"),
                      stderr=result.stderr.decode("utf-8", "replace"))
        if log is not None:
            with open(log, "a") as handle:
                handle.write(json.dumps(dict(at=utc(), **record)) + "\n")
        if check and result.returncode != 0:
            raise LabError("{} exit {}\n{}{}".format(
                " ".join(argv[1:]), result.returncode, record["stdout"], record["stderr"]))
        return record

    def spawn(self, tag, argv, stdout: Path, stderr: Path | None = None, env=None):
        stdout.parent.mkdir(parents=True, exist_ok=True)
        out = stdout.open("ab")
        err = (stderr.open("ab") if stderr else subprocess.STDOUT)
        proc = subprocess.Popen([str(a) for a in argv], stdout=out, stderr=err,
                                stdin=subprocess.DEVNULL, env=env or self.env, cwd=str(ROOT),
                                start_new_session=True)
        self.state.setdefault("pids", {})[tag] = dict(
            pid=proc.pid, argv=[str(a) for a in argv], stdout=str(stdout), started=utc())
        self.save()
        return proc

    def alive(self, tag) -> bool:
        entry = self.state.get("pids", {}).get(tag)
        if not entry:
            return False
        try:
            os.kill(entry["pid"], 0)
        except OSError:
            return False
        try:
            cmdline = Path(f"/proc/{entry['pid']}/cmdline").read_bytes().split(b"\0")
            return entry["argv"][0].encode() in cmdline[:3] or True
        except OSError:
            return True

    def stop(self, tag, grace=30.0):
        entry = self.state.get("pids", {}).get(tag)
        if not entry:
            return None
        pid = entry["pid"]
        how = "absent"
        if self.alive(tag):
            os.kill(pid, signal.SIGTERM)
            how = "SIGTERM"
            deadline = time.monotonic() + grace
            while time.monotonic() < deadline and self.alive(tag):
                time.sleep(0.2)
            if self.alive(tag):
                os.kill(pid, signal.SIGKILL)
                how = "SIGKILL"
                time.sleep(0.5)
        self.state.setdefault("stopped", []).append(dict(tag=tag, pid=pid, how=how, at=utc()))
        del self.state["pids"][tag]
        self.save()
        return how

    @staticmethod
    def wait_for(path: Path, pattern: str, timeout: float, start=0):
        deadline = time.monotonic() + timeout
        regex = re.compile(pattern)
        while True:
            if path.exists():
                text = path.read_text("utf-8", "replace")[start:]
                match = regex.search(text)
                if match:
                    return match
            if time.monotonic() > deadline:
                raise LabError(f"timeout waiting for /{pattern}/ in {path}")
            time.sleep(0.2)

    # -- NNTP -----------------------------------------------------------------
    def tls_context(self, name) -> ssl.SSLContext:
        context = ssl.create_default_context(cafile=str(self.node_dir(name) / "cert.pem"))
        context.check_hostname = True
        return context

    def session(self, name, login=HUMAN, wire=None) -> Session:
        node = self.state["nodes"][name]
        session = Session("127.0.0.1", node["nntp"], 30.0)
        trace = []
        original_line, original_send = session.line, session.send

        def line():
            text = original_line()
            trace.append("S: " + text)
            return text

        def send(text):
            shown = re.sub(r"^(AUTHINFO PASS) .*", r"\1 ********", text)
            trace.append("C: " + shown)
            original_send(text)

        session.line, session.send = line, send
        session.trace = trace
        # The constructor already read the greeting.
        trace.append("S: " + session.greeting)
        if not session.greeting.startswith("20"):
            raise LabError(f"{name}: greeting {session.greeting}")
        session.cmd("STARTTLS")
        session.upgrade(self.tls_context(name))
        session.login(login, node["passwords"][login])
        if wire is not None:
            wire.extend(trace)
        return session

    # -- provisioning ---------------------------------------------------------
    def provision(self):
        if self.state.get("provisioned"):
            return
        self.root.mkdir(parents=True, exist_ok=True)
        self.state["images"] = str(self.images)
        self.state["image_sha256"] = sha256(self.images / "image.sha256")
        self.state["nodes"] = {}
        setup = self.root / "setup.jsonl"
        for name, spec in NODES.items():
            self.state["nodes"][name] = self.provision_node(name, spec, setup)
        for name, spec in NODES.items():
            for peer in spec["peers"]:
                self.peer(name, peer, setup)
        self.state["author"] = self.signer(self.root / "author", "author", 0x41)
        for name in ("B", "C"):
            self.provision_bp(name, setup)
        self.provision_link()
        self.state["provisioned"] = utc()
        self.save()

    def provision_node(self, name, spec, setup):
        d = self.node_dir(name)
        d.mkdir(parents=True, exist_ok=True)
        cert, key = d / "cert.pem", d / "key.pem"
        self.run_openssl("req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256", "-days", "3",
                         "-subj", "/CN=localhost", "-addext",
                         "subjectAltName=DNS:localhost,IP:127.0.0.1", "-keyout", key, "-out", cert)
        key.chmod(0o600)
        store, control, log = d / "store", d / "control.sock", d / "fn.log"
        self.fn("developer", "store", store, "init", *GROUPS, log=setup)
        config = d / "fn.toml"
        config.write_text(
            f'[store]\npath = "{store}"\n[listener]\nhost = "127.0.0.1"\nport = {spec["nntp"]}\n'
            f'tls_cert = "{cert}"\ntls_key = "{key}"\n'
            f'[auth]\nrequired = true\nprotected_only = true\npath = "{d / "auth.toml"}"\n'
            f'[posting]\nenabled = true\n[control]\npath = "{control}"\n[log]\npath = "{log}"\n')
        self.fn("developer", "operator", config, "policy", "set", "path-identity",
                f"{name.lower()}.mission.invalid", log=setup)
        passwords = {}
        for login in (spec["peer_login"], HUMAN):
            password = secrets.token_urlsafe(18)
            passwords[login] = password
            self.fn("developer", "operator", config, "principal", "set-password", login,
                    "--posting", stdin=f"{password}\n{password}\n".encode(), log=setup)
        listed = self.fn("developer", "operator", config, "principal", "list", log=setup)["stdout"]
        principals = {}
        for line in listed.splitlines():
            match = re.search(r"([0-9a-f]{64})", line)
            if match:
                login = line.split()[0]
                principals[login] = match.group(1)
        if set(principals) < set(passwords):
            raise LabError(f"{name}: principal list did not name every login: {listed}")
        (d / "passwords.json").write_text(json.dumps(passwords))
        (d / "passwords.json").chmod(0o600)
        return dict(name=name, nntp=spec["nntp"], web=spec["web"], dir=str(d), store=str(store),
                    config=str(config), control=str(control), log=str(log), cert=str(cert),
                    peer_login=spec["peer_login"], passwords=passwords, principals=principals,
                    path_identity=f"{name.lower()}.mission.invalid")

    def peer(self, source, target, setup):
        s, t = self.state["nodes"][source], self.state["nodes"][target]
        profile = Path(s["dir"]) / f"{target}.fnauth"
        profile.write_bytes(f"FNAUTH1\n{t['peer_login']}\n{t['passwords'][t['peer_login']]}\n".encode())
        profile.chmod(0o600)
        self.fn("developer", "operator", s["config"], "peer", "add", target, t["path_identity"],
                "127.0.0.1", t["nntp"], WILDMAT, WILDMAT, "principal",
                s["principals"][s["peer_login"]], profile, "false", "true", "starttls",
                "localhost", t["cert"], log=setup)

    def signer(self, d: Path, label, principal_byte):
        from cryptography.hazmat.primitives import serialization
        from cryptography.hazmat.primitives.asymmetric import ed25519
        d.mkdir(parents=True, exist_ok=True)
        key = ed25519.Ed25519PrivateKey.generate()
        seed = key.private_bytes(serialization.Encoding.Raw, serialization.PrivateFormat.Raw,
                                 serialization.NoEncryption())
        public = key.public_key().public_bytes(serialization.Encoding.Raw,
                                               serialization.PublicFormat.Raw)
        paths = {k: str(d / f"{label}-{suffix}") for k, suffix in (
            ("principal", "principal.bin"), ("ed_public", "ed-public.bin"),
            ("ed_secret", "ed-secret.bin"), ("ml_private", "ml-private.pem"),
            ("ml_public", "ml-public.pem"))}
        Path(paths["principal"]).write_bytes(bytes([principal_byte]) * 32)
        Path(paths["ed_public"]).write_bytes(public)
        Path(paths["ed_secret"]).write_bytes(seed + public)
        Path(paths["ed_secret"]).chmod(0o600)
        self.run_openssl("genpkey", "-algorithm", "ML-DSA-65", "-out", paths["ml_private"])
        self.run_openssl("pkey", "-in", paths["ml_private"], "-pubout", "-out", paths["ml_public"])
        paths["principal_hex"] = (bytes([principal_byte]) * 32).hex()
        return paths

    def provision_bp(self, name, setup):
        node = self.state["nodes"][name]
        spec = NODES[name]["bp"]
        relay = RELAYS[spec["relay"]]
        far = NODES[spec["far"]]["bp"]
        d = Path(node["dir"]) / "bp"
        d.mkdir(exist_ok=True)
        store = d / "store"
        self.fn("dtn-developer", "store", store, "init", *GROUPS, log=setup)
        config = d / "bp.toml"
        config.write_text(f'[store]\npath = "{store}"\n')
        self.fn("dtn-developer", "operator", config, "policy", "set", "path-identity",
                f"{name.lower()}-bp.mission.invalid", log=setup)
        # The relay is the neighbour: it carries the far fn node's bundles.
        # B requests and is released by C's receipts (`releases-for`, D23);
        # C receives requests and issues receipts.  The two shapes are the
        # app-receipt lab's sender and receiver (tests/bp-dtn7).
        sender = spec.get("role", "sender") == "sender"
        self.fn("dtn-developer", "operator", config, "bp-boundary", "add", spec["relay"],
                f"{spec['relay']}.mission.invalid", f"dtn://dtn7-{spec['relay']}/", relay["cla"],
                "carries", far["eid"], *(["releases-for", far["eid"]] if sender else []), log=setup)
        # The far node under its own EID, on a port nothing listens on; the
        # receiver judges the carried requests under this scope.
        scope = self.state.setdefault("bp_scope", {})
        far_port = 12190 + (0 if name == "B" else 1)
        candidates = ([[]] if sender else
                      [["fn.mission", "32768", "16"], [WILDMAT, "32768", "16"]])
        for candidate in candidates:
            record = self.fn("dtn-developer", "operator", config, "bp-boundary", "add",
                             f"{spec['far'].lower()}-author", f"{spec['far'].lower()}.mission.invalid",
                             far["eid"], far_port, *candidate, check=False, log=setup)
            if record["rc"] == 0:
                scope[name] = candidate
                break
        else:
            raise LabError(f"{name}: no bp-boundary scope accepted")
        route = self.fn("dtn-developer", "operator", config, "bp-route", "add", far["eid"] + "*",
                        spec["relay"], check=False, log=setup)
        if route["rc"] != 0:
            # An image before the routing lane (2026-09-25) has no bp-route
            # verb; `bp-node serve` then forwards nothing on its own.
            self.state.setdefault("findings", []).append(dict(
                at=utc(), node=name, what="bp-route add refused",
                line=(route["stdout"] + route["stderr"]).strip()))
        wf, fnbs, rj = d / "workflow.fnwf", d / "service.fnbs", d / "receipts.fnrj"
        if sender:
            self.fn("dtn-developer", "app-journal", "workflow-init", store, wf, spec["eid"], far["eid"],
                    "native-policy", far["eid"], BP_LIFETIME, "origin-native", "wire-auth", log=setup)
        node["bp"] = dict(dir=str(d), store=str(store), config=str(config), workflow=str(wf),
                          service=str(fnbs), receipts=str(rj), port=spec["port"], eid=spec["eid"],
                          far_eid=far["eid"], relay=spec["relay"], contact=relay["cla"],
                          sequence=0, works=[])
        self.enroll_author_in_bp_store(name, setup)

    def enroll_author_in_bp_store(self, name, setup):
        """The keyring is a store record and `hybrid-enroll` needs an owner's
        control socket; the DTN image has none.  A developer owner serves the
        BP store for the enrolment only, then stops."""
        node = self.state["nodes"][name]
        bp = node["bp"]
        d = Path(bp["dir"])
        control, config = d / "control.sock", d / "owner.toml"
        port = 12180 + (1 if name == "B" else 2)
        config.write_text(f'[store]\npath = "{bp["store"]}"\n[listener]\nhost = "127.0.0.1"\n'
                          f'port = {port}\n[control]\npath = "{control}"\n'
                          f'[log]\npath = "{d / "owner.log"}"\n')
        out = d / "owner.stdout"
        self.spawn(f"bp-owner-{name}", [self.image("developer"), "--fn", "operator", config, "run"], out)
        try:
            self.wait_for(out, rf"LISTENING {port}", 120)
            author = self.state["author"]
            record = self.fn("developer", "hybrid-enroll", control, "1", author["principal"],
                             author["ed_public"], author["ml_public"], log=setup)
            bp["author_enrolled"] = dict(at=utc(), stdout=record["stdout"].strip())
        finally:
            self.stop(f"bp-owner-{name}")

    def provision_link(self):
        d = self.root / "link"
        d.mkdir(exist_ok=True)
        (d / "state").write_text("up\n")
        self.state["link"] = dict(dir=str(d), state=str(d / "state"), log=str(d / "link.log"))

    # -- starting and stopping -------------------------------------------------
    def start_owner(self, name):
        node = self.state["nodes"][name]
        if self.alive(f"owner-{name}"):
            return
        d = Path(node["dir"])
        out = d / "owner.stdout"
        start = len(out.read_bytes()) if out.exists() else 0
        self.spawn(f"owner-{name}", [self.image("developer"), "--fn", "operator", node["config"], "run"],
                   out, d / "owner.stderr")
        self.wait_for(out, rf"LISTENING {node['nntp']}", 120, start)

    def start_web(self, name):
        node = self.state["nodes"][name]
        if self.alive(f"web-{name}"):
            return
        env = dict(self.env, FN_CLIENT_PASSWORD=node["passwords"][HUMAN])
        self.spawn(f"web-{name}", [sys.executable, str(HERE / "fn_web.py"), "--node",
                                    f"127.0.0.1:{node['nntp']}", "--tls-cert", node["cert"],
                                    "--user", HUMAN, "--port", node["web"],
                                    "--outbox", str(Path(node["dir"]) / "web-outbox"),
                                    "--marks", str(Path(node["dir"]) / "web-marks.json")],
                   Path(node["dir"]) / "web.log", env=env)

    def enroll_author(self, name):
        node = self.state["nodes"][name]
        if node.get("author_enrolled"):
            return
        author = self.state["author"]
        record = self.fn("developer", "hybrid-enroll", node["control"], "1", author["principal"],
                         author["ed_public"], author["ml_public"], log=self.root / "setup.jsonl")
        node["author_enrolled"] = dict(at=utc(), stdout=record["stdout"].strip())
        self.save()

    def relay_routes(self, name) -> Path:
        """dtn7 static routes (`idx src dst via`, globbed): the far node's
        bundles cross the link, the near node's come home.  Epidemic routing
        would also echo every bundle back to its sender (seen 2026-09-25)."""
        spec = RELAYS[name]
        side = self.state["nodes"][spec["side"]]["bp"]
        path = self.root / "relays" / f"{name}.routes"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"1 {side['eid']}* {side['far_eid']}* dtn://dtn7-{spec['other']}/\n"
                        f"2 {side['far_eid']}* {side['eid']}* {side['eid']}\n")
        return path

    def relay_argv(self, name):
        spec = RELAYS[name]
        side = self.state["nodes"][spec["side"]]["bp"]
        link = LINK[f"{name}->{spec['other']}"]["listen"]
        return [self.dtn7 / "target" / "release" / "dtnd", "-n", f"dtn7-{name}",
                "-W", self.root / "relays" / name, "-D", "sled", "-C", f"tcp:port={spec['cla']}",
                "-w", spec["web"], "-i", "0", "-j", "5s", "-p", "1h", "--disable_nd", "-d",
                "-r", "static", "-R", f"static.routes={self.relay_routes(name)}",
                "-s", f"tcp://127.0.0.1:{link}/dtn7-{spec['other']}",
                "-s", f"tcp://127.0.0.1:{side['port']}/{side['eid'][6:-1]}"]

    def start_relay(self, name):
        if self.alive(f"relay-{name}"):
            return
        (self.root / "relays" / name).mkdir(parents=True, exist_ok=True)
        self.spawn(f"relay-{name}", self.relay_argv(name), self.root / "relays" / f"{name}.log")
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            try:
                with socket.create_connection(("127.0.0.1", RELAYS[name]["web"]), 1.0):
                    return
            except OSError:
                time.sleep(0.3)
        raise LabError(f"relay {name} did not open its web port")

    def start_link(self):
        if self.alive("link"):
            return
        self.spawn("link", [sys.executable, str(HERE / "mission_lab.py"), "--root", self.root,
                            "--images", self.images, "--dtn7", self.dtn7, "link-serve"],
                   Path(self.state["link"]["log"]))
        time.sleep(0.5)

    def bp_serve_argv(self, name):
        bp = self.state["nodes"][name]["bp"]
        return [self.image("dtn-developer"), "--fn", "bp-node", "serve", bp["port"], bp["service"],
                bp["store"], bp["receipts"], bp["workflow"], bp["eid"], bp["far_eid"], bp["eid"],
                "native-policy", bp["eid"], "127.0.0.1", bp["contact"], "0", BP_LIFETIME, BP_CRC,
                BP_HOPS, BP_MRU, dtn_wall_ms(), BP_WALL_ERROR]

    def start_bp_serve(self, name):
        if self.alive(f"bp-{name}"):
            return
        bp = self.state["nodes"][name]["bp"]
        log = Path(bp["dir"]) / "serve.log"
        start = len(log.read_bytes()) if log.exists() else 0
        self.spawn(f"bp-{name}", self.bp_serve_argv(name), log)
        self.wait_for(log, r"BP NODE LISTENING", 120, start)

    def up(self):
        self.provision()
        for name in NODES:
            self.start_owner(name)
        for name in NODES:
            self.enroll_author(name)
        for name in NODES:
            self.start_web(name)
        self.start_link()
        for name in RELAYS:
            self.start_relay(name)
        for name in ("C", "B"):
            self.start_bp_serve(name)
        self.state["up"] = utc()
        self.save()

    def down(self):
        order = [t for t in self.state.get("pids", {}) if t.startswith("web-")]
        order += [t for t in self.state.get("pids", {}) if t.startswith("bp-")]
        order += [t for t in self.state.get("pids", {}) if t.startswith("relay-")]
        order += [t for t in self.state.get("pids", {}) if t == "link"]
        order += [t for t in self.state.get("pids", {}) if t.startswith("owner-")]
        order += [t for t in list(self.state.get("pids", {})) if t not in order]
        report = {}
        for tag in order:
            report[tag] = self.stop(tag)
        self.state["down"] = utc()
        self.save()
        return report

    # -- the link ---------------------------------------------------------------
    def link_state(self) -> str:
        path = Path(self.state["link"]["state"])
        return path.read_text().strip() if path.exists() else "unknown"

    def set_link(self, state):
        path = Path(self.state["link"]["state"])
        path.write_text(state + "\n")
        with open(self.state["link"]["log"], "a") as handle:
            handle.write(f"{utc()} link {state} (operator)\n")

    def link_serve(self):
        """Two proxies; the state file says whether they listen.  A `down`
        closes the listeners (dials are refused) and severs live sessions."""
        log = open(self.state["link"]["log"], "a", buffering=1)
        proxies = {}
        for name, spec in LINK.items():
            proxies[name] = Proxy(name, spec["listen"], RELAYS[spec["target"]]["cla"], log)
        current = None
        while True:
            state = self.link_state()
            if state != current:
                log.write(f"{utc()} link {state}\n")
                for proxy in proxies.values():
                    proxy.set(state == "up")
                current = state
            time.sleep(0.25)


class Proxy:
    def __init__(self, name, listen, target, log):
        self.name, self.listen_port, self.target, self.log = name, listen, target, log
        self.listener = None
        self.sessions = []
        self.lock = threading.Lock()
        self.thread = None

    def set(self, up: bool):
        with self.lock:
            if up and self.listener is None:
                self.listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                self.listener.bind(("127.0.0.1", self.listen_port))
                self.listener.listen(8)
                self.thread = threading.Thread(target=self.accept_loop, args=(self.listener,),
                                               daemon=True)
                self.thread.start()
            elif not up and self.listener is not None:
                listener, self.listener = self.listener, None
                try:
                    listener.close()
                except OSError:
                    pass
                for pair in list(self.sessions):
                    for s in pair:
                        try:
                            s.shutdown(socket.SHUT_RDWR)
                        except OSError:
                            pass
                        try:
                            s.close()
                        except OSError:
                            pass
                self.log.write(f"{utc()} {self.name} severed {len(self.sessions)} session(s)\n")
                self.sessions.clear()

    def accept_loop(self, listener):
        while True:
            try:
                client, address = listener.accept()
            except OSError:
                return
            try:
                upstream = socket.create_connection(("127.0.0.1", self.target), 10.0)
            except OSError as error:
                self.log.write(f"{utc()} {self.name} dial {self.target} failed: {error}\n")
                client.close()
                continue
            self.log.write(f"{utc()} {self.name} session {address[1]}->{self.target}\n")
            pair = (client, upstream)
            with self.lock:
                self.sessions.append(pair)
            threading.Thread(target=self.pump, args=(pair,), daemon=True).start()

    def pump(self, pair):
        client, upstream = pair
        moved = 0
        try:
            while True:
                ready, _, _ = select.select([client, upstream], [], [], 60.0)
                if not ready:
                    continue
                for s in ready:
                    data = s.recv(65536)
                    if not data:
                        return
                    (upstream if s is client else client).sendall(data)
                    moved += len(data)
        except OSError:
            return
        finally:
            for s in pair:
                try:
                    s.close()
                except OSError:
                    pass
            with self.lock:
                if pair in self.sessions:
                    self.sessions.remove(pair)
            self.log.write(f"{utc()} {self.name} session closed after {moved} octets\n")


def parser():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--root", type=Path, default=Path(os.environ.get(
        "FN_MISSION_ROOT", "/tank/fn/scratch/spike-mission/lab")))
    p.add_argument("--images", type=Path, default=Path(os.environ.get("FN_MISSION_IMAGES", "")))
    p.add_argument("--dtn7", type=Path, default=Path(os.environ.get("FN_MISSION_DTN7", "/tank/fn/dtn7/repo")))
    p.add_argument("command", choices=["up", "down", "status", "demo", "link", "link-serve"])
    p.add_argument("rest", nargs=argparse.REMAINDER)
    return p


def main(argv=None) -> int:
    args = parser().parse_args(argv)
    if not str(args.images):
        print("set FN_MISSION_IMAGES or --images to a frozen image directory", file=sys.stderr)
        return 2
    lab = Lab(args.root, args.images, args.dtn7)
    if args.command == "up":
        lab.up()
        print(json.dumps(dict(up=lab.state["up"], root=str(lab.root), images=str(lab.images),
                              pids={k: v["pid"] for k, v in lab.state["pids"].items()}), indent=1))
    elif args.command == "down":
        print(json.dumps(lab.down(), indent=1))
    elif args.command == "link":
        if args.rest and args.rest[0] in ("up", "down"):
            lab.set_link(args.rest[0])
        print(f"link {lab.link_state()}")
    elif args.command == "link-serve":
        lab.link_serve()
    elif args.command == "status":
        import mission_status
        return mission_status.main(lab, args.rest)
    elif args.command == "demo":
        import mission_demo
        return mission_demo.main(lab, args.rest)
    return 0


if __name__ == "__main__":
    # Run from the module namespace, so the demo and status modules that
    # import mission_lab see the same Lab and LabError classes.
    import mission_lab
    sys.exit(mission_lab.main())
