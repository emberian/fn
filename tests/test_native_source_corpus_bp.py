"""Opt-in native witness: the source corpus carried by BP through a dtn7-rs
relay keeps its authored source (the Fable mandate section 5.3; D25, D32;
PRF-127; SCN-073).

Topology, loopback, every process started and stopped by PID:

    fn A (`store post`, `bp-obligation request`)
        --> dtn7 relay (sled store) --[byte relay]--> fn B (`bp-node serve`)

A is the injecting node (path identity sender.bp.gate.invalid) and B the
receiving one (receiver.bp.gate.invalid).  Each element of
tests/fixtures/source-corpus is POSTed to A's NNTP owner (the served POST,
fn-inj-decide), and a durable forwarding obligation (FNWF) is undertaken
for each accepted one; `bp-obligation
request` publishes ACL2's kind-8 attempt and hands ACL2's request ADU to A's
FNBS carrier.  B admits the bundle on the carried-author boundary (D23),
takes kind-5 custody and runs the request through fn-bpaj-transit-plan, so
what B stores is fn-peer-relayed-octets of A's article.  The signed element
is the dual-signature carrier `hybrid-sign-carrier` renders from
signed.article, POSTed as the corpus test's carrier route; its author is
enrolled at both nodes (D23).

The last element's transfer into B is held mid-bundle by the byte relay and
B is SIGKILLed by PID while it is held; B restarts and the dtn7 relay is
restarted over its sled store, which re-forwards the held bundle.  After
every element is delivered, B is SIGKILLed once more (idle) and reopened.

Every decision is an image's; Python observes replies, logs and bytes:

  * the kind-8 attempt: A's own `BP obligation request durable attempt` line;
  * the bundle identity: source EID, creation time and sequence number, read
    from the primary block (RFC 9171 section 4.3.1) of the bundle B retained
    in its kind-5 frame; an observation, compared with nothing ACL2 decides;
  * the stored representation: the record each node's owner serves by
    Message-ID (ARTICLE, equal to `store inspect`, NNT-020).  B's record
    must be A's with `receiver.bp.gate.invalid!!` spliced after `Path: `
    (RFC 5537 section 3.2.1: an empty diagnostic marks the verified hop) and
    nothing else changed.

The table is printed as one `SOURCE-CORPUS-BP-TABLE <json>` line.

Run: FN_NATIVE_DTN_HOST=<fn-host-dtn-developer> FN_NATIVE_HOST=<fn-host-developer>
     FN_DTN7_REPO=<dtn7-rs checkout> python3 -m unittest tests.test_native_source_corpus_bp
"""

import hashlib
import json
import os
from pathlib import Path
import re
import select
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "tests" / "fixtures" / "source-corpus"
IMAGE_TEXT = os.environ.get("FN_NATIVE_DTN_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
# The DTN image has no NNTP owner and no signing verbs.  The default
# developer image of the same tree is each node's NNTP owner over the same
# Store (A's served POST injects; enrollment; the record read back by
# ARTICLE, which equals `store inspect', NNT-020) and renders the carrier.
DEV_TEXT = os.environ.get("FN_NATIVE_HOST")
SIGN_IMAGE = Path(DEV_TEXT) if DEV_TEXT else None
REPO_TEXT = os.environ.get("FN_DTN7_REPO")
REPO = Path(REPO_TEXT) if REPO_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK)
             and SIGN_IMAGE is not None and SIGN_IMAGE.is_file()
             and REPO is not None and (REPO / "target/release/dtnd").is_file())
SENDER, RECEIVER = "dtn://sender/", "dtn://receiver/"
A_ID, B_ID = "sender.bp.gate.invalid", "receiver.bp.gate.invalid"
DTN_EPOCH_UNIX = 946684800
ELEMENTS = ("supplied-date", "generated-date", "client-path", "xref", "unknown-headers",
            "mime", "legacy", "signed")
ED_PUBLIC = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
ED_SECRET = "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60" + ED_PUBLIC


def sha(data):
    return hashlib.sha256(data).hexdigest()


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def header(article, name):
    for line in article.split(b"\r\n\r\n", 1)[0].split(b"\r\n"):
        if line.lower().startswith(name.lower() + b":"):
            return line.split(b":", 1)[1].strip().decode("ascii", "replace")
    return None


def spliced(octets, identity):
    """A's record with B's Path update: `<identity>!!' after `Path: '."""
    head = b"Path: "
    at = 0 if octets.startswith(head) else octets.find(b"\r\n" + head) + 2
    if at < 0 or octets.find(b"\r\n\r\n") < at:
        return None
    cut = at + len(head)
    return octets[:cut] + identity.encode() + b"!!" + octets[cut:]


# -- a read-only view of a bundle's primary block (RFC 9171 section 4.3.1) ----
def cbor_item(data, at):
    """(value, next) for the CBOR subset a primary block uses."""
    first = data[at]
    major, info = first >> 5, first & 31
    at += 1
    if info < 24:
        value = info
    elif info in (24, 25, 26, 27):
        width = 1 << (info - 24)
        value = int.from_bytes(data[at:at + width], "big")
        at += width
    else:
        raise ValueError("indefinite item in a primary block")
    if major == 0:
        return value, at
    if major in (2, 3):
        return bytes(data[at:at + value]), at + value
    if major == 4:
        items = []
        for _ in range(value):
            item, at = cbor_item(data, at)
            items.append(item)
        return items, at
    raise ValueError("unexpected CBOR major type {}".format(major))


def eid_text(eid):
    if isinstance(eid, list) and len(eid) == 2 and eid[0] == 1:
        return "dtn:" + (eid[1].decode() if isinstance(eid[1], bytes) else "none")
    if isinstance(eid, list) and len(eid) == 2 and eid[0] == 2:
        return "ipn:{}.{}".format(*eid[1])
    return repr(eid)


def bundle_identity(frame):
    """(source EID, creation time ms, sequence) of the first BPv7 bundle in
    FRAME, found by its opening octets (indefinite array, primary block of 8
    to 11 items, version 7)."""
    for head in (b"\x9f\x88\x07", b"\x9f\x89\x07", b"\x9f\x8a\x07", b"\x9f\x8b\x07"):
        at = frame.find(head)
        if at < 0:
            continue
        try:
            block, _ = cbor_item(frame, at + 1)
        except (ValueError, IndexError):
            continue
        if len(block) >= 8 and block[0] == 7:
            return {"source": eid_text(block[4]), "destination": eid_text(block[3]),
                    "creation_ms": block[6][0], "sequence": block[6][1]}
    return None


class HoldRelay:
    """Forward bytes both ways; once armed, stop forwarding the client's bytes
    after `hold_after` of them.  It never answers a protocol message."""

    def __init__(self, target):
        self.listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(8)
        self.listener.settimeout(0.2)
        self.port = self.listener.getsockname()[1]
        self.target, self.hold_after = target, None
        self.held = threading.Event()
        self.stopped = threading.Event()
        threading.Thread(target=self._accept, daemon=True).start()

    def arm(self, hold_after):
        self.hold_after = hold_after
        self.held.clear()

    def _accept(self):
        while not self.stopped.is_set():
            try:
                client, _ = self.listener.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            threading.Thread(target=self._exchange, args=(client,), daemon=True).start()

    def _exchange(self, client):
        sent = 0
        with client:
            try:
                upstream = socket.create_connection(("127.0.0.1", self.target), 5)
            except OSError:
                return
            with upstream:
                deadline = time.monotonic() + 120
                while time.monotonic() < deadline and not self.stopped.is_set():
                    readable, _, _ = select.select((client, upstream), (), (), 0.2)
                    for source in readable:
                        try:
                            data = source.recv(65536)
                        except OSError:
                            return
                        if not data:
                            return
                        target = upstream if source is client else client
                        if source is client and self.hold_after is not None \
                                and sent + len(data) > self.hold_after:
                            data = data[:max(0, self.hold_after - sent)]
                            self.hold_after = None
                            try:
                                upstream.sendall(data)
                            except OSError:
                                pass
                            self.held.set()
                            upstream.settimeout(60)
                            try:
                                while upstream.recv(65536):
                                    pass
                            except OSError:
                                pass
                            return
                        if source is client:
                            sent += len(data)
                        try:
                            target.sendall(data)
                        except OSError:
                            return

    def close(self):
        self.stopped.set()
        self.listener.close()


class Dtnd:
    def __init__(self, work, name, cla_port, peers):
        self.bin = REPO / "target/release/dtnd"
        self.work = work / name
        self.work.mkdir(parents=True, exist_ok=True)
        self.name, self.cla_port, self.web_port = name, cla_port, free_port()
        self.peers, self.proc, self.starts = peers, None, []

    def start(self):
        cmd = [str(self.bin), "-n", self.name, "-W", str(self.work), "-D", "sled",
               "-C", "tcp:port={}".format(self.cla_port), "-w", str(self.web_port),
               "-i", "0", "--disable_nd", "-d"]
        for peer in self.peers:
            cmd += ["-s", peer]
        log = self.work / "dtnd-{}.log".format(len(self.starts))
        self.proc = subprocess.Popen(cmd, stdout=log.open("wb"), stderr=subprocess.STDOUT,
                                     cwd=str(self.work))
        self.starts.append({"pid": self.proc.pid, "log": str(log)})
        time.sleep(2.5)

    def stop(self):
        if self.proc is not None and self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait(timeout=10)


@unittest.skipUnless(READY, "set FN_NATIVE_DTN_HOST, FN_NATIVE_HOST and FN_DTN7_REPO")
class NativeSourceCorpusBpTests(unittest.TestCase):
    def setUp(self):
        keep = os.environ.get("FN_NATIVE_TEST_DIAGNOSTIC_DIR")
        if keep:
            self.base = Path(keep) / "source-corpus-bp"
            self.base.mkdir(parents=True, exist_ok=False)
        else:
            self.temporary = tempfile.TemporaryDirectory(prefix="fn-source-corpus-bp-")
            self.addCleanup(self.temporary.cleanup)
            self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("FN_HOST", None)
        self.wall = str(int((time.time() - DTN_EPOCH_UNIX) * 1000))
        self.processes, self.relays, self.hold = [], [], None
        self.addCleanup(self.stop_all)

    def fn(self, tag, *args, expected=0, timeout=240, image=None):
        result = subprocess.run([str(image or IMAGE), "--fn", *map(str, args)], cwd=ROOT,
                                env=self.env, capture_output=True, timeout=timeout)
        (self.base / (tag + ".log")).write_bytes(
            b"$ fn " + " ".join(map(str, args)).encode() + b"\n" + result.stdout
            + result.stderr + b"\n# rc=%d\n" % result.returncode)
        if expected is not None:
            self.assertEqual(result.returncode, expected, (tag, result.stdout[-600:],
                                                            result.stderr[-600:]))
        return result

    def spawn(self, tag, *args):
        log = self.base / (tag + ".log")
        with log.open("wb") as handle:
            process = subprocess.Popen([str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
                                       env=self.env, stdout=handle,
                                       stderr=subprocess.STDOUT)
        self.processes.append(process)
        return process, log

    @staticmethod
    def wait_count(log, pattern, count, timeout):
        rx = re.compile(pattern)
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if len(rx.findall(log.read_text(errors="replace"))) >= count:
                return True
            time.sleep(0.3)
        return False

    def stop(self, process, kill=False):
        if process.poll() is None:
            if kill:
                process.send_signal(signal.SIGKILL)
            else:
                process.terminate()
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        if process in self.processes:
            self.processes.remove(process)
        return process.returncode

    def stop_all(self):
        for process in list(self.processes):
            self.stop(process)
        for relay in self.relays:
            relay.stop()
        if self.hold is not None:
            self.hold.close()

    @staticmethod
    def b_frames(b_fnbs):
        directory = b_fnbs / "lifecycle"
        return {path.name: path.read_bytes()
                for path in (sorted(directory.glob("*.fnb")) if directory.exists() else [])}

    def signing_keys(self):
        root = self.base / "keys"
        root.mkdir()
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        keys = [root / "principal", root / "ed.public", root / "ed.secret",
                root / "ml.public.pem", root / "ml.private.pem"]
        keys[0].write_bytes(bytes([85]) * 32)
        keys[1].write_bytes(bytes.fromhex(ED_PUBLIC))
        keys[2].write_bytes(bytes.fromhex(ED_SECRET))
        subprocess.run([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(keys[4])],
                       check=True, timeout=60)
        subprocess.run([openssl, "pkey", "-in", str(keys[4]), "-pubout", "-out",
                        str(keys[3])], check=True, timeout=60)
        return keys

    def signed_carrier(self, keys):
        carrier = self.base / "keys" / "signed.carrier"
        self.fn("setup-sign-carrier", "hybrid-sign-carrier", *keys,
                CORPUS / "signed.article", carrier, image=SIGN_IMAGE)
        return carrier.read_bytes()

    # -- each node's NNTP owner (the default developer image) ----------------
    def owner_config(self, side, store):
        port, control = free_port(), self.base / (side + "-control.sock")
        config = self.base / (side + ".toml")
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                          '[control]\npath = "{}"\n'.format(store, port, control),
                          encoding="ascii")
        return {"side": side, "store": store, "config": config, "port": port,
                "control": control}

    def owner_start(self, node, tag):
        log = self.base / (tag + ".log")
        with log.open("wb") as handle:
            process = subprocess.Popen([str(SIGN_IMAGE), "--fn", "operator",
                                        str(node["config"]), "run"], cwd=ROOT, env=self.env,
                                       stdout=handle, stderr=subprocess.STDOUT)
        self.processes.append(process)
        self.assertTrue(self.wait_count(log, r"LISTENING ", 1, 120), tag)
        return process

    def connect(self, node):
        client = socket.create_connection(("127.0.0.1", node["port"]), timeout=30)
        stream = client.makefile("rwb", buffering=0)
        self.assertTrue(stream.readline().startswith(b"200 "))
        return client, stream

    @staticmethod
    def body(stream):
        lines = []
        while True:
            line = stream.readline()
            if line in (b".\r\n", b""):
                return b"".join(lines)
            lines.append(line[1:] if line.startswith(b"..") else line)

    def post(self, node, payload):
        client, stream = self.connect(node)
        with client:
            stream.write(b"POST\r\n")
            first = stream.readline()
            self.assertTrue(first.startswith(b"340"), first)
            for line in payload.split(b"\r\n")[:-1]:
                stream.write((b"." + line if line.startswith(b".") else line) + b"\r\n")
            stream.write(b".\r\n")
            return stream.readline().rstrip(b"\r\n").decode("ascii", "replace")

    def served(self, node):
        """{Message-ID: octets} for every article a fresh view of fn.test serves."""
        client, stream = self.connect(node)
        view = {}
        with client:
            stream.write(b"LISTGROUP fn.test\r\n")
            if not stream.readline().startswith(b"211"):
                return view
            for number in [int(x) for x in self.body(stream).split()]:
                stream.write(b"ARTICLE %d\r\n" % number)
                if stream.readline().startswith(b"220"):
                    octets = self.body(stream)
                    view[header(octets, b"Message-ID")] = octets
        return view

    def records(self, node, tag):
        process = self.owner_start(node, tag)
        view = self.served(node)
        self.stop(process)
        return view

    def test_corpus_carried_by_bp_through_dtn7(self):
        base = self.base
        a_store, b_store = base / "a-store", base / "b-store"
        a_fnbs, b_fnbs = base / "a-fnbs", base / "b-fnbs"
        a_wf, b_wf, b_rj = base / "a-fnwf", base / "b-fnwf", base / "b-fnrj"
        a_port, b_port, relay_port = free_port(), free_port(), free_port()
        # dtn7 reaches B through the byte relay, so a transfer into B can be
        # held mid-bundle.
        self.hold = HoldRelay(b_port)
        for store in (a_store, b_store):
            self.fn("setup-init-" + store.name, "store", store, "init", "fn.test")
        a, b = self.owner_config("a", a_store), self.owner_config("b", b_store)
        for node, identity in ((a, A_ID), (b, B_ID)):
            self.fn("setup-{}-path".format(node["side"]), "operator", node["config"],
                    "policy", "set", "path-identity", identity)
        keys = self.signing_keys()
        sources = {name: (CORPUS / (name + ".article")).read_bytes()
                   for name in ELEMENTS if name != "signed"}
        sources["signed"] = self.signed_carrier(keys)
        # --- the corpus at A: the served POST, the author enrolled at both ---
        facts = {}
        for node in (b, a):
            owner = self.owner_start(node, "setup-{}-owner".format(node["side"]))
            self.fn("setup-{}-enroll".format(node["side"]), "hybrid-enroll", node["control"],
                    "1", keys[0], keys[1], keys[3], image=SIGN_IMAGE)
            if node is a:
                for name in ELEMENTS:
                    facts[name] = {"post": self.post(a, sources[name]),
                                   "source_sha256": sha(sources[name])}
                view = self.served(a)
            self.stop(owner)
        subjects = {header(o, b"Subject"): m for m, o in view.items()}
        for name in ELEMENTS:
            subject = header(sources[name], b"Subject")
            facts[name]["message_id"] = subjects.get(subject) \
                if facts[name]["post"].startswith("240") else None
        carried = [n for n in ELEMENTS if facts[n]["message_id"]]
        self.fn("setup-wf-init", "app-journal", "workflow-init", a_store, a_wf, SENDER,
                RECEIVER, "native-policy", RECEIVER, 3600000, "origin-native", "wire-auth")
        for txid, name in enumerate(carried, start=1):
            work = "work-" + name
            facts[name]["work"] = work
            self.fn("a-enqueue-" + name, "app-journal", "workflow-enqueue", a_store, a_wf,
                    txid, 0, work, facts[name]["message_id"], "forward-" + work, RECEIVER,
                    "native-policy", "terms-native")
            self.fn("a-undertake-" + name, "bp-obligation", "undertake", a_store, a_wf,
                    work, 3)
        # --- boundaries and routes (D23 carried mode), as the request labs ---
        for node, name, remote, port, far, scope in (
                (a, "return-boundary", "r1.bp.gate.invalid", a_port,
                 ("receiver-author", B_ID, RECEIVER), []),
                (b, "ingress-boundary", "rn.bp.gate.invalid", b_port,
                 ("sender-author", A_ID, SENDER), ["fn.test", "65536", "16"])):
            side = node["side"]
            releases = ["releases-for", far[2]] if side == "a" else []
            self.fn("setup-{}-boundary".format(side), "operator", node["config"],
                    "bp-boundary", "add", name, remote, "dtn://dtn7-r1/", port, "carries",
                    far[2], *releases, "contact", relay_port)
            self.fn("setup-{}-route".format(side), "operator", node["config"], "bp-route",
                    "add", far[2] + "*", name)
            self.fn("setup-{}-author".format(side), "operator", node["config"],
                    "bp-boundary", "add", far[0], far[1], far[2], free_port(), *scope)
        # --- the relay and B ---------------------------------------------------
        relay = Dtnd(base, "dtn7-r1", relay_port,
                     ["tcp://127.0.0.1:{}/receiver".format(self.hold.port),
                      "tcp://127.0.0.1:{}/sender".format(a_port)])
        self.relays.append(relay)
        relay.start()

        def start_b(tag):
            process, log = self.spawn(
                tag, "bp-node", "serve", b_port, b_fnbs, b_store, b_rj, b_wf, RECEIVER,
                SENDER, RECEIVER, "native-policy", RECEIVER, "127.0.0.1", relay_port, "0",
                3600000, 2, 32, 1048576, self.wall, 60000)
            self.assertTrue(self.wait_count(log, r"BP NODE LISTENING", 1, 60), tag)
            return process, log

        b_serve, b_log = start_b("b-serve-0")
        # --- each obligation: ACL2's kind-8 attempt, then the carrier ---------
        attempt_rx = re.compile(r"BP obligation request durable attempt (.*)")
        verdict_rx = r"BP node delivery request-\S+"
        seen = 0
        for index, name in enumerate(carried):
            work = facts[name]["work"]
            last = index == len(carried) - 1
            if last:
                # B dies mid-receive: the byte relay holds this transfer.
                self.hold.arm(200)
            request = self.fn("a-request-" + name, "bp-obligation", "request", a_store, a_wf,
                              work, work + "-attempt", a_fnbs, SENDER, "127.0.0.1",
                              relay_port, 3600000, 2, 32, 1048576, self.wall, 60000,
                              expected=None)
            text = (request.stdout + request.stderr).decode("utf-8", "replace")
            found = attempt_rx.search(text)
            facts[name]["attempt"] = found.group(1).strip() if found else None
            facts[name]["request_rc"] = request.returncode
            if last:
                facts[name]["held"] = self.hold.held.wait(60)
                self.stop(b_serve, kill=True)
                facts[name]["b_sigkill"] = b_serve.pid
                b_serve, b_log = start_b("b-serve-1")
                relay.stop()
                relay.start()
                seen = 0
            seen += 1
            self.wait_count(b_log, verdict_rx, seen, 60)
            verdicts = re.findall(verdict_rx, b_log.read_text(errors="replace"))
            facts[name]["b_verdict"] = verdicts[seen - 1] if len(verdicts) >= seen else None
        self.stop(b_serve)
        frames = self.b_frames(b_fnbs)
        # --- the records -----------------------------------------------------------
        a_view = self.records(a, "a-read")
        b_view = self.records(b, "b-read")
        # B SIGKILLed once more, idle, then reopened: the same records.
        b_serve, b_log = start_b("b-serve-2")
        self.stop(b_serve, kill=True)
        b_serve, b_log = start_b("b-serve-3")
        self.stop(b_serve)
        b_again = self.records(b, "b-read-again")
        rows = []
        for name in ELEMENTS:
            f = facts[name]
            msgid = f["message_id"]
            a_octets = a_view.get(msgid) if msgid else None
            b_octets = b_view.get(msgid) if msgid else None
            matching = [n for n, frame in frames.items() if msgid and msgid.encode() in frame]
            f.update(a=a_octets, b=b_octets, b_reopened=b_again.get(msgid) if msgid else None,
                     frame=matching[0] if matching else None,
                     bundle=bundle_identity(frames[matching[0]]) if matching else None)
            rows.append({
                "element": name, "message_id": msgid,
                "operation": "POST at A, bp-obligation request, dtn7, bp-node serve at B",
                "a_post": f["post"], "source_sha256": f["source_sha256"],
                "kind8_attempt": f.get("attempt"), "b_verdict": f.get("b_verdict"),
                "bundle": f["bundle"], "b_frame": f["frame"],
                "a_stored_sha256": sha(a_octets) if a_octets else None,
                "b_stored_sha256": sha(b_octets) if b_octets else None,
                "a_path": header(a_octets, b"Path") if a_octets else None,
                "b_path": header(b_octets, b"Path") if b_octets else None,
                "b_is_a_with_b_splice": (b_octets == spliced(a_octets, B_ID)
                                         if a_octets and b_octets else None),
                "b_after_sigkill_reopen_same": (f["b_reopened"] == b_octets
                                                if b_octets else None),
                "b_sigkill_mid_receive": f.get("b_sigkill"),
            })
        print("SOURCE-CORPUS-BP-TABLE " + json.dumps(rows, sort_keys=True))
        # --- the contract ---------------------------------------------------------
        self.assertTrue(facts["xref"]["post"].startswith("441"), facts["xref"])
        self.assertEqual(carried, [n for n in ELEMENTS if n != "xref"],
                         [(n, facts[n]["post"]) for n in ELEMENTS])
        self.assertTrue(facts[carried[-1]].get("held"), "the transfer into B was not held")
        for name in carried:
            f = facts[name]
            self.assertIsNotNone(f["attempt"], (name, "no kind-8 attempt line"))
            self.assertEqual(f["b_verdict"], "BP node delivery request-accepted", name)
            self.assertIsNotNone(f["a"], (name, "A serves no record"))
            self.assertIsNotNone(f["b"], (name, "B serves no record"))
            self.assertEqual(f["b"], spliced(f["a"], B_ID), name)
            self.assertEqual(f["b_reopened"], f["b"], name)
            self.assertIsNotNone(f["bundle"], (name, "no bundle in B's kind-5 frame"))
            self.assertEqual(f["bundle"]["source"], "dtn://sender/", name)
        identities = [(facts[n]["bundle"]["creation_ms"], facts[n]["bundle"]["sequence"])
                      for n in carried]
        self.assertEqual(len(set(identities)), len(identities), identities)


if __name__ == "__main__":
    unittest.main()
