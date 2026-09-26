"""Opt-in native witness for the NEWNEWS pull feed (NNT-018, SCN-058, PRF-100).

Node B is behind NAT: nothing dials it.  B pulls by NEWNEWS (RFC 3977
section 7.4) from a second fn node A and from INN's nnrpd; the rounds are
books/peer-pull.lisp's, driven by host/native/pull-service.lisp.  A
recording proxy in front of the pulled server logs every command B sends,
so the cases read B's NEWNEWS lines rather than trusting B's own account.

- test_pull_from_fn_node: A holds two articles; B's round lists, offers
  and stores both, its FNPL cursor advances, and a later round names a
  later instant and stores nothing new.
- test_kill_mid_round_recovery_asks_the_same_newnews: the proxy withholds
  B's first ARTICLE; B is killed (SIGKILL) there; after restart B's first
  NEWNEWS is byte-identical to the dead round's and the article is stored.
- test_unavailable_id_is_dropped_at_the_bound (PRF-165, PKT-213): a
  scripted peer lists an id it answers 430; the other ids are stored, the
  cursor holds for BOUND-1 rounds and advances at the BOUND-th, logging the
  drop once.
- test_unavailable_count_survives_a_cut: the held close's FNPL append is
  cut after its fsync (the count survives the restart) and before its
  write (the count starts again).
- test_pull_from_inn: INN (FN_INN_SRC, an installed INN 2.7 tree) holds an
  article in fn.test; B pulls it from nnrpd and stores it.

Protected pulls (NNT-023, SCN-071, PRF-125; books/peer-pull-session.lisp).
Node A serves STARTTLS with `[auth] required = true, protected_only = true`
and a principal for B; B's peer record for A names STARTTLS, A's
certificate as the only trust anchor and B's credential profile.

- test_tls_pull_as_its_own_principal: B pulls both articles over TLS as its
  principal and its cursor advances; the recording proxy sees STARTTLS and
  no AUTHINFO, DATE, NEWNEWS or ARTICLE in the clear.
- test_wrong_principal_is_refused_by_the_serving_node: B's profile names a
  login A does not hold; A refuses it after TLS, B stores nothing and its
  FNPL journal does not grow past the first instant.
- test_clear_credential_is_refused_before_any_connection: a clear transport
  with a credential and no loopback-lab permission; B's own ACL2 refuses
  every round and the proxy in front of A is never dialled.
- test_cursor_publication_cuts_over_tls: packet 5's six kill cuts, over the
  protected transport.

Run: FN_NATIVE_HOST=<launcher> [FN_INN_SRC=/tank/fn/inn/2.7.4] \
     python3 -m unittest -v tests.test_native_peer_pull
"""

import calendar
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import subprocess
import tempfile
import threading
import time
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
INN_SRC = os.environ.get("FN_INN_SRC")
INN_READY = bool(INN_SRC and (Path(INN_SRC) / "bin" / "innd").is_file())
INTERVAL = "2"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def port_open(port):
    with socket.socket() as probe:
        probe.settimeout(1)
        return probe.connect_ex(("127.0.0.1", port)) == 0


def sha256_of(path):
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return None


def article(message_id, subject, path=None):
    lines = []
    if path:
        lines.append("Path: " + path)
    lines += ["From: poster@example.invalid", "Newsgroups: fn.test",
              "Subject: " + subject,
              "Date: Fri, 25 Sep 2026 03:00:00 +0000",
              "Message-ID: " + message_id]
    return ("\r\n".join(lines) + "\r\n\r\nbody of " + subject + "\r\n").encode("ascii")


class RecordingProxy:
    """TCP relay to TARGET that records each command line its clients send.

    With `hold` set, the first ARTICLE command is recorded, not forwarded,
    and `held` is set: the round is frozen after NEWNEWS and a local 335.
    """

    def __init__(self, target_port):
        self.target_port = target_port
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(8)
        self.port = self.listener.getsockname()[1]
        self.lock = threading.Lock()
        self.commands = []
        self.connections = 0
        self.hold = False
        self.passed = 0
        self.held = threading.Event()
        self.closed = False
        threading.Thread(target=self.accept_loop, daemon=True).start()

    def accept_loop(self):
        while not self.closed:
            try:
                client, _ = self.listener.accept()
            except OSError:
                return
            with self.lock:
                self.connections += 1
            threading.Thread(target=self.relay, args=(client,), daemon=True).start()

    def relay(self, client):
        try:
            server = socket.create_connection(("127.0.0.1", self.target_port), timeout=30)
        except OSError:
            client.close()
            return

        def downstream():
            try:
                while True:
                    data = server.recv(65536)
                    if not data:
                        break
                    client.sendall(data)
            except OSError:
                pass
            finally:
                for s in (client, server):
                    try:
                        s.shutdown(socket.SHUT_RDWR)
                    except OSError:
                        pass

        threading.Thread(target=downstream, daemon=True).start()
        buffered = b""
        try:
            while True:
                data = client.recv(65536)
                if not data:
                    break
                buffered += data
                while b"\n" in buffered:
                    line, buffered = buffered.split(b"\n", 1)
                    line += b"\n"
                    with self.lock:
                        self.commands.append(line.rstrip(b"\r\n").decode("ascii", "replace"))
                        holding = self.hold and line.upper().startswith(b"ARTICLE")
                    if holding:
                        self.held.set()
                        while True:
                            if not client.recv(65536):
                                return
                    server.sendall(line)
                # Octets with no line end yet (a TLS record) pass through now
                # unless an ARTICLE may have to be held; they are recorded
                # once their line completes, never as a command of their own.
                if buffered and not self.hold:
                    server.sendall(buffered)
                    with self.lock:
                        self.passed += len(buffered)
                    buffered = b""
        except OSError:
            pass
        finally:
            for s in (client, server):
                try:
                    s.close()
                except OSError:
                    pass

    def newnews(self):
        with self.lock:
            return [c for c in self.commands if c.upper().startswith("NEWNEWS")]

    def mark(self):
        with self.lock:
            return len(self.commands)

    def since(self, mark):
        with self.lock:
            return list(self.commands[mark:])

    def close(self):
        self.closed = True
        self.listener.close()


class ScriptedPeer:
    """A reader-only NNTP server (PRF-165, PKT-213): DATE answers the wall
    clock, every NEWNEWS lists LISTED, and ARTICLE serves ARTICLES and
    answers 430 for any other id -- a peer that keeps listing an article it
    cannot produce.  It records each command, as the proxy does."""

    def __init__(self, listed, articles, tls=None):
        self.listed = list(listed)
        self.articles = dict(articles)
        self.arrived = int(time.time())
        # TLS: (certificate, key) -- STARTTLS is answered 382 and the
        # session continues inside TLS, so ARTICLE is counted HERE, on the
        # server side, where a proxy in front could not read it (PKT-236 b).
        self.tls = tls
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(8)
        self.port = self.listener.getsockname()[1]
        self.lock = threading.Lock()
        self.commands = []
        self.closed = False
        threading.Thread(target=self.accept_loop, daemon=True).start()

    def accept_loop(self):
        while not self.closed:
            try:
                client, _ = self.listener.accept()
            except OSError:
                return
            threading.Thread(target=self.serve, args=(client,), daemon=True).start()

    def serve(self, client):
        try:
            stream = client.makefile("rwb", buffering=0)
            stream.write(b"200 scripted peer ready (no posting)\r\n")
            while True:
                line = stream.readline()
                if not line:
                    return
                text = line.rstrip(b"\r\n").decode("ascii", "replace")
                with self.lock:
                    self.commands.append(text)
                word = text.split(" ", 1)[0].upper()
                if word == "DATE":
                    stream.write(time.strftime("111 %Y%m%d%H%M%S\r\n",
                                               time.gmtime()).encode("ascii"))
                elif word == "NEWNEWS":
                    # RFC 3977 7.4: ids that ARRIVED at or after the instant;
                    # all of this peer's ids arrived when it was built.
                    words = text.split()
                    try:
                        since = calendar.timegm(time.strptime(words[2] + words[3],
                                                              "%Y%m%d%H%M%S"))
                    except (IndexError, ValueError):
                        since = 0
                    listed = self.listed if self.arrived >= since else []
                    body = b"".join(m.encode("ascii") + b"\r\n" for m in listed)
                    stream.write(b"230 list follows\r\n" + body + b".\r\n")
                elif word == "ARTICLE":
                    mid = text.split(" ", 1)[1] if " " in text else ""
                    if mid in self.articles:
                        octets = self.articles[mid].replace(b"\r\n.", b"\r\n..")
                        stream.write("220 0 {}\r\n".format(mid).encode("ascii")
                                     + octets + b".\r\n")
                    else:
                        stream.write(b"430 no such article\r\n")
                elif word == "STARTTLS" and self.tls:
                    import ssl
                    stream.write(b"382 continue with TLS negotiation\r\n")
                    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
                    context.load_cert_chain(str(self.tls[0]), str(self.tls[1]))
                    client = context.wrap_socket(client, server_side=True)
                    stream = client.makefile("rwb", buffering=0)
                elif word == "QUIT":
                    stream.write(b"205 bye\r\n")
                    return
                else:
                    stream.write(b"500 what\r\n")
        except OSError:
            pass
        finally:
            try:
                client.close()
            except OSError:
                pass

    def count(self, prefix):
        with self.lock:
            return sum(1 for c in self.commands if c.startswith(prefix))

    def newnews(self):
        with self.lock:
            return [c for c in self.commands if c.upper().startswith("NEWNEWS")]

    def close(self):
        self.closed = True
        self.listener.close()


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativePeerPullTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-pull-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.processes = []
        self.addCleanup(self.stop_all)
        self.evidence = Path(os.environ.get("FN_PULL_EVIDENCE", self.base / "evidence"))
        self.evidence.mkdir(parents=True, exist_ok=True)
        self.nodes = []
        self.addCleanup(self.keep_logs)

    def keep_logs(self):
        for node in self.nodes:
            for name in ("fn.log", "stderr.log"):
                source = node["root"] / name
                if source.exists():
                    shutil.copyfile(source, self.evidence / "{}-{}-{}".format(
                        self._testMethodName, node["name"], name))

    # ------------------------------------------------------------ nodes

    def command(self, arguments, expected=0):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=180, check=False)
        self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name, groups, identity):
        root = self.base / name
        root.mkdir()
        store, control = root / "store", root / "control.sock"
        port = free_port()
        self.command([IMAGE, "--fn", "store", store, "init", *groups])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                store, port, control, root / "fn.log"), encoding="ascii")
        node = {"name": name, "root": root, "config": config, "port": port,
                "store": store, "log": root / "fn.log"}
        self.nodes.append(node)
        self.command([IMAGE, "--fn", "operator", config, "policy", "set",
                      "path-identity", identity])
        return node

    def pull_from(self, node, name, identity, port):
        """NAME is a peer B dials only: inbound fn.*, outbound none.  Its
        source address is one no socket here uses, so the test's own reader
        sessions from 127.0.0.1 are readers, not that peer's transit."""
        self.command([IMAGE, "--fn", "operator", node["config"], "peer", "add",
                      name, identity, "127.0.0.1", str(port), "fn.*", "-",
                      "127.0.0.9", "true"])
        self.command([IMAGE, "--fn", "operator", node["config"], "peer", "pull",
                      name, INTERVAL])

    def start(self, node):
        err = open(node["root"] / "stderr.log", "ab")
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=err)
        self.processes.append(process)
        node["process"] = process
        wait_for_announcement(process, b"LISTENING ")

    def stop(self, node):
        process = node.pop("process")
        process.terminate()
        process.communicate(timeout=60)
        self.processes.remove(process)

    def kill(self, node):
        process = node.pop("process")
        process.send_signal(signal.SIGKILL)
        process.communicate(timeout=60)
        self.processes.remove(process)

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.communicate(timeout=60)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.communicate(timeout=60)

    # ------------------------------------------------------------ NNTP

    def session(self, port, lines):
        with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            greeting = stream.readline()
            self.assertTrue(greeting.startswith(b"200 ") or greeting.startswith(b"201 "),
                            greeting)
            replies = []
            for item in lines:
                stream.write(item)
                replies.append(stream.readline())
            return replies

    def post(self, node, payload):
        first, second = self.session(node["port"], [b"POST\r\n", payload + b".\r\n"])
        self.assertTrue(first.startswith(b"340"), first)
        self.assertTrue(second.startswith(b"240"), second)

    def article_code(self, node, message_id):
        return self.session(node["port"],
                            [b"STAT " + message_id.encode("ascii") + b"\r\n"])[0][:3]

    def await_article(self, node, message_id, timeout=90):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if self.article_code(node, message_id) == b"223":
                return True
            time.sleep(0.25)
        self.fail("{} did not store {}; log: {}".format(
            node["name"], message_id, self.log_tail(node)))

    def log_tail(self, node):
        try:
            return node["log"].read_text(errors="replace")[-2000:]
        except OSError:
            return ""

    def pull_lines(self, node):
        try:
            return [l for l in node["log"].read_text(errors="replace").splitlines()
                    if l.startswith("pull peer=")]
        except OSError:
            return []

    def await_log(self, node, needle, count=1, timeout=90):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if sum(needle in l for l in self.pull_lines(node)) >= count:
                return
            time.sleep(0.25)
        self.fail("{}: fewer than {} '{}' lines; log: {}".format(
            node["name"], count, needle, self.log_tail(node)))

    def fnpl_files(self, node):
        top = node["store"] / "pull"
        return sorted(str(p.relative_to(top)) for p in top.rglob("*") if p.is_file()) \
            if top.exists() else []

    def witness(self, kind, data, nodes):
        data = dict(data, kind=kind)
        for node in nodes:
            keep = self.evidence / "{}-{}.log".format(kind, node["name"])
            if node["log"].exists():
                shutil.copyfile(node["log"], keep)
            data["log_sha256_" + node["name"]] = sha256_of(node["log"])
        data["image_sha256"] = sha256_of(IMAGE)
        data["core_sha256"] = sha256_of(str(IMAGE) + ".core")
        (self.evidence / (kind + ".witness.json")).write_text(
            json.dumps(data, sort_keys=True, indent=1), encoding="utf-8")
        print("NATIVE-PULL-WITNESS " + json.dumps(data, sort_keys=True), flush=True)

    def two_nodes(self):
        a = self.initialize("A", ["fn.test"], "a.pull.example.invalid")
        b = self.initialize("B", ["fn.test"], "b.pull.example.invalid")
        self.start(a)
        proxy = RecordingProxy(a["port"])
        self.addCleanup(proxy.close)
        self.pull_from(b, "A", "a.pull.example.invalid", proxy.port)
        return a, b, proxy

    # ------------------------------------------------------------ cases

    def test_pull_from_fn_node(self):
        a, b, proxy = self.two_nodes()
        ids = ["<pull-one@example.invalid>", "<pull-two@example.invalid>"]
        for n, message_id in enumerate(ids):
            self.post(a, article(message_id, "pull-{}".format(n)))
        self.start(b)
        for message_id in ids:
            self.await_article(b, message_id)
        self.await_log(b, "cursor=advanced", 1)
        # A later round asks a later instant and has nothing to take.
        self.await_log(b, "round=done", 2)
        newnews = proxy.newnews()
        articles = [c for c in proxy.commands if c.upper().startswith("ARTICLE")]
        fnpl = self.fnpl_files(b)
        self.stop(b)
        self.stop(a)
        self.witness("fn-node", {"newnews": newnews, "article_commands": articles,
                                 "pull_lines": self.pull_lines(b), "fnpl": fnpl,
                                 "proxy_connections": proxy.connections}, [a, b])
        self.assertGreaterEqual(len(newnews), 2, newnews)
        self.assertTrue(newnews[0].startswith("NEWNEWS fn.* "), newnews)
        self.assertTrue(newnews[0].endswith(" GMT"), newnews)
        self.assertLess(newnews[0], newnews[1], newnews)
        self.assertEqual(sorted(articles), sorted("ARTICLE " + i for i in ids))
        self.assertTrue(fnpl, "no FNPL journal under the store's pull directory")
        for message_id in ids:
            self.assertIn(message_id, " ".join(articles))

    def test_kill_mid_round_recovery_asks_the_same_newnews(self):
        a, b, proxy = self.two_nodes()
        first = "<pull-before-crash@example.invalid>"
        self.post(a, article(first, "before-crash"))
        self.start(b)
        self.await_article(b, first)
        self.await_log(b, "cursor=advanced", 1)
        victim = "<pull-crash@example.invalid>"
        proxy.hold = True
        self.post(a, article(victim, "crash"))
        self.assertTrue(proxy.held.wait(90), "no ARTICLE for {}; log: {}".format(
            victim, self.log_tail(b)))
        dead_newnews = proxy.newnews()[-1]
        self.assertNotEqual(self.article_code(b, victim), b"223")
        self.kill(b)
        mark = proxy.mark()
        proxy.hold = False
        self.start(b)
        self.await_article(b, victim)
        after = [c for c in proxy.since(mark) if c.upper().startswith("NEWNEWS")]
        self.stop(b)
        self.stop(a)
        self.witness("kill-mid-round", {"dead_round_newnews": dead_newnews,
                                        "newnews_after_restart": after,
                                        "pull_lines": self.pull_lines(b),
                                        "fnpl": self.fnpl_files(b)}, [a, b])
        self.assertTrue(after, "B asked nothing after restart")
        self.assertEqual(after[0], dead_newnews)

    def test_cursor_publication_cuts(self):
        """Packet 5 (PRF-124): SIGKILL at every write of the cursor's
        publication.  A fresh cursor journals its first instant before the
        round dials (append 1) and the round's close journals the advanced
        cursor (append 2); each is cut before the write, after the write and
        after the fsync.  After a restart without the fault, every article A
        held is stored at B exactly once (no skipped accepted work), and what
        B re-offered to itself is bounded by the dead round's listing (the
        duplicates draw 435 and change nothing)."""
        results = {}
        for append in (1, 2):
            for cut in ("before-write", "after-write", "after-fsync"):
                label = "{}:{}".format(cut, append)
                a, b, proxy = self.two_nodes_named("A" + label.replace(":", "-"),
                                                   "B" + label.replace(":", "-"))
                ids = ["<cut-{}-{}@example.invalid>".format(label.replace(":", "-"), k)
                       for k in range(2)]
                for n, message_id in enumerate(ids):
                    self.post(a, article(message_id, "cut-{}".format(n)))
                self.env["FN_PULL_TEST_KILL"] = label
                try:
                    self.start(b)
                except Exception:  # died before announcing LISTENING
                    pass
                finally:
                    del self.env["FN_PULL_TEST_KILL"]
                process = b["process"]
                code = process.wait(timeout=120)
                b.pop("process")
                process.communicate(timeout=60)
                self.processes.remove(process)
                self.assertEqual(code, -signal.SIGKILL, label)
                mark = proxy.mark()
                self.start(b)
                for message_id in ids:
                    self.await_article(b, message_id)
                self.await_log(b, "cursor=advanced", 1)
                after = proxy.since(mark)
                articles = [c for c in after if c.upper().startswith("ARTICLE")]
                newnews = [c for c in after if c.upper().startswith("NEWNEWS")]
                counts = {i: self.count_article(b, i) for i in ids}
                self.stop(b)
                self.stop(a)
                results[label] = {"newnews_after": newnews[:2],
                                  "article_after": articles, "counts": counts,
                                  "pull_lines": self.pull_lines(b)}
                for message_id in ids:
                    self.assertEqual(counts[message_id], 1, (label, counts))
                # Only ids the peer listed are fetched, each at most once per
                # round: the duplicate replay is bounded by the listing.
                self.assertLessEqual(len(articles), len(ids), (label, articles))
        self.witness("cursor-cuts", results, [])

    def two_nodes_named(self, name_a, name_b):
        a = self.initialize(name_a, ["fn.test"], "a.pull.example.invalid")
        b = self.initialize(name_b, ["fn.test"], "b.pull.example.invalid")
        self.start(a)
        proxy = RecordingProxy(a["port"])
        self.addCleanup(proxy.close)
        self.pull_from(b, "A", "a.pull.example.invalid", proxy.port)
        return a, b, proxy

    def stored(self, node, message_id):
        return self.article_code(node, message_id) == b"223"

    def count_article(self, node, message_id):
        """How many local articles of fn.test carry MESSAGE_ID (XOVER 1-)."""
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            stream.readline()
            stream.write(b"GROUP fn.test\r\n")
            stream.readline()
            stream.write(b"XOVER 1-\r\n")
            head = stream.readline()
            lines = []
            if head.startswith(b"224"):
                while True:
                    line = stream.readline()
                    if not line or line == b".\r\n":
                        break
                    lines.append(line)
        return sum(1 for line in lines if message_id.encode("ascii") in line)

    # ------------------------------------------------------------ protected

    def certificate(self, root, name):
        certificate, key = root / (name + "-certificate.pem"), root / (name + "-key.pem")
        result = subprocess.run(
            [os.environ.get("FN_TEST_OPENSSL", "openssl"), "req", "-x509", "-newkey",
             "rsa:2048", "-nodes", "-sha256", "-days", "1", "-subj", "/CN=localhost",
             "-keyout", str(key), "-out", str(certificate)],
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return certificate, key

    def initialize_protected(self, name, login, password, protected_only=True):
        """A serving node: STARTTLS, authentication required and AUTHINFO only
        on a protected channel; LOGIN/PASSWORD is the principal it holds for
        the pulling node."""
        root = self.base / name
        root.mkdir()
        store, control = root / "store", root / "control.sock"
        port = free_port()
        certificate, key = self.certificate(root, name)
        self.command([IMAGE, "--fn", "store", store, "init", "fn.test"])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n[log]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = {}\npath = "{}"\n'.format(
                store, port, certificate, key, control, root / "fn.log",
                "true" if protected_only else "false",
                root / "auth.toml"), encoding="ascii")
        enrolled = subprocess.run(
            [str(IMAGE), "--fn", "operator", str(config), "principal", "set-password",
             login], cwd=ROOT, env=self.env,
            input=(password + "\n" + password + "\n").encode(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        node = {"name": name, "root": root, "config": config, "port": port,
                "store": store, "log": root / "fn.log", "certificate": certificate}
        self.nodes.append(node)
        self.command([IMAGE, "--fn", "operator", config, "policy", "set",
                      "path-identity", "a.pull.example.invalid"])
        return node

    def operator_post(self, node, message_id, subject):
        payload = node["root"] / (subject + ".article")
        payload.write_bytes(article(message_id, subject))
        self.command([IMAGE, "--fn", "operator", node["config"], "post",
                      "--message-id", message_id, "--payload", payload,
                      "--group", "fn.test"])

    def profile(self, node, login, password):
        path = node["root"] / "A.fnauth"
        path.write_bytes("FNAUTH1\n{}\n{}\n".format(login, password).encode("ascii"))
        path.chmod(0o600)
        return path

    def pull_protected(self, b, a, port, profile, tls=True, allow_clear=False):
        """B's record for A: inbound and outbound fn.*, source-address auth on
        an address no socket here uses, B's credential PROFILE, and STARTTLS
        against A's certificate as the only anchor (or a clear transport)."""
        security = ["starttls", "localhost", str(a["certificate"])] if tls else []
        self.command([IMAGE, "--fn", "operator", b["config"], "peer", "add", "A",
                      "a.pull.example.invalid", "127.0.0.1", str(port), "fn.*", "fn.*",
                      "source-address", "127.0.0.9", str(profile),
                      "true" if allow_clear else "false", "false", *security])
        self.command([IMAGE, "--fn", "operator", b["config"], "peer", "pull", "A",
                      INTERVAL])

    def protected_pair(self, name_a="A", name_b="B", login="nodeB", password="b-secret",
                       presented=None, tls=True):
        a = self.initialize_protected(name_a, login, password)
        b = self.initialize(name_b, ["fn.test"], "b.pull.example.invalid")
        self.start(a)
        proxy = RecordingProxy(a["port"])
        self.addCleanup(proxy.close)
        self.pull_protected(b, a, proxy.port,
                            self.profile(b, *(presented or (login, password))), tls=tls)
        return a, b, proxy

    def plaintext_private(self, proxy):
        """Commands the proxy saw in the clear that carry a credential or
        read the archive."""
        with proxy.lock:
            return [c for c in proxy.commands
                    if c.upper().startswith(("AUTHINFO", "DATE", "NEWNEWS", "ARTICLE"))]

    def fnpl_size(self, node):
        top = node["store"] / "pull"
        return sum(p.stat().st_size for p in top.rglob("*") if p.is_file()) \
            if top.exists() else 0

    def test_tls_pull_as_its_own_principal(self):
        a, b, proxy = self.protected_pair()
        ids = ["<tls-one@example.invalid>", "<tls-two@example.invalid>"]
        for n, message_id in enumerate(ids):
            self.operator_post(a, message_id, "tls-{}".format(n))
        self.start(b)
        for message_id in ids:
            self.await_article(b, message_id)
        self.await_log(b, "cursor=advanced transport=tls", 1)
        self.await_log(b, "round=done", 2)
        with proxy.lock:
            first = proxy.commands[:1]
        private = self.plaintext_private(proxy)
        counts = {i: self.count_article(b, i) for i in ids}
        self.stop(b)
        self.stop(a)
        self.witness("tls-pull", {"first_plaintext_command": first,
                                  "plaintext_private": private,
                                  "octets_passed_through": proxy.passed,
                                  "counts": counts, "pull_lines": self.pull_lines(b),
                                  "fnpl": self.fnpl_files(b)}, [a, b])
        self.assertEqual(first, ["STARTTLS"])
        self.assertEqual(private, [])
        self.assertGreater(proxy.passed, 0)
        for message_id in ids:
            self.assertEqual(counts[message_id], 1)

    def test_wrong_principal_is_refused_by_the_serving_node(self):
        a, b, proxy = self.protected_pair(presented=("mallory", "not-b-secret"))
        message_id = "<tls-refused@example.invalid>"
        self.operator_post(a, message_id, "tls-refused")
        self.start(b)
        self.await_log(b, "round=failed cursor=held at=preamble", 1)
        journal = self.fnpl_size(b)
        self.await_log(b, "round=failed cursor=held at=preamble", 3)
        journal_later = self.fnpl_size(b)
        stored = self.stored(b, message_id)
        lines = self.pull_lines(b)
        private = self.plaintext_private(proxy)
        with proxy.lock:
            first = proxy.commands[:1]
        self.stop(b)
        self.stop(a)
        self.witness("tls-wrong-principal", {"pull_lines": lines, "stored": stored,
                                             "fnpl_octets": [journal, journal_later],
                                             "first_plaintext_command": first,
                                             "plaintext_private": private,
                                             "proxy_connections": proxy.connections},
                     [a, b])
        self.assertFalse(stored)
        self.assertFalse(any("cursor=advanced" in l for l in lines), lines)
        self.assertEqual(journal, journal_later)
        self.assertEqual(first, ["STARTTLS"])
        self.assertEqual(private, [])
        self.assertGreaterEqual(proxy.connections, 3)

    def test_clear_credential_is_refused_before_any_connection(self):
        a, b, proxy = self.protected_pair(tls=False)
        self.operator_post(a, "<clear-refused@example.invalid>", "clear-refused")
        self.start(b)
        self.await_log(b, "refused=clear-credential", 3)
        lines = self.pull_lines(b)
        self.stop(b)
        self.stop(a)
        self.witness("clear-credential", {"pull_lines": lines,
                                          "proxy_connections": proxy.connections,
                                          "proxy_commands": proxy.commands}, [a, b])
        self.assertEqual(proxy.connections, 0)
        self.assertTrue(all("round=failed cursor=held refused=clear-credential" in l
                            for l in lines), lines)

    def test_cursor_publication_cuts_over_tls(self):
        """Packet 5's campaign (test_cursor_publication_cuts) over the
        protected transport: every article stored exactly once at every cut."""
        results = {}
        for append in (1, 2):
            for cut in ("before-write", "after-write", "after-fsync"):
                label = "{}:{}".format(cut, append)
                tag = label.replace(":", "-")
                a, b, proxy = self.protected_pair("TA" + tag, "TB" + tag)
                ids = ["<tls-cut-{}-{}@example.invalid>".format(tag, k) for k in range(2)]
                for n, message_id in enumerate(ids):
                    self.operator_post(a, message_id, "tls-cut-{}".format(n))
                self.env["FN_PULL_TEST_KILL"] = label
                try:
                    self.start(b)
                except Exception:  # died before announcing LISTENING
                    pass
                finally:
                    del self.env["FN_PULL_TEST_KILL"]
                process = b["process"]
                code = process.wait(timeout=120)
                b.pop("process")
                process.communicate(timeout=60)
                self.processes.remove(process)
                self.assertEqual(code, -signal.SIGKILL, label)
                self.start(b)
                for message_id in ids:
                    self.await_article(b, message_id)
                self.await_log(b, "cursor=advanced transport=tls", 1)
                counts = {i: self.count_article(b, i) for i in ids}
                private = self.plaintext_private(proxy)
                self.stop(b)
                self.stop(a)
                results[label] = {"counts": counts, "pull_lines": self.pull_lines(b),
                                  "plaintext_private": private}
                for message_id in ids:
                    self.assertEqual(counts[message_id], 1, (label, counts))
                self.assertEqual(private, [], label)
        self.witness("tls-cursor-cuts", results, [])

    # ------------------------------------------------------------ PRF-165

    def unavailable_pair(self, name, bound):
        ghost = "<ghost-{}@example.invalid>".format(name)
        real = ["<real-{}-{}@example.invalid>".format(name, k) for k in range(2)]
        peer = ScriptedPeer([real[0], ghost, real[1]],
                            {m: article(m, "real-" + m[6:12], path="scripted!not-for-mail")
                             for m in real})
        self.addCleanup(peer.close)
        b = self.initialize("B" + name, ["fn.test"], "b.pull.example.invalid")
        self.command([IMAGE, "--fn", "operator", b["config"], "peer", "add",
                      "S", "s.pull.example.invalid", "127.0.0.1", str(peer.port),
                      "fn.*", "-", "127.0.0.9", "true"])
        self.command([IMAGE, "--fn", "operator", b["config"], "peer", "pull",
                      "S", INTERVAL, str(bound)])
        return peer, b, ghost, real

    def test_unavailable_id_is_dropped_at_the_bound(self):
        """PKT-213: the peer lists <ghost> between two real articles and
        answers its ARTICLE 430.  The real articles are stored in the first
        round; the cursor holds for BOUND-1 complete rounds, each naming the
        same instant; at the BOUND-th the cursor advances and the log names
        <ghost> once; the next NEWNEWS names a later instant."""
        bound = 3
        peer, b, ghost, real = self.unavailable_pair("drop", bound)
        self.start(b)
        for message_id in real:
            self.await_article(b, message_id)
        self.await_log(b, "dropped=" + ghost, 1)
        self.await_log(b, "cursor=advanced", 1)
        lines = self.pull_lines(b)
        ghost_articles = peer.count("ARTICLE " + ghost)
        newnews = peer.newnews()
        counts = {m: self.count_article(b, m) for m in real}
        fnpl = self.fnpl_files(b)
        self.stop(b)
        self.witness("unavailable-drop", {"pull_lines": lines, "newnews": newnews,
                                          "ghost_article_commands": ghost_articles,
                                          "counts": counts, "fnpl": fnpl, "bound": bound},
                     [b])
        done = [l for l in lines if "round=done" in l]
        advanced_at = next(i for i, l in enumerate(done) if "cursor=advanced" in l)
        self.assertEqual(advanced_at, bound - 1, done)
        for l in done[:bound - 1]:
            self.assertIn("cursor=held unavailable=1", l)
            self.assertNotIn("dropped=", l)
        self.assertIn("unavailable=1 dropped=" + ghost, done[bound - 1])
        self.assertEqual(sum("dropped=" in l for l in lines), 1, lines)
        self.assertEqual(len(set(newnews[:bound])), 1, newnews)
        self.assertGreaterEqual(ghost_articles, bound)
        for m in real:
            self.assertEqual(counts[m], 1, counts)

    def test_unavailable_count_survives_a_cut(self):
        """PKT-213 at the FNPL cuts: append 2 is round 1's held close (the
        :pull-unavailable record, then the cursor record).  Killed after its
        fsync, the restarted node recovers <ghost>'s count of 1 and drops it
        after BOUND-1 more rounds (BOUND ARTICLE <ghost> in all); killed
        before its write, round 1 is not durable and the count starts again
        (BOUND+1 in all).  Either way the real articles are stored once."""
        bound = 3
        results = {}
        for cut, total in (("after-fsync:2", bound), ("before-write:2", bound + 1)):
            name = cut.replace(":", "-")
            peer, b, ghost, real = self.unavailable_pair(name, bound)
            self.env["FN_PULL_TEST_KILL"] = cut
            try:
                self.start(b)
            except Exception:
                pass
            finally:
                del self.env["FN_PULL_TEST_KILL"]
            process = b["process"]
            code = process.wait(timeout=120)
            b.pop("process")
            process.communicate(timeout=60)
            self.processes.remove(process)
            self.assertEqual(code, -signal.SIGKILL, cut)
            before = peer.count("ARTICLE " + ghost)
            self.start(b)
            self.await_log(b, "dropped=" + ghost, 1)
            self.await_log(b, "cursor=advanced", 1)
            ghost_articles = peer.count("ARTICLE " + ghost)
            counts = {m: self.count_article(b, m) for m in real}
            lines = self.pull_lines(b)
            self.stop(b)
            results[cut] = {"ghost_before_kill": before, "ghost_total": ghost_articles,
                            "counts": counts, "pull_lines": lines,
                            "log_sha256": sha256_of(b["log"])}
            self.assertEqual(before, 1, (cut, before))
            self.assertEqual(ghost_articles, total, (cut, ghost_articles, lines))
            for m in real:
                self.assertEqual(counts[m], 1, (cut, counts))
        self.witness("unavailable-cuts", results, [])

    # ------------------------------------------------------------ PKT-236 (b), (c)

    def test_tls_replay_bound_counted_by_the_server(self):
        """PKT-236 (b): the pull's duplicate-replay bound after a close cut,
        observed through TLS.  The scripted peer terminates STARTTLS itself
        and counts every ARTICLE it is sent.  B is killed after the fsync of
        its close record (append 2: the round stored both ids) and before
        that write; after the restart every ARTICLE B sends names an id not
        stored at the kill, at most once (fn-pull-recovery-asks-the-dead-
        rounds-newnews: the restarted round asks the dead round's NEWNEWS,
        and ids the local node already holds draw 435, never ARTICLE)."""
        results = {}
        for cut in ("before-write:2", "after-fsync:2"):
            name = cut.replace(":", "-")
            root = self.base / ("S" + name)
            root.mkdir()
            certificate, key = self.certificate(root, "S")
            ids = ["<tls-bound-{}-{}@example.invalid>".format(name, k) for k in range(2)]
            peer = ScriptedPeer(ids, {m: article(m, "tb" + m[11:16], path="scripted!not-for-mail")
                                      for m in ids}, tls=(certificate, key))
            self.addCleanup(peer.close)
            b = self.initialize("B" + name, ["fn.test"], "b.pull.example.invalid")
            self.command([IMAGE, "--fn", "operator", b["config"], "peer", "add", "S",
                          "s.pull.example.invalid", "127.0.0.1", str(peer.port), "fn.*",
                          "-", "source-address", "127.0.0.9", "true", "starttls",
                          "localhost", str(certificate)])
            self.command([IMAGE, "--fn", "operator", b["config"], "peer", "pull", "S",
                          INTERVAL])
            self.env["FN_PULL_TEST_KILL"] = cut
            try:
                self.start(b)
            except Exception:
                pass
            finally:
                del self.env["FN_PULL_TEST_KILL"]
            process = b["process"]
            code = process.wait(timeout=120)
            b.pop("process")
            process.communicate(timeout=60)
            self.processes.remove(process)
            self.assertEqual(code, -signal.SIGKILL, cut)
            with peer.lock:
                mark = len(peer.commands)
            self.start(b)
            for m in ids:
                self.await_article(b, m)
            self.await_log(b, "cursor=advanced", 1)
            with peer.lock:
                before = list(peer.commands[:mark])
                after = list(peer.commands[mark:])
            counts = {m: self.count_article(b, m) for m in ids}
            lines = self.pull_lines(b)
            self.stop(b)
            fetched_before = [c for c in before if c.startswith("ARTICLE ")]
            fetched_after = [c for c in after if c.startswith("ARTICLE ")]
            results[cut] = {"article_before_kill": fetched_before,
                            "article_after_restart": fetched_after,
                            "starttls": sum(c == "STARTTLS" for c in before + after),
                            "counts": counts, "pull_lines": lines,
                            "log_sha256": sha256_of(b["log"])}
            self.assertTrue(all("transport=tls" in l for l in lines if "round=" in l), lines)
            self.assertEqual(sorted(fetched_before), sorted("ARTICLE " + m for m in ids))
            # The bound: after the restart no id is fetched twice, and none
            # the node already held at the kill (append 2 follows the whole
            # round, so both ids were stored before it).
            self.assertEqual(len(fetched_after), len(set(fetched_after)), fetched_after)
            self.assertEqual(fetched_after, [], (cut, fetched_after))
            for m in ids:
                self.assertEqual(counts[m], 1, (cut, counts))
        self.witness("tls-replay-bound", results, [])

    def test_loopback_lab_exception_against_an_unprotected_server(self):
        """PKT-236 (c): the loopback-lab exception's positive arm natively.
        A requires authentication but not a protected channel
        (protected_only = false); B's record for A is a clear transport to
        the loopback literal with a credential whose profile permits clear
        text.  B authenticates in the clear (the proxy sees AUTHINFO), pulls
        both articles and advances."""
        a = self.initialize_protected("A", "nodeB", "b-secret", protected_only=False)
        b = self.initialize("B", ["fn.test"], "b.pull.example.invalid")
        self.start(a)
        proxy = RecordingProxy(a["port"])
        self.addCleanup(proxy.close)
        self.pull_protected(b, a, proxy.port, self.profile(b, "nodeB", "b-secret"),
                            tls=False, allow_clear=True)
        ids = ["<lab-one@example.invalid>", "<lab-two@example.invalid>"]
        for n, message_id in enumerate(ids):
            self.operator_post(a, message_id, "lab-{}".format(n))
        self.start(b)
        for message_id in ids:
            self.await_article(b, message_id)
        self.await_log(b, "cursor=advanced", 1)
        with proxy.lock:
            commands = list(proxy.commands)
        lines = self.pull_lines(b)
        self.stop(b)
        self.stop(a)
        self.witness("loopback-lab", {"commands": [c for c in commands
                                                   if not c.upper().startswith("AUTHINFO PASS")],
                                      "authinfo_pass_seen": any(c.upper().startswith("AUTHINFO PASS")
                                                                for c in commands),
                                      "pull_lines": lines}, [a, b])
        self.assertIn("AUTHINFO USER nodeB", commands)
        self.assertNotIn("STARTTLS", commands)
        self.assertTrue(any("transport=clear" in l and "cursor=advanced" in l for l in lines), lines)

    # ------------------------------------------------------------ the soak

    @unittest.skipUnless(os.environ.get("FN_PULL_SOAK_SECONDS"),
                         "set FN_PULL_SOAK_SECONDS for the bounded soak (runbook)")
    def test_soak_two_nodes_and_an_unproducible_listing(self):
        """SCN-095's bounded native form: B pulls a fn node A and the
        scripted peer S (which keeps listing <ghost> and answers it 430)
        once a minute for FN_PULL_SOAK_SECONDS; A receives an article every
        two minutes; B is restarted cleanly half-way.  "Days" is the claim;
        this is its bounded evidence: every article A held reaches B once,
        <ghost> is dropped exactly once at the bound (the count survives the
        restart), B's cursor for S advances, and B's RSS is sampled."""
        seconds = int(os.environ["FN_PULL_SOAK_SECONDS"])
        bound = 3
        a = self.initialize("A", ["fn.test"], "a.pull.example.invalid")
        self.start(a)
        peer, b, ghost, real = self.unavailable_pair("soak", bound)
        self.command([IMAGE, "--fn", "operator", b["config"], "peer", "add", "A",
                      "a.pull.example.invalid", "127.0.0.1", str(a["port"]), "fn.*",
                      "-", "127.0.0.8", "true"])
        for name in ("A", "S"):
            self.command([IMAGE, "--fn", "operator", b["config"], "peer", "pull",
                          name, "60", str(bound)])
        self.start(b)
        posted, rss, restarted = [], [], False
        begin = time.monotonic()
        k = 0
        while time.monotonic() - begin < seconds:
            if k % 4 == 0:
                mid = "<soak-{}@example.invalid>".format(k)
                self.post(a, article(mid, "soak-{}".format(k)))
                posted.append(mid)
            try:
                rss.append(int(Path("/proc/{}/status".format(b["process"].pid)).read_text()
                               .split("VmRSS:")[1].split()[0]))
            except (OSError, IndexError, ValueError):
                pass
            if not restarted and time.monotonic() - begin > seconds / 2:
                self.stop(b)
                self.start(b)
                restarted = True
            time.sleep(30)
            k += 1
        for mid in posted + real:
            self.await_article(b, mid, timeout=180)
        self.await_log(b, "dropped=" + ghost, 1, timeout=240)
        lines = self.pull_lines(b)
        counts = {m: self.count_article(b, m) for m in posted + real}
        self.stop(b)
        self.stop(a)
        self.witness("soak", {"seconds": seconds, "posted": len(posted),
                              "counts_all_one": all(v == 1 for v in counts.values()),
                              "rounds": len(lines),
                              "dropped_lines": [l for l in lines if "dropped=" in l],
                              "ghost_article_commands": peer.count("ARTICLE " + ghost),
                              "rss_kib_first_last_max": [rss[0], rss[-1], max(rss)] if rss else [],
                              "restarted": restarted}, [a, b])
        self.assertTrue(all(v == 1 for v in counts.values()), counts)
        self.assertEqual(sum("dropped=" + ghost in l for l in lines), 1, lines)
        self.assertEqual(peer.count("ARTICLE " + ghost), bound)

    @unittest.skipUnless(INN_READY, "set FN_INN_SRC to an installed INN 2.7 tree")
    def test_pull_from_inn(self):
        inn = InnLab(self.base / "inn", Path(INN_SRC))
        self.addCleanup(inn.stop)
        self.assertTrue(inn.start(), inn.diagnostics())
        message_id = "<pull-from-inn@inn.pull.example.invalid>"
        reply = inn.inject(message_id, article(
            message_id, "from-inn", path="inn-reader!not-for-mail"))
        self.assertTrue(reply.startswith(b"235"), reply)
        proxy = RecordingProxy(inn.nnrpd_port)
        self.addCleanup(proxy.close)
        b = self.initialize("B", ["fn.test"], "b.pull.example.invalid")
        self.pull_from(b, "INN", inn.pathhost, proxy.port)
        self.start(b)
        self.await_article(b, message_id)
        self.await_log(b, "cursor=advanced", 1)
        newnews = proxy.newnews()
        stored = self.session(b["port"], [b"HEAD " + message_id.encode() + b"\r\n"])[0]
        self.stop(b)
        self.witness("inn", {"newnews": newnews, "pull_lines": self.pull_lines(b),
                             "inn_ihave": reply.decode().strip(),
                             "fnpl": self.fnpl_files(b),
                             "b_head": stored.decode().strip()}, [b])
        self.assertTrue(newnews and newnews[0].startswith("NEWNEWS fn.* "), newnews)


class InnLab:
    """A private innd + nnrpd on free ports (after spike/mega tools/spike_peering_lab.py)."""

    pathhost = "inn.pull.example.invalid"

    def __init__(self, prefix, src):
        self.prefix, self.src = prefix, src
        self.innd_port, self.nnrpd_port = free_port(), free_port()
        self.processes = []

    def env(self):
        return dict(os.environ, INNCONF=str(self.prefix / "etc/inn.conf"))

    def setup(self):
        prefix = self.prefix
        for sub in ("bin", "lib", "etc", "share", "doc"):
            if (self.src / sub).exists():
                shutil.copytree(self.src / sub, prefix / sub, symlinks=True)
        for sub in ("spool/articles", "spool/incoming", "spool/outgoing", "spool/overview",
                    "spool/tmp", "spool/innfeed", "spool/archive", "db", "log", "run",
                    "tmp", "http"):
            (prefix / sub).mkdir(parents=True, exist_ok=True)
        user = subprocess.check_output(["id", "-un"], text=True).strip()
        group = subprocess.check_output(["id", "-gn"], text=True).strip()
        (prefix / "etc/inn.conf").write_text(
            "pathhost: {p}\ndomain: pull.example.invalid\nserver: 127.0.0.1\n"
            "mta: \"/bin/true %s\"\nport: {i}\nbindaddress: 127.0.0.1\n"
            "hismethod: hisv6\novmethod: tradindexed\nenableoverview: true\n"
            "allownewnews: true\nnnrpdloadlimit: 0\nmaxartsize: 1000000\n"
            "artcutoff: 0\nwanttrash: false\nnnrpdposthost: none\n"
            "runasuser: {u}\nrunasgroup: {g}\npathnews: {x}\nxrefslave: false\n".format(
                p=self.pathhost, i=self.innd_port, u=user, g=group, x=prefix))
        (prefix / "etc/incoming.conf").write_text(
            "streaming: true\nmax-connections: 8\npeer lab {\n"
            "    hostname: 127.0.0.1\n    patterns: fn.*\n}\n")
        (prefix / "etc/newsfeeds").write_text("ME/{}:*::\n".format(self.pathhost))
        (prefix / "etc/readers.conf").write_text(
            'auth "localhost" {\n    hosts: "localhost, 127.0.0.1, ::1"\n'
            '    default: "<localhost>"\n}\naccess "localhost" {\n'
            '    users: "<localhost>"\n    newsgroups: "*"\n    access: RPAN\n}\n')
        db = prefix / "db"
        (db / "history").write_text("")
        subprocess.run([str(prefix / "bin/makedbz"), "-i", "-f", str(db / "history")],
                       env=self.env(), check=True, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
        for ext in ("dir", "hash", "index"):
            staged = db / "history.n.{}".format(ext)
            if staged.exists():
                staged.rename(db / "history.{}".format(ext))
        (db / "active").write_text("".join(
            "{} 0000000000 0000000001 {}\n".format(g, f) for g, f in (
                ("control", "y"), ("control.cancel", "y"), ("control.newgroup", "y"),
                ("control.rmgroup", "y"), ("control.checkgroups", "y"), ("junk", "n"),
                ("fn.test", "y"))))
        (db / "active.times").write_text("")
        (db / "newsgroups").write_text("")

    def start(self):
        self.setup()
        out = open(self.prefix / "log/innd-stdout.log", "ab")
        self.processes.append(subprocess.Popen(
            [str(self.prefix / "bin/innd"), "-d"], stdout=out,
            stderr=subprocess.STDOUT, env=self.env()))
        for _ in range(60):
            mode = subprocess.run([str(self.prefix / "bin/ctlinnd"), "-t", "2", "mode"],
                                  env=self.env(), stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, text=True)
            if "Server running" in mode.stdout:
                break
            time.sleep(1)
        out2 = open(self.prefix / "log/nnrpd-stdout.log", "ab")
        self.processes.append(subprocess.Popen(
            [str(self.prefix / "bin/nnrpd"), "-D", "-f", "-p", str(self.nnrpd_port)],
            stdout=out2, stderr=subprocess.STDOUT, env=self.env()))
        for _ in range(30):
            if port_open(self.nnrpd_port):
                break
            time.sleep(1)
        return port_open(self.innd_port) and port_open(self.nnrpd_port)

    def inject(self, message_id, octets):
        for _ in range(10):
            try:
                with socket.create_connection(("127.0.0.1", self.innd_port),
                                              timeout=30) as client:
                    stream = client.makefile("rwb", buffering=0)
                    stream.readline()
                    stream.write(b"IHAVE " + message_id.encode() + b"\r\n")
                    first = stream.readline()
                    if not first.startswith(b"335"):
                        return first
                    stream.write(octets + b".\r\n")
                    return stream.readline()
            except ConnectionRefusedError:
                time.sleep(2)
        return b"refused-connection"

    def diagnostics(self):
        out = []
        for name in ("innd-stdout.log", "nnrpd-stdout.log"):
            try:
                out.append((self.prefix / "log" / name).read_text(errors="replace")[-1000:])
            except OSError:
                pass
        return "\n".join(out)

    def stop(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    process.kill()
        # innd records its own PID (it may have re-execed); signal only that.
        run = self.prefix / "run"
        for pidfile in run.glob("*.pid") if run.exists() else ():
            try:
                os.kill(int(pidfile.read_text().split()[0]), signal.SIGTERM)
            except (ValueError, ProcessLookupError, IndexError, PermissionError):
                pass


if __name__ == "__main__":
    unittest.main()
