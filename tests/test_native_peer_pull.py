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
- test_pull_from_inn: INN (FN_INN_SRC, an installed INN 2.7 tree) holds an
  article in fn.test; B pulls it from nnrpd and stores it.

Run: FN_NATIVE_HOST=<launcher> [FN_INN_SRC=/tank/fn/inn/2.7.4] \
     python3 -m unittest -v tests.test_native_peer_pull
"""

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
                stored_at_death = {i: self.stored(b, i) for i in ids}
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
                results[label] = {"stored_at_death": stored_at_death,
                                  "newnews_after": newnews[:2],
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
