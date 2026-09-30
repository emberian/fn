#!/usr/bin/env python3
"""SCN-076, the operator walk (HST-008, HST-009): one INSTALLED `fn` from
nothing to a recovered node, on scratch nodes.

packaging/install-native.sh installs the production image (FN_NATIVE_HOST)
into a scratch prefix once per class; every command after that is
PREFIX/bin/fn, never the image.  The steps are those of
planning/evidence/operator-walk-2026-09-26/walk.sh, split into cases that
each fit the per-test budget, and every wait ends on an observation (the
owner's LISTENING line, a log line, the peer's MODE STREAM count), never a
fixed sleep.  Exit codes are the ACL2 outcome table's (tools/outcome_codes.py)
and health's (specs/host.md "Operator health": 20 plus the first held state,
19 when none is held and one is unobserved, 0 when every state is clear).

D34 (fresh deploys, no migrations) retired the walk's upgrade rehearsal and
`rollback-check`: the backup step is docs/operator.md section 9's (stop, copy
the node folder, start) and its restore on a copy.
"""
import hashlib
import os
import re
import shutil
import signal
import sys
import socket
import ssl
import subprocess
import tempfile
import threading
import time
import unittest
from pathlib import Path

from tests.native_harness import ROOT, Node, durable_root, free_port, native_image, requires
from tools.outcome_codes import EXIT

IMAGE = native_image("FN_NATIVE_HOST")
MISSION = "small-community"
# The mission's article bound (1 MiB, test_native_heap_from_profile).
ARTICLE_BOUND = 1048576
# health (docs/operator.md "health"): every state clear; the node not running
# (fn-nh-not-running-report); unavailable-peer held (20 + its index, 6).
HEALTH_CLEAR, HEALTH_NOT_RUNNING, HEALTH_UNAVAILABLE_PEER = 0, 18, 26


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace")


def article(tag, body=None):
    body = body if body is not None else "body {}".format(tag).encode("ascii")
    return (b"From: walk@example.invalid\r\nNewsgroups: local.test\r\n"
            b"Subject: walk " + tag.encode("ascii") + b"\r\n"
            b"Date: Sat, 26 Sep 2026 02:00:00 +0000\r\n"
            b"Message-ID: <walk-" + tag.encode("ascii") + b"@example.invalid>\r\n\r\n"
            + body + b"\r\n")


def until(predicate, timeout, what):
    """PREDICATE() true within TIMEOUT seconds (polled every 50 ms), else fail."""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        value = predicate()
        if value:
            return value
        time.sleep(0.05)
    raise AssertionError("not within {} s: {}".format(timeout, what))


class NoStreamPeer:
    """A loopback NNTP peer that answers 501 to MODE STREAM (RFC 4644 2.3)
    and takes IHAVE; it decides nothing, it counts the commands it read."""

    def __init__(self, mode_answer=b"501 streaming not supported"):
        self.mode_answer = mode_answer
        self.lines = []
        self.lock = threading.Lock()
        self.socket = socket.socket()
        self.socket.bind(("127.0.0.1", 0))
        self.socket.listen(4)
        self.port = self.socket.getsockname()[1]
        threading.Thread(target=self._accept, daemon=True).start()

    def count(self, prefix):
        with self.lock:
            return sum(1 for line in self.lines if line.upper().startswith(prefix.upper()))

    def _accept(self):
        while True:
            try:
                conn, _ = self.socket.accept()
            except OSError:
                return
            threading.Thread(target=self._serve, args=(conn,), daemon=True).start()

    def _serve(self, conn):
        with conn, conn.makefile("rwb") as f:
            f.write(b"200 nostream ready\r\n")
            f.flush()
            for line in f:
                with self.lock:
                    self.lines.append(line.rstrip(b"\r\n"))
                word = line.split(b" ", 1)[0].strip().upper()
                if word == b"QUIT":
                    f.write(b"205 bye\r\n")
                    f.flush()
                    return
                if word == b"IHAVE":
                    f.write(b"335 send it\r\n")
                    f.flush()
                    for body in f:
                        if body in (b".\r\n", b".\n"):
                            break
                    f.write(b"235 thanks\r\n")
                elif word == b"MODE":
                    f.write(self.mode_answer + b"\r\n")
                elif word == b"CAPABILITIES":
                    f.write(b"101 capabilities\r\nVERSION 2\r\nIHAVE\r\n.\r\n")
                else:
                    f.write(b"500 unknown\r\n")
                f.flush()

    def close(self):
        self.socket.close()


@requires(IMAGE)
class OperatorWalkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # A durable mount: a mission's init requires durable storage
        # (store-mount-identity, PKT-670) and /tmp is tmpfs on hbox; a short
        # prefix keeps store/control.sock inside a Unix socket's path.
        cls.tmp = Path(tempfile.mkdtemp(prefix="ow-", dir=durable_root()))
        cls.addClassCleanup(shutil.rmtree, cls.tmp, True)
        prefix = cls.tmp / "prefix"
        installed = subprocess.run(
            ["sh", "packaging/install-native.sh"], cwd=ROOT, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=120, check=False,
            env=dict(os.environ, FN_NATIVE_HOST=str(IMAGE), FN_NATIVE_CORE=str(IMAGE) + ".core",
                     FN_NATIVE_SOURCE_REVISION="operator-walk", PREFIX=str(prefix)))
        if installed.returncode != 0:
            raise AssertionError("install-native.sh exit {}: {}".format(
                installed.returncode, installed.stdout.decode("utf-8", "replace")[-4096:]))
        cls.fn = prefix / "bin" / "fn"
        cls.installed_host = prefix / "libexec" / "fn" / "fn-host.core"

    def test_the_installed_image_is_the_production_image(self):
        digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
        self.assertTrue(os.access(self.fn, os.X_OK))
        self.assertEqual(digest(self.installed_host), digest(str(IMAGE) + ".core"))

    def setUp(self):
        self.began = time.monotonic()

    def mark(self, label):
        """A step's elapsed time on stderr: the budget report names the test,
        this names the step inside it."""
        print("walk {:7.2f} s {}".format(time.monotonic() - self.began, label),
              file=sys.stderr, flush=True)

    # --- one node from a mission ------------------------------------------

    def node(self, name):
        """A node whose fn.toml `mission` writes (loopback, a fresh port),
        with the self-signed pair the image makes at ROOT/tls (row Q10a:
        `--tls-name', no `openssl' program)."""
        root = Path(tempfile.mkdtemp(prefix=name + "-", dir=self.tmp))
        # Keep each not-yet-started node's port bound while mission/configuration
        # runs. Two closed free_port probes may otherwise choose the same port.
        reservation = socket.socket()
        self.addCleanup(reservation.close)
        reservation.bind(("127.0.0.1", 0))
        node = Node(self, IMAGE, root=root, name=name, launcher=str(self.fn), control=False,
                    port=reservation.getsockname()[1])
        node.config.unlink()
        node.operator("mission", MISSION, "--port", str(node.port),
                      "--tls-name", "127.0.0.1", expect=EXIT.OK)
        node.log = root / "log" / "fn.log"
        return self.timed(node, before_start=reservation.close)

    def timed(self, node, before_start=None):
        """NODE's commands, starts and stops each marked with their duration."""
        for verb in ("invoke", "start", "stop"):
            def wrapped(*words, _verb=verb, _inner=getattr(node, verb), **options):
                began = time.monotonic()
                try:
                    if _verb == "start" and before_start is not None:
                        # Native fn binds its own socket. Release only this
                        # node's reservation immediately before starting it.
                        before_start()
                    return _inner(*words, **options)
                finally:
                    label = " ".join(str(w) for w in words[2:4]) if _verb == "invoke" else _verb
                    self.mark("{} {} took {:.2f} s".format(node.name, label,
                                                          time.monotonic() - began))
            setattr(node, verb, wrapped)
        return node

    def initialized(self, name, identity):
        node = self.node(name)
        node.operator("init", expect=EXIT.OK)
        node.operator("policy", "set", "path-identity", identity, expect=EXIT.OK)
        return node

    def log_count(self, node, needle):
        try:
            return node.log.read_text(encoding="utf-8", errors="replace").count(needle)
        except FileNotFoundError:
            return 0

    def post(self, node, tag, expect=EXIT.OK, body=None):
        result = node.post("<walk-{}@example.invalid>".format(tag), article(tag, body),
                           group="local.test", expect=expect)
        return result

    # --- the walk ---------------------------------------------------------

    def test_before_init_every_verb_is_refused_no_store_and_init_takes_no_profile_word(self):
        root = Path(tempfile.mkdtemp(prefix="pre-", dir=self.tmp))
        missing = Node(self, IMAGE, root=root, launcher=str(self.fn), listener=False,
                       control=False)
        missing.config.unlink()
        help_ = missing.operator("help", expect=EXIT.OK)
        self.assertIn(b"usage: fn operator CONFIG", help_.stdout)
        status = missing.operator("status", expect=EXIT.USAGE)
        self.assertIn("configuration file is missing", text(status))

        node = self.node("a")
        for verb in (("status",), ("health",), ("run", "--once")):
            refused = node.operator(*verb, expect=EXIT.REFUSED)
            self.assertIn("NO-STORE", text(refused), verb)
            self.assertIn(" init", text(refused), "{}: no init line".format(verb))
            self.assertNotIn("fault", text(refused).lower(), verb)
        self.assertFalse(node.store_path.exists())
        profile = node.operator("init", "--profile", "scale", expect=EXIT.USAGE)
        self.assertIn("MISSION-FIXES-PROFILE", text(profile))
        self.assertFalse(node.store_path.exists())
        node.operator("init", expect=EXIT.OK)
        again = node.operator("init", expect=EXIT.REFUSED)
        self.assertIn("STORE-EXISTS", text(again))
        port = node.operator("show", "listener", "port", expect=EXIT.OK)
        self.assertIn(str(node.port).encode(), port.stdout)
        node.operator("policy", "set", "path-identity", "a.walk.invalid", expect=EXIT.OK)
        node.operator("status", expect=EXIT.OK)
        node.operator("health", expect=HEALTH_NOT_RUNNING)

    def test_two_peered_nodes_carry_a_post_and_refuse_one_over_the_article_bound(self):
        a = self.initialized("a", "a.walk.invalid")
        b = self.initialized("b", "b.walk.invalid")
        enrolled = a.operator("principal", "set-password", "walker", "--posting",
                              input=b"walk-secret-1\nwalk-secret-1\n", expect=EXIT.OK)
        self.assertIn("effective-at-next-start", text(enrolled))
        principals = a.operator("principal", "list", expect=EXIT.OK)
        self.assertIn(b"walker", principals.stdout)
        a.operator("peer", "add", "b", "b.walk.invalid", "127.0.0.1", str(b.port), "-",
                   "local.*", "127.0.0.1", "true", expect=EXIT.OK)
        b.operator("peer", "add", "a", "a.walk.invalid", "127.0.0.1", str(a.port), "local.*",
                   "-", "127.0.0.1", "true", expect=EXIT.OK)
        peers = a.operator("peer", "list", expect=EXIT.OK)
        self.assertIn(b"b.walk.invalid", peers.stdout)
        self.mark("set up")
        a.start()
        b.start()
        self.mark("both listening")
        a.operator("status", expect=EXIT.OK)
        self.post(a, "1")
        self.mark("posted")
        until(lambda: self.log_count(b, "accepted peer"), 15, "b's log names the accepted peer a")
        until(lambda: self.log_count(a, " feed "), 15, "a's log names its feed to b")
        self.mark("fed")
        b.operator("status", expect=EXIT.OK)
        a.operator("health", expect=HEALTH_CLEAR)
        over = self.post(a, "big", expect=EXIT.REFUSED, body=b"x" * (ARTICLE_BOUND + 51424))
        self.assertIn("REFUSED", text(over))

    def nostream(self, mode_answer):
        """A started node A feeding local.* to a streaming-configured peer
        that answers MODE STREAM with MODE_ANSWER, after one post."""
        peer = NoStreamPeer(mode_answer)
        self.addCleanup(peer.close)
        a = self.initialized("a", "a.walk.invalid")
        a.operator("peer", "add", "nostream", "ns.walk.invalid", "127.0.0.1", str(peer.port),
                   "-", "local.*", "127.0.0.9", "true", expect=EXIT.OK)
        a.start()
        self.post(a, "2")
        return a, peer

    def logged(self, a, peer, needle):
        try:
            until(lambda: self.log_count(a, needle), 15, "a logs " + needle)
        except AssertionError as failure:
            raise AssertionError("{}\npeer read {!r}\na's log:\n{}".format(
                failure, peer.lines, a.log.read_text(errors="replace")[-4000:]
                if a.log.exists() else "(none)")) from None
        return [line for line in a.log.read_text(encoding="utf-8").splitlines()
                if needle in line]

    def test_a_peer_answering_501_to_mode_stream_is_fed_with_ihave(self):
        """RFC 4644 2.3: 501 is `streaming not supported'; the owner falls
        back to IHAVE (RFC 3977 6.3.2) on the same connection
        (fn-fc-mode-stream-unsupported-falls-back-to-ihave)."""
        a, peer = self.nostream(b"501 streaming not supported")
        line = self.logged(a, peer, "mode-stream-unsupported")
        self.assertEqual(len(line), 1, line)
        self.assertIn("peer=nostream", line[0])
        until(lambda: peer.count(b"IHAVE <walk-2@example.invalid>"), 15, "the peer is offered walk-2")
        self.assertEqual(peer.count(b"MODE STREAM"), 1, peer.lines)
        a.operator("health", expect=HEALTH_CLEAR)

    def test_a_peer_refusing_mode_stream_otherwise_is_stopped_by_name_and_not_redialled(self):
        """Any other answer but 203 stops the peer by name for this run
        (fn-fc-mode-stream-refusal-stops-the-dial, fn-fc-dial-allowedp)."""
        a, peer = self.nostream(b"502 not for you")
        line = self.logged(a, peer, "reason=mode-stream-refused")
        self.assertEqual(len(line), 1, line)
        self.assertIn("peer=nostream", line[0])
        # New work wakes the feed (as the first post did); the stopped peer
        # is not dialled for it.
        self.post(a, "2b")
        a.operator("health", expect=HEALTH_UNAVAILABLE_PEER)
        self.assertEqual(peer.count(b"MODE STREAM"), 1, peer.lines)
        self.assertEqual(peer.count(b"IHAVE"), 0, peer.lines)

    def test_backup_of_the_stopped_node_restored_on_a_copy_and_recovered(self):
        """docs/operator.md section 9, "Back up": stop, copy the node folder,
        start.  D34 retired `store needs-upgrade', `upgrade-profile' and
        `rollback-check' (one store format, a new release is a fresh
        install), so the restore is the operator's: the copy replaces a
        store, `recover' and `run' serve it."""
        a = self.initialized("a", "a.walk.invalid")
        a.start()
        self.post(a, "1")
        a.stop()
        self.mark("first run")
        backup = a.root / "backup"
        backup.mkdir()
        for part in ("store", "tls", "fn.toml"):
            subprocess.run(["cp", "-a", str(a.root / part), str(backup / part)], check=True)
        a.start()
        self.post(a, "3")
        self.post(a, "4")
        a.stop()
        self.mark("second run")

        # The restore, on a copy with its own port.  Row S8: the mission's
        # paths are relative to fn.toml's directory, so no path is rewritten.
        # Beside A, not inside it: store/control.sock must stay within a Unix
        # socket's 103 octets.
        copy = Path(tempfile.mkdtemp(prefix="c-", dir=self.tmp))
        for part in ("store", "tls"):
            subprocess.run(["cp", "-a", str(backup / part), str(copy / part)], check=True)
        (copy / "log").mkdir()
        port = free_port()
        config = (backup / "fn.toml").read_text(encoding="utf-8")
        self.assertNotIn(str(a.root), config, "the mission wrote an absolute node path")
        config = re.sub(r"(?m)^port=\d+$", "port={}".format(port), config)
        c = self.timed(Node(self, IMAGE, root=copy, name="copy", launcher=str(self.fn),
                            control=False, port=port))
        c.config.write_text(config, encoding="utf-8")
        c.operator("recover", expect=EXIT.OK)
        c.operator("status", expect=EXIT.OK)
        c.start()
        self.mark("restored copy listening")
        # The restored store holds the backup's article and not the later two.
        # (A duplicate is accepted, exit 0, "already satisfied": the word says which.)
        again = self.post(c, "1")
        later = self.post(c, "3")
        self.assertIn("DUPLICATE", text(again), "the backup's article is new")
        self.assertIn("ACCEPTED", text(later), "a later article was restored")
        c.operator("health", expect=HEALTH_CLEAR)

    def test_a_node_moved_by_copying_its_directory(self):
        """Row S8, moving a node: stop, copy the node directory elsewhere,
        start the copy.  fn.toml's paths are relative to its own directory,
        so the copy serves its own store, log and socket and the original is
        left as it was; nothing in fn.toml is edited."""
        a = self.initialized("m", "m.walk.invalid")
        a.start()
        self.post(a, "moved-1")
        a.stop()
        before = sorted(p.name for p in (a.root / "store").iterdir())
        moved = Path(tempfile.mkdtemp(prefix="mv-", dir=self.tmp)) / "node"
        subprocess.run(["cp", "-a", str(a.root), str(moved)], check=True)
        written = (moved / "fn.toml").read_bytes()
        self.assertNotIn(str(a.root).encode(), written, "fn.toml names the old directory")
        m = self.timed(Node(self, IMAGE, root=moved, name="moved", launcher=str(self.fn),
                            control=False, port=a.port))
        m.config.write_bytes(written)  # the harness wrote its own; the copy's, byte for byte
        m.log = moved / "log" / "fn.log"
        # Same file system: nothing to rebind; `status' opens the moved store.
        m.operator("status", expect=EXIT.OK)
        m.start()
        self.mark("moved node listening")
        self.assertIn("DUPLICATE", text(self.post(m, "moved-1")), "the moved store")
        self.assertIn("ACCEPTED", text(self.post(m, "moved-2")))
        m.stop()
        self.assertGreater(m.log.stat().st_size, 0, "the moved node logs in its own directory")
        # The original was not written by the moved node.
        self.assertEqual(sorted(p.name for p in (a.root / "store").iterdir()), before)
        a.start()
        self.assertIn("ACCEPTED", text(self.post(a, "moved-2")), "the original's own store")
        a.stop()

    def no_openssl_path(self):
        """A PATH with every program of /usr/bin and /bin but `openssl'."""
        bin_dir = Path(tempfile.mkdtemp(prefix="no-openssl-", dir=self.tmp))
        for source in (Path("/usr/bin"), Path("/bin")):
            for program in source.iterdir():
                target = bin_dir / program.name
                if program.name != "openssl" and not target.exists():
                    target.symlink_to(program)
        return str(bin_dir)

    def test_a_node_on_tls_from_the_mission_with_no_openssl_program(self):
        """Row Q10a: `mission --tls-port P --tls-name 127.0.0.1' with no
        `openssl' program on PATH writes the self-signed pair beside fn.toml
        (the key at 0600), the node serves NNTP over TLS on P with it, a
        client that trusts tls/cert.pem verifies the handshake against the
        name 127.0.0.1, and `tls self-signed' refuses to replace it."""
        path = self.no_openssl_path()
        env = {"PATH": path}
        root = Path(tempfile.mkdtemp(prefix="tls-", dir=self.tmp))
        node = self.timed(Node(self, IMAGE, root=root, name="tls", launcher=str(self.fn),
                               control=False, port=free_port()))
        node.config.unlink()
        tls_port = free_port()
        node.operator("mission", MISSION, "--port", str(node.port), "--tls-port", str(tls_port),
                      "--tls-name", "127.0.0.1", "--tls-name", "localhost",
                      env=env, expect=EXIT.OK)
        cert, key = root / "tls" / "cert.pem", root / "tls" / "key.pem"
        self.assertTrue(cert.read_bytes().startswith(b"-----BEGIN CERTIFICATE-----\n"))
        self.assertTrue(key.read_bytes().startswith(b"-----BEGIN EC PRIVATE KEY-----\n"))
        self.assertEqual(key.stat().st_mode & 0o777, 0o600)
        self.assertIn("tls_port = {}".format(tls_port), node.config.read_text(encoding="utf-8"))
        node.log = root / "log" / "fn.log"
        node.operator("init", env=env, expect=EXIT.OK)
        node.start(env=env)
        context = ssl.create_default_context(cafile=str(cert))
        for name in ("127.0.0.1", "localhost"):
            with socket.create_connection(("127.0.0.1", tls_port), timeout=30) as raw:
                with context.wrap_socket(raw, server_hostname=name) as tls:
                    self.assertEqual(tls.getpeercert()["subject"], ((("commonName", "127.0.0.1"),),))
                    self.assertRegex(tls.recv(512), rb"^20[01] ")
        # A name the certificate does not carry fails verification.
        with socket.create_connection(("127.0.0.1", tls_port), timeout=30) as raw:
            with self.assertRaises(ssl.SSLCertVerificationError):
                context.wrap_socket(raw, server_hostname="news.example.org")
        node.stop()
        # Refused by name, and nothing written, while the pair is there.
        before = cert.read_bytes()
        refused = node.operator("tls", "self-signed", "127.0.0.1", env=env, expect=EXIT.REFUSED)
        self.assertIn(b"EXISTS", refused.stdout + refused.stderr)
        self.assertEqual(cert.read_bytes(), before)
        # With both files gone it makes a new pair (other names, 2 days).
        cert.unlink()
        key.unlink()
        node.operator("tls", "self-signed", "localhost", "--days", "2", env=env, expect=EXIT.OK)
        self.assertNotEqual(cert.read_bytes(), before)
        self.assertEqual(key.stat().st_mode & 0o777, 0o600)
        bad = node.operator("tls", "self-signed", "0.0.0.0", env=env, expect=EXIT.REFUSED)
        self.assertIn(b"TLS-NAME", bad.stdout + bad.stderr)

    def test_sigkill_of_the_owner_then_status_recover_run_and_health(self):
        a = self.initialized("a", "a.walk.invalid")
        owner = a.start()
        self.post(a, "1")
        self.mark("posted")
        owner.signal(signal.SIGKILL)
        owner.wait(timeout=15)
        owner.finish()
        a.process = None
        self.mark("killed")
        self.assertTrue((a.store_path / "control.sock").exists(),
                        "the killed owner's control socket file stays")
        a.operator("status", expect=EXIT.OK)
        self.mark("status")
        a.operator("recover", expect=EXIT.OK)
        self.mark("recover")
        a.start()
        self.mark("listening again")
        a.operator("health", expect=HEALTH_CLEAR)
        a.operator("status", expect=EXIT.OK)
        self.mark("health and status")


if __name__ == "__main__":
    unittest.main()
