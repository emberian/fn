"""The native operator's `[log] path` and `[posting] agent`, on a real image.

A post's service log line lands in the file `[log] path` names, the served
POST's line names the agent its article's Injection-Info carries, and that
agent is the store's `path-identity` policy; `[posting] agent` and a relative
`[log] path` are refused by `run` with the key named.  The ACL2 side of each
claim is books/owner-agent.lisp, books/owner-log.lisp and
books/native-config.lisp (fn-native-config-unsupported-key); this file is
the measurement that the image wires them.
"""
import os
from pathlib import Path
import select
import socket
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent


def image():
    """The image under test: FN_NATIVE_HOST, else the developer image."""
    named = os.environ.get("FN_NATIVE_HOST")
    if named:
        return Path(named)
    return Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                               ROOT / "build" / "fn-host-developer"))


IMAGE = image()
SKIP_REASON = ("no native image at {}: build one with tools/build_native_host.sh "
               "(FN_NATIVE_PROFILE=developer) or name one with FN_NATIVE_HOST or "
               "FN_NATIVE_DEVELOPER_HOST".format(IMAGE))
IDENTITY = "profile.example.invalid"


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    for name in ("FN_HOST", "FN_NATIVE_CONTROL_TEST_STOP",
                 "FN_NATIVE_CONTROL_FAULT", "FN_NATIVE_POST_FAULT",
                 "FN_NATIVE_OWNER_TEST_SIGTERM",
                 "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP",
                 "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT"):
        env.pop(name, None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK), SKIP_REASON)
class NativeProfileTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-profile-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.log = self.root / "log" / "fn.log"
        self.log.parent.mkdir()
        self.port = free_port()
        initialized = self.image("store", str(self.store), "init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())

    def image(self, *words, timeout=180):
        return subprocess.run([str(IMAGE), "--fn"] + list(words), cwd=ROOT,
                              env=environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout, check=False)

    def config(self, name, extra=""):
        path = self.root / name
        path.write_text(
            "[store]\npath = \"{}\"\n"
            "[listener]\nhost = \"127.0.0.1\"\nport = {}\n"
            "[control]\npath = \"{}\"\n{}".format(
                self.store, self.port, self.root / "control.sock", extra),
            encoding="ascii")
        return path

    def start(self, config):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(config), "run"], cwd=ROOT,
            env=environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        self.addCleanup(self.stop, process)
        lines = []
        for _ in range(6):
            ready = select.select([process.stdout], [], [], 180)[0]
            self.assertTrue(ready, "the owner did not become ready: {}".format(lines))
            line = process.stdout.readline()
            lines.append(line)
            if line.startswith(b"LISTENING "):
                return process
            if process.poll() is not None:
                self.fail("owner exited: {} {}".format(
                    lines, process.stderr.read().decode("utf-8", "replace")))
        self.fail("no LISTENING line: {!r}".format(lines))

    @staticmethod
    def stop(process):
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=120)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()

    def served_post(self, message_id):
        """POST one article over NNTP; return the final reply line."""
        with socket.create_connection(("127.0.0.1", self.port), timeout=60) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            stream.write(b"POST\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"340"))
            stream.write(b"From: author@example.invalid\r\n"
                         b"Newsgroups: fn.test\r\n"
                         b"Subject: the service log\r\n"
                         b"Message-ID: " + message_id.encode("ascii") + b"\r\n"
                         b"\r\nserved body\r\n.\r\n")
            stream.flush()
            reply = stream.readline()
            stream.write(b"ARTICLE " + message_id.encode("ascii") + b"\r\n")
            stream.flush()
            head = stream.readline()
            article = b""
            if head.startswith(b"220"):
                while True:
                    line = stream.readline()
                    if line in (b".\r\n", b""):
                        break
                    article += line
            stream.write(b"QUIT\r\n")
            stream.flush()
            return reply, article

    def control_post(self, config, message_id):
        payload = self.root / "control.article"
        payload.write_bytes(b"From: author@example.invalid\r\n"
                            b"Newsgroups: fn.test\r\n"
                            b"Subject: control\r\n"
                            b"Date: Tue, 22 Sep 2026 09:00:00 +0000\r\n"
                            b"Message-ID: " + message_id.encode("ascii") +
                            b"\r\n\r\ncontrol body\r\n")
        return self.image("operator", str(config), "post", "--message-id",
                          message_id, "--payload", str(payload), "--group",
                          "fn.test", timeout=120)

    def wait_for_log(self, needle, seconds=30):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            text = self.log.read_text(encoding="ascii") if self.log.exists() else ""
            if needle in text:
                return text
            time.sleep(0.2)
        return self.log.read_text(encoding="ascii") if self.log.exists() else ""

    def test_posts_land_in_the_configured_log_and_name_the_path_identity(self):
        config = self.config("fn.toml", "[log]\npath = \"{}\"\n".format(self.log))
        policy = self.image("operator", str(config), "policy", "set",
                            "path-identity", IDENTITY)
        self.assertEqual(policy.returncode, 0, policy.stderr.decode())
        # A line written before this run must survive it: the file is
        # opened append-only and never truncated.
        self.log.write_text("earlier line\n", encoding="ascii")
        owner = self.start(config)

        reply, article = self.served_post("<served-log@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        self.assertIn("Injection-Info: {}\r\n".format(IDENTITY).encode("ascii"),
                      article)
        self.assertIn("Path: {}!".format(IDENTITY).encode("ascii"), article)

        control = self.control_post(config, "<control-log@example.invalid>")
        self.assertEqual(control.returncode, 0, control.stderr.decode())

        text = self.wait_for_log("message-id=<control-log@example.invalid>")
        lines = text.splitlines()
        self.assertEqual(lines[0], "earlier line")
        self.assertTrue(any(line.startswith("accepted reader connection=")
                            for line in lines), lines)
        served = [line for line in lines
                  if "message-id=<served-log@example.invalid>" in line]
        self.assertEqual(len(served), 1, lines)
        self.assertTrue(served[0].startswith("accepted post path=served "), served)
        self.assertIn(" agent={} ".format(IDENTITY), served[0])
        controlled = [line for line in lines
                      if "message-id=<control-log@example.invalid>" in line]
        self.assertEqual(len(controlled), 1, lines)
        self.assertTrue(controlled[0].startswith("accepted post path=control "),
                        controlled)
        # Nothing of the log went to stderr when a file was configured.
        self.stop(owner)
        self.assertNotIn(b"path=served", owner.stderr.read())

    def test_without_a_log_path_the_lines_go_to_stderr(self):
        config = self.config("fn.toml")
        owner = self.start(config)
        control = self.control_post(config, "<stderr-log@example.invalid>")
        self.assertEqual(control.returncode, 0, control.stderr.decode())
        self.stop(owner)
        self.assertIn(b"accepted post path=control "
                      b"message-id=<stderr-log@example.invalid>",
                      owner.stderr.read())
        self.assertFalse(self.log.exists())

    def test_posting_agent_and_a_relative_log_are_refused_by_name(self):
        for name, extra, key in (
                ("agent.toml", "[posting]\nagent = \"fn@hbox.ember.software\"\n",
                 b"UNSUPPORTED-PROFILE agent"),
                ("relative.toml", "[log]\npath = \"fn.log\"\n",
                 b"UNSUPPORTED-PROFILE log")):
            with self.subTest(name=name):
                result = self.image("operator", str(self.config(name, extra)), "run",
                                    timeout=120)
                self.assertEqual(result.returncode, 5, result.stderr.decode())
                self.assertIn(key, result.stderr)
