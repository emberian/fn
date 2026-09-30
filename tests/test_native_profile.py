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
import time
import unittest

from tests.native_harness import EXIT, Node, article, executable, native_image

# The image under test: FN_NATIVE_HOST, else the developer image.
IMAGE = (native_image("FN_NATIVE_HOST") if os.environ.get("FN_NATIVE_HOST")
         else native_image("FN_NATIVE_DEVELOPER_HOST"))
SKIP_REASON = ("no native image at {}: build one with tools/build_native_host.sh "
               "(FN_NATIVE_PROFILE=developer) or name one with FN_NATIVE_HOST or "
               "FN_NATIVE_DEVELOPER_HOST".format(IMAGE))
IDENTITY = "profile.example.invalid"


@unittest.skipUnless(executable(IMAGE), SKIP_REASON)
class NativeProfileTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.root, self.store, self.port = self.node.root, self.node.store_path, self.node.port
        self.log = self.root / "log" / "fn.log"
        self.log.parent.mkdir()
        self.node.store("init", "fn.test", expect=EXIT.OK)

    def image(self, *words, timeout=180):
        return self.node.invoke(*words, timeout=timeout)

    def config(self, name, extra=""):
        """The node's fn.toml with EXTRA (a table) after its [listener] fields."""
        self.node.write_config(extra=extra)
        return self.node.config

    def start(self, config):
        return self.node.start()

    def stop(self, process):
        self.node.stop(expect=None, process=process)

    def served_post(self, message_id):
        """POST one article over NNTP; the final reply line and the ARTICLE served."""
        with self.node.session() as client:
            _, reply = client.post(article(message_id, subject="the service log",
                                           date=None, body=b"served body\r\n"))
            return reply, client.article(message_id) or b""

    def control_post(self, config, message_id):
        return self.node.post(message_id, article(
            message_id, subject="control", date="Tue, 22 Sep 2026 09:00:00 +0000",
            body=b"control body\r\n"), timeout=120)

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
        connections = [line for line in lines
                       if line.startswith("accepted reader connection=")]
        self.assertTrue(connections, lines)
        # Q10d: one accepted socket line includes its actual loopback client
        # address; the host neither formats nor substitutes a peer identity.
        for line in connections:
            self.assertEqual(line.count(" client-address="), 1, line)
            self.assertTrue(line.endswith(" client-address=127.0.0.1"), line)
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
        self.assertNotIn(b"path=served", owner.stderr.since(0))

    def test_without_a_log_path_the_lines_go_to_stderr(self):
        config = self.config("fn.toml")
        owner = self.start(config)
        control = self.control_post(config, "<stderr-log@example.invalid>")
        self.assertEqual(control.returncode, 0, control.stderr.decode())
        self.stop(owner)
        self.assertIn(b"accepted post path=control "
                      b"message-id=<stderr-log@example.invalid>",
                      owner.stderr.since(0))
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
                self.assertEqual(result.returncode, EXIT.USAGE, result.stderr.decode())
                self.assertIn(key, result.stderr)
