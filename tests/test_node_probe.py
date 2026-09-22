"""tools/node_probe.py against a fake node that speaks just enough NNTP.

The fake is `tests/fake_node.py`, which wraps its socket in real TLS with a
certificate openssl writes for the run, so the probe's handshake, its
483-before-TLS assertion, its login and its fresh-connection reread are
exercised end to end over loopback.  Each test names
the one thing about the node it changes and the verdict that change must
produce; the exit code is asserted on every run because it is the part a
shell script reads.
"""
import contextlib
import io
import json
import os
import pathlib
import shutil
import socket
import sys
import tempfile
import unittest
from unittest import mock

from tests.fake_node import FakeNode, make_pair

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import node_probe  # noqa: E402


@unittest.skipUnless(shutil.which("openssl"), "no openssl to make a certificate")
class NodeProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.dir = pathlib.Path(cls.tmp.name)
        cls.cert, cls.key = make_pair(cls.dir)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def probe(self, node, password="right", extra=(), cafile=None):
        out = io.StringIO()
        record = self.dir / ("record-%d.json" % node.port)
        argv = ["127.0.0.1", str(node.port), "--cafile", str(cafile or self.cert),
                "--group", "fn.agents", "--json", str(record), "--timeout", "10"] + list(extra)
        with mock.patch.dict(os.environ, {"FN_PROBE_USER": "yue", "FN_PROBE_PASSWORD": password}):
            with contextlib.redirect_stdout(out):
                code = node_probe.main(argv)
        summary = json.loads(record.read_text())
        return code, summary, out.getvalue()

    def serve(self, **kw):
        node = FakeNode(self.cert, self.key, **kw)
        node.start()
        self.addCleanup(node.stop)
        return node

    def verdicts(self, summary):
        return {s["step"]: s["verdict"] for s in summary["steps"]}

    def test_a_correct_node_holds_every_assertion_and_the_post_comes_back(self):
        node = self.serve()
        code, summary, text = self.probe(node)
        self.assertEqual(code, 0, text)
        self.assertEqual(set(self.verdicts(summary).values()), {"held"})
        self.assertIn(summary["message_id"], node.articles)
        self.assertEqual(summary["tls"]["version"][:3], "TLS")
        self.assertIn("AUTHINFO PASS *", node.seen)
        self.assertEqual(self.verdicts(summary)["second:login"], "held")
        self.assertEqual([s for s in node.seen if s == "STARTTLS"], ["STARTTLS", "STARTTLS"])

    def test_a_node_that_would_take_the_password_in_the_clear_is_violated_and_never_gets_it(self):
        node = self.serve(protected_only=False)
        code, summary, text = self.probe(node)
        self.assertEqual(code, 1, text)
        v = self.verdicts(summary)
        self.assertEqual(v["first:authinfo-before-tls-refused"], "violated")
        self.assertEqual(v["first:starttls"], "undecided")
        self.assertEqual(v["post"], "undecided")
        self.assertNotIn("AUTHINFO PASS *", node.seen)

    def test_a_wrong_password_is_violated_and_nothing_after_it_is_decided(self):
        node = self.serve()
        code, summary, text = self.probe(node, password="wrong")
        self.assertEqual(code, 1, text)
        v = self.verdicts(summary)
        self.assertEqual(v["first:login"], "violated")
        self.assertEqual(v["first:starttls"], "held")
        self.assertEqual(v["group"], "undecided")
        self.assertEqual(v["reread-fresh-connection"], "undecided")

    def test_a_refused_post_is_violated_and_the_reread_is_undecided(self):
        node = self.serve(accept_post=False)
        code, summary, text = self.probe(node)
        self.assertEqual(code, 1, text)
        v = self.verdicts(summary)
        self.assertEqual(v["group"], "held")
        self.assertEqual(v["post"], "violated")
        self.assertEqual(v["reread-fresh-connection"], "undecided")

    def test_a_certificate_the_client_does_not_trust_is_a_violated_handshake(self):
        other = pathlib.Path(tempfile.mkdtemp(dir=self.dir))
        cert, _ = make_pair(other)
        node = self.serve()
        code, summary, text = self.probe(node, cafile=cert)
        self.assertEqual(code, 1, text)
        v = self.verdicts(summary)
        self.assertEqual(v["first:starttls"], "violated")
        self.assertEqual(v["first:login"], "undecided")
        self.assertNotIn("AUTHINFO PASS *", node.seen)

    def test_an_unreachable_node_decides_nothing_and_exits_3(self):
        spare = socket.socket()
        spare.bind(("127.0.0.1", 0))
        port = spare.getsockname()[1]
        spare.close()
        node = mock.Mock(port=port)
        code, summary, text = self.probe(node)
        self.assertEqual(code, 3, text)
        self.assertEqual(set(self.verdicts(summary).values()), {"undecided"})

    def test_no_post_stops_after_the_group_and_is_not_a_pass(self):
        node = self.serve()
        code, summary, text = self.probe(node, extra=["--no-post"])
        self.assertEqual(code, 3, text)
        v = self.verdicts(summary)
        self.assertEqual(v["group"], "held")
        self.assertEqual(v["post"], "undecided")
        self.assertEqual(node.articles, {})

    def test_the_password_reaches_neither_the_record_nor_the_output(self):
        node = self.serve(password="s3cret-word")
        code, summary, text = self.probe(node, password="s3cret-word")
        self.assertEqual(code, 0, text)
        self.assertNotIn("s3cret-word", text)
        self.assertNotIn("s3cret-word", json.dumps(summary))

    def test_a_missing_credential_or_cafile_is_a_usage_error(self):
        with mock.patch.dict(os.environ, {"FN_PROBE_USER": "", "FN_PROBE_PASSWORD": ""}):
            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as stop:
                    node_probe.main(["127.0.0.1", "1", "--cafile", str(self.cert)])
        self.assertEqual(stop.exception.code, 2)
        with mock.patch.dict(os.environ, {"FN_PROBE_USER": "u", "FN_PROBE_PASSWORD": "p"}):
            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as stop:
                    node_probe.main(["127.0.0.1", "1", "--cafile", str(self.dir / "absent.pem")])
        self.assertEqual(stop.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
