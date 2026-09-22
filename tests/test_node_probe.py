"""tools/node_probe.py against a fake node that speaks just enough NNTP.

The fake wraps its socket in real TLS with a certificate made here, so the
probe's handshake, its 483-before-TLS assertion, its login and its fresh-
connection reread are exercised end to end over loopback.  Each test names
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
import ssl
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import node_probe  # noqa: E402


class FakeNode(threading.Thread):
    """Serves one connection after another until stopped."""

    def __init__(self, cert, key, protected_only=True, password="right", accept_post=True,
                 offer_starttls=True):
        super().__init__(daemon=True)
        self.context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.context.load_cert_chain(cert, key)
        self.protected_only = protected_only
        self.password = password
        self.accept_post = accept_post
        self.offer_starttls = offer_starttls
        self.articles = {}
        self.listener = socket.socket()
        self.listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(4)
        self.port = self.listener.getsockname()[1]
        self.stopping = False
        self.seen = []

    def stop(self):
        self.stopping = True
        self.listener.close()

    def run(self):
        while not self.stopping:
            try:
                conn, _ = self.listener.accept()
            except OSError:
                return
            try:
                self.serve(conn)
            except (OSError, ssl.SSLError):
                pass
            finally:
                try:
                    conn.close()
                except OSError:
                    pass

    def serve(self, conn):
        conn.settimeout(10)
        buf = b""
        tls = False
        authenticated = False

        def line():
            nonlocal buf
            while b"\r\n" not in buf:
                chunk = conn.recv(4096)
                if not chunk:
                    raise OSError("client went away")
                buf += chunk
            out, buf = buf.split(b"\r\n", 1)
            return out.decode()

        def send(text):
            conn.sendall(text.encode() + b"\r\n")

        send("200 fake node ready")
        try:
            while True:
                cmd = line()
                self.seen.append(cmd if not cmd.startswith("AUTHINFO PASS") else "AUTHINFO PASS *")
                words = cmd.split()
                verb = words[0].upper() if words else ""
                if verb == "CAPABILITIES":
                    caps = ["VERSION 2", "READER", "POST"]
                    if self.offer_starttls and not tls:
                        caps.append("STARTTLS")
                    if not authenticated and (tls or not self.protected_only):
                        caps.append("AUTHINFO USER")
                    send("101 capabilities")
                    for cap in caps:
                        send(cap)
                    send(".")
                elif verb == "STARTTLS":
                    if tls or not self.offer_starttls:
                        send("502 already or never")
                        continue
                    send("382 continue with TLS negotiation")
                    assert buf == b"", "the fake never takes pipelined octets"
                    conn = self.context.wrap_socket(conn, server_side=True)
                    tls = True
                elif verb == "AUTHINFO":
                    if self.protected_only and not tls:
                        send("483 a protected channel is required; use STARTTLS")
                    elif words[1].upper() == "USER":
                        send("381 password required")
                    elif words[1].upper() == "PASS":
                        if " ".join(words[2:]) == self.password:
                            authenticated = True
                            send("281 authentication accepted")
                        else:
                            send("481 authentication failed")
                    else:
                        send("501 syntax")
                elif verb == "GROUP":
                    if not authenticated:
                        send("480 authentication required")
                        continue
                    send("211 %d 1 %d %s" % (len(self.articles), max(len(self.articles), 1), words[1]))
                elif verb == "POST":
                    if not authenticated or not self.accept_post:
                        send("440 posting not permitted")
                        continue
                    send("340 send article")
                    lines = []
                    while True:
                        one = line()
                        if one == ".":
                            break
                        lines.append(one[1:] if one.startswith("..") else one)
                    msgid = [l.split(":", 1)[1].strip() for l in lines
                             if l.lower().startswith("message-id:")]
                    self.articles[msgid[0]] = lines
                    send("240 article received")
                elif verb == "ARTICLE":
                    lines = self.articles.get(words[1])
                    if lines is None:
                        send("430 no such article")
                        continue
                    send("220 0 %s" % words[1])
                    for one in lines:
                        send(("." + one) if one.startswith(".") else one)
                    send(".")
                elif verb == "QUIT":
                    send("205 bye")
                    return
                else:
                    send("500 unknown")
        finally:
            conn.close()


def make_pair(directory):
    cert, key = directory / "cert.pem", directory / "key.pem"
    subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-sha256",
                    "-days", "2", "-subj", "/CN=localhost",
                    "-addext", "subjectAltName=IP:127.0.0.1,DNS:localhost",
                    "-keyout", str(key), "-out", str(cert)],
                   check=True, capture_output=True)
    return cert, key


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
