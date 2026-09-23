"""The separate web client against an actual NNTP socket and HTTP requests."""
import http.client
from pathlib import Path
import shutil
import sys
import tempfile
import threading
import unittest
from types import SimpleNamespace
from urllib.parse import urlencode

from tests.fake_node import FakeNode, make_pair

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_web  # noqa: E402


@unittest.skipUnless(shutil.which("openssl"), "openssl is required for the socket fixture")
class WebClientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.cert, cls.key = make_pair(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def setUp(self):
        self.node = FakeNode(self.cert, self.key,
                             protected_only=False, require_auth=False)
        self.node.start()
        args = SimpleNamespace(host="127.0.0.1", port=self.node.port,
                               timeout=5.0, plain=True, cafile=None)
        self.server = fn_web.WebServer(0, fn_web.Backend(args, "", ""))
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(5)
        self.node.stop()

    def request(self, method, path, body=None, origin=True):
        connection = http.client.HTTPConnection("127.0.0.1", self.server.server_port,
                                                 timeout=10)
        headers = {}
        if method == "POST":
            headers["Content-Type"] = "application/x-www-form-urlencoded"
            if origin:
                headers["Origin"] = "http://127.0.0.1:%d" % self.server.server_port
            body = urlencode({"csrf": self.server.token, "group": "fn.agents",
                              "subject": "hello", "sender": "human <h@local.invalid>",
                              "references": "", "body": "A real post"} | (body or {}))
        connection.request(method, path, body=body, headers=headers)
        reply = connection.getresponse()
        data = reply.read().decode("utf-8")
        result = reply.status, dict(reply.getheaders()), data
        connection.close()
        return result

    def test_groups_recent_article_and_escaped_source(self):
        self.node.inject("fn.agents", ["From: <script>alert(1)</script>",
                                       "Newsgroups: fn.agents",
                                       "Subject: Hello <img src=https://bad.invalid/x>",
                                       "Message-ID: <one@fake.invalid>",
                                       "Path: peer!other", "Injection-Info: gateway",
                                       "FN-Statement: opaque-evidence", "",
                                       "<script>steal()</script>"])
        status, headers, page = self.request("GET", "/")
        self.assertEqual(status, 200)
        self.assertIn("fn.agents", page)
        self.assertIn("default-src 'none'", headers["Content-Security-Policy"])
        self.assertEqual(headers["Cache-Control"], "no-store")
        status, _, page = self.request("GET", "/g?name=fn.agents")
        self.assertEqual(status, 200)
        self.assertIn("Hello &lt;img src=https://bad.invalid/x&gt;", page)
        self.assertIn("/a?group=fn.agents&amp;number=1", page)
        status, _, page = self.request("GET", "/a?group=fn.agents&number=1")
        self.assertEqual(status, 200)
        self.assertIn("&lt;script&gt;steal()&lt;/script&gt;", page)
        self.assertNotIn("<script>steal()", page)
        self.assertIn("FN-Statement present; not verified here", page)
        self.assertIn("Path: peer!other", page)
        self.assertIn("Viewing does not acknowledge application processing", page)

    def test_composer_posts_via_nntp_and_keeps_three_outcomes(self):
        accepted = self.request("POST", "/post")
        self.assertEqual(accepted[0], 200)
        self.assertIn("accepted", accepted[2])
        self.assertEqual(len(self.node.articles), 1)
        stored = next(iter(self.node.articles.values()))
        self.assertIn("A real post", stored)
        self.assertNotIn("Path:", stored)

        self.node.refuse_post = True
        refused = self.request("POST", "/post")
        self.assertEqual(refused[0], 503)
        self.assertIn("<span class='badge refused'>refused</span>", refused[2])

        self.node.refuse_post = False
        self.node.uncertain_post = True
        uncertain = self.request("POST", "/post")
        self.assertEqual(uncertain[0], 503)
        self.assertIn("<span class='badge uncertain'>uncertain</span>", uncertain[2])
        self.assertIn("do not repost", uncertain[2])
        self.assertEqual(len(self.node.articles), 1)

    def test_form_origin_and_size_are_checked_before_nntp_post(self):
        denied = self.request("POST", "/post", origin=False)
        self.assertEqual(denied[0], 403)
        oversized = self.request("POST", "/post", body={"body": "x" * 25000})
        self.assertEqual(oversized[0], 400)
        self.assertEqual(self.node.articles, {})

    def test_post_connection_loss_keeps_settlement_identifier(self):
        self.node.drop_before_greeting = True
        status, _, page = self.request("POST", "/post")
        self.assertEqual(status, 503)
        self.assertIn("<span class='badge uncertain'>uncertain</span>", page)
        self.assertIn("Check this Message-ID", page)
        self.assertIn("&lt;fn-client.", page)


if __name__ == "__main__":
    unittest.main()
