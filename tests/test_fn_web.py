"""The separate web client against an actual NNTP socket and HTTP requests."""
from concurrent.futures import ThreadPoolExecutor
import http.client
from pathlib import Path
import re
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
            submission_id = (body or {}).get("submission_id") or self.form_id()
            body = urlencode({"csrf": self.server.token, "submission_id": submission_id,
                              "group": "fn.agents",
                              "subject": "hello", "sender": "human <h@local.invalid>",
                              "references": "", "body": "A real post"} | (body or {}))
        connection.request(method, path, body=body, headers=headers)
        reply = connection.getresponse()
        data = reply.read().decode("utf-8")
        result = reply.status, dict(reply.getheaders()), data
        connection.close()
        return result

    def form_id(self):
        status, _, page = self.request("GET", "/compose?group=fn.agents")
        self.assertEqual(status, 200)
        return re.search(r"name='submission_id' value='([^']+)'", page).group(1)

    def post(self, body=None, origin=True):
        status, headers, page = self.request("POST", "/post", body, origin)
        if status == 303:
            return self.request("GET", headers["Location"])
        return status, headers, page

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
        self.assertEqual(headers["Referrer-Policy"], "same-origin")
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
        accepted = self.post()
        self.assertEqual(accepted[0], 200)
        self.assertIn("accepted", accepted[2])
        self.assertEqual(len(self.node.articles), 1)
        stored = next(iter(self.node.articles.values()))
        self.assertIn("A real post", stored)
        self.assertNotIn("Path:", stored)

        self.node.refuse_post = True
        refused = self.post()
        self.assertEqual(refused[0], 200)
        self.assertIn("<span class='badge refused'>refused</span>", refused[2])

        self.node.refuse_post = False
        self.node.uncertain_post = True
        uncertain = self.post()
        self.assertEqual(uncertain[0], 200)
        self.assertIn("<span class='badge uncertain'>uncertain</span>", uncertain[2])
        self.assertIn("do not repost", uncertain[2])
        self.assertEqual(len(self.node.articles), 1)

    def test_form_origin_and_size_are_checked_before_nntp_post(self):
        denied = self.post(origin=False)
        self.assertEqual(denied[0], 403)
        oversized = self.post(body={"body": "x" * 25000})
        self.assertEqual(oversized[0], 400)
        wrong_group = self.post(body={"group": "fn.humans"})
        self.assertEqual(wrong_group[0], 400)
        self.assertEqual(self.node.articles, {})

    def test_post_connection_loss_keeps_settlement_identifier(self):
        self.node.drop_before_greeting = True
        status, _, page = self.post()
        self.assertEqual(status, 200)
        self.assertIn("<span class='badge uncertain'>uncertain</span>", page)
        self.assertIn("Check whether the node serves this Message-ID", page)
        self.assertIn("&lt;fn-client.", page)

    def test_double_submit_and_refresh_keep_one_exact_article(self):
        token = self.form_id()
        def send(body):
            return self.request("POST", "/post", {
                "submission_id": token, "body": body})
        with ThreadPoolExecutor(max_workers=2) as pool:
            first, second = list(pool.map(send, ("first source", "other source")))
        self.assertEqual(first[0], 303)
        self.assertEqual(second[0], 303)
        self.assertEqual(first[1]["Location"], second[1]["Location"])
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(len(self.node.articles), 1)
        page1 = self.request("GET", first[1]["Location"])[2]
        page2 = self.request("GET", first[1]["Location"])[2]
        self.assertEqual(page1, page2)
        old = next(iter(self.node.articles.values()))
        self.assertIn("first source" if "first source" in old else "other source", old)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": token, "body": "third source"})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(next(iter(self.node.articles.values())), old)

    def test_uncertain_settlement_is_read_only_and_unknown_token_never_posts(self):
        token = self.form_id()
        self.node.uncertain_post = True
        status, headers, _ = self.request("POST", "/post", {
            "submission_id": token})
        self.assertEqual(status, 303)
        result = self.request("GET", headers["Location"])[2]
        self.assertIn("badge uncertain", result)
        self.assertIn("Message-ID:", result)
        status, _, settled = self.request("GET", "/settle?id=" + token)
        self.assertEqual(status, 200)
        self.assertIn("did not serve this Message-ID in this lookup", settled)
        self.assertIn("original POST outcome has not changed", settled)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": token})[0], 303)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": "forgotten"})[0], 410)
        self.assertEqual(self.node.seen.count("POST"), 1)
        self.server.submissions = fn_web.SubmissionBook(self.server.backend)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": token})[0], 410)
        self.assertEqual(self.node.seen.count("POST"), 1)

    def test_bounded_form_memory_evicts_without_reposting(self):
        first = self.form_id()
        for _ in range(fn_web.MAX_SUBMISSIONS):
            self.server.submissions.new("fn.agents")
        self.assertEqual(len(self.server.submissions.entries), fn_web.MAX_SUBMISSIONS)
        self.assertEqual(self.request("POST", "/post", {
            "submission_id": first})[0], 410)
        self.assertNotIn("POST", self.node.seen)


if __name__ == "__main__":
    unittest.main()
