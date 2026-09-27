"""The friends' web reader (WEB-003) against the fake node over real TLS and HTTP.

The fake says what the reader does with an answer, never that fn gives it;
the native run (tests/fn_reader_drive.mjs over a scratch node) is the
evidence about the node.
"""
import html
import http.client
import re
import shutil
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from types import SimpleNamespace
from urllib.parse import urlencode

from tests.fake_node import FakeNode, make_pair

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_reader  # noqa: E402

fn_reader.KEEP_CONNECTIONS = False   # the fake serves one connection at a time

PASSWORD = "right"


@unittest.skipUnless(shutil.which("openssl"), "openssl is required for the socket fixture")
class ReaderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.cert, cls.key = make_pair(Path(cls.temporary.name))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def start(self, **node):
        self.node = FakeNode(self.cert, self.key, groups=("fn.test",), **node)
        self.node.start()
        self.state = tempfile.TemporaryDirectory()
        args = SimpleNamespace(host="127.0.0.1", port=self.node.port, timeout=5.0,
                               plain_node=False, tls_cert=str(self.cert))
        self.server = fn_reader.Reader(("127.0.0.1", 0), fn_reader.Node(args),
                                       Path(self.state.name), site="Test news",
                                       mail_domain="example.invalid", secure=False)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.cookies = {}
        self.pages = []

    def tearDown(self):
        if hasattr(self, "server"):
            self.server.shutdown()
            self.server.server_close()
            self.thread.join(5)
            self.node.stop()
            self.state.cleanup()
            for page in self.pages:
                self.assertNotIn(PASSWORD + "-secret", page)

    def request(self, method, path, fields=None, headers=None):
        conn = http.client.HTTPConnection("127.0.0.1", self.server.server_address[1], timeout=10)
        sent = {"Host": "127.0.0.1:%d" % self.server.server_address[1]}
        if self.cookies:
            sent["Cookie"] = "; ".join("%s=%s" % kv for kv in self.cookies.items())
        body = None
        if fields is not None:
            body = urlencode(fields)
            sent["Content-Type"] = "application/x-www-form-urlencoded"
            sent["Origin"] = "http://" + sent["Host"]
        sent.update(headers or {})
        conn.request(method, path, body=body, headers=sent)
        response = conn.getresponse()
        text = response.read().decode("utf-8")
        for name, value in response.getheaders():
            if name.lower() == "set-cookie":
                key, _, rest = value.partition("=")
                content = rest.split(";")[0]
                if "Max-Age=0" in value:
                    self.cookies.pop(key, None)
                else:
                    self.cookies[key] = content
        conn.close()
        self.pages.append(text)
        return response.status, response.getheader("Location"), text

    def sign_in(self, password=PASSWORD, user="alice"):
        _, _, page = self.request("GET", "/signin")
        pre = re.search(r"name='pre' value='([^']+)'", page).group(1)
        return self.request("POST", "/signin", {"pre": pre, "next": "/", "user": user,
                                                "password": password})

    def csrf(self):
        _, _, page = self.request("GET", "/me")
        return re.search(r"name='csrf' value='([^']+)'", page).group(1)

    def compose(self, **query):
        status, _, page = self.request("GET", "/new?" + urlencode(dict(query, g="fn.test")))
        self.assertEqual(status, 200)
        return {name: html.unescape(value) for name, value in
                re.findall(r"<input type='hidden' name='([a-z]+)' value='([^']*)'>", page)}

    def post(self, subject="hello", body="first line\n.dot line\nünïcode ✓"):
        fields = self.compose()
        fields.update(subject=subject, body=body)
        return self.request("POST", "/post", fields), fields["sid"]

    # ------------------------------------------------------------ tests

    def test_sign_in_is_the_nodes_answer_and_the_password_stays_out(self):
        self.start(password=PASSWORD)
        status, where, _ = self.request("GET", "/")
        self.assertEqual((status, where), (303, "/signin"))
        status, _, page = self.sign_in("wrong-secret")
        self.assertEqual(status, 401)
        self.assertIn("don&#x27;t match", page)
        self.assertNotIn("fnr_session", self.cookies)
        self.assertNotIn("wrong-secret", page)
        self.assertIn("AUTHINFO PASS *", self.node.seen)
        self.assertLess(self.node.seen.index("STARTTLS"), self.node.seen.index("AUTHINFO PASS *"))
        status, where, _ = self.sign_in()
        self.assertEqual((status, where), (303, "/"))
        self.assertIn("fnr_session", self.cookies)
        status, _, page = self.request("GET", "/")
        self.assertEqual(status, 200)
        self.assertIn("fn.test", page)
        # signing out drops the session
        self.request("POST", "/signout", {"csrf": self.csrf()})
        self.assertEqual(self.request("GET", "/")[0], 303)

    def test_unreachable_node_is_not_a_wrong_password(self):
        self.start(password=PASSWORD)
        self.node.stop()
        status, _, page = self.sign_in()
        self.assertEqual(status, 503)
        self.assertIn("can&#x27;t reach", page)

    def test_a_post_from_another_site_or_without_the_token_does_nothing(self):
        self.start(password=PASSWORD)
        self.sign_in()
        fields = self.compose()
        fields.update(subject="x", body="y")
        status, _, _ = self.request("POST", "/post", fields,
                                    headers={"Sec-Fetch-Site": "cross-site"})
        self.assertEqual(status, 403)
        status, _, _ = self.request("POST", "/post", fields,
                                    headers={"Origin": "https://evil.example"})
        self.assertEqual(status, 403)
        fields["csrf"] = "forged"
        self.assertEqual(self.request("POST", "/post", fields)[1], "/signin")
        self.assertNotIn("POST", self.node.seen)

    def test_post_once_read_unread_and_remove_own(self):
        self.start(password=PASSWORD)
        self.node.seed("fn.test", "welcome", "hi there")
        self.sign_in()
        _, _, page = self.request("GET", "/")
        self.assertIn("1 new", page)
        (status, where, _), sid = self.post()
        self.assertEqual(status, 303)
        _, _, page = self.request("GET", where)
        self.assertIn("Posted!", page)
        posted = [m for m in self.node.articles if m.startswith("<fn-reader.")]
        self.assertEqual(len(posted), 1)
        lines = self.node.articles[posted[0]]
        self.assertIn("Content-Type: text/plain; charset=utf-8", lines)
        self.assertIn(".dot line", lines)
        self.assertTrue(all(line.isascii() for line in lines[:lines.index("")]))
        # the same form again never posts again
        fields = {"csrf": self.csrf(), "sid": sid, "g": "fn.test", "subject": "hello",
                  "body": "again", "refs": "", "re": ""}
        self.request("POST", "/post", fields)
        self.assertEqual(self.node.seen.count("POST"), 1)
        # reading marks read
        _, _, page = self.request("GET", "/g?name=fn.test")
        self.assertEqual(page.count("1 new"), 1)      # your own post is not news to you
        _, _, page = self.request("GET", "/t?g=fn.test&n=2")
        self.assertIn("ünïcode ✓", page)
        self.assertIn("Remove my post", page)
        _, _, page = self.request("GET", "/t?g=fn.test&n=1")
        self.assertNotIn("Remove my post", page)
        _, _, page = self.request("GET", "/")
        self.assertIn("all read", page)
        # replying carries References
        fields = self.compose(re="1")
        self.assertEqual(fields["refs"], "<seed-1@fake.invalid>")
        # removing sends the cancel control article for the recorded post
        _, _, page = self.request("GET", "/remove?" + urlencode(
            {"id": posted[0], "g": "fn.test", "n": 2}))
        remove_sid = re.search(r"name='sid' value='([0-9a-f]+)'", page).group(1)
        status, where, _ = self.request("POST", "/remove", {
            "csrf": self.csrf(), "id": posted[0], "g": "fn.test", "sid": remove_sid})
        cancels = [lines for m, lines in self.node.articles.items()
                   if "Control: cancel " + posted[0] in lines]
        self.assertEqual(len(cancels), 1)
        _, _, page = self.request("GET", where)
        # the fake does not withdraw: the reader reports what the node still serves
        self.assertIn("still shows the post", page)
        # a post that is not one of ours has no remove page
        status, _, _ = self.request("GET", "/remove?" + urlencode(
            {"id": "<seed-1@fake.invalid>", "g": "fn.test"}))
        self.assertEqual(status, 404)

    def test_refused_shows_the_nodes_reason_and_offers_an_edit(self):
        self.start(password=PASSWORD, refuse_post=True,
                   refusal="441 posting failed; From is not a valid mailbox list")
        self.sign_in()
        (_, where, _), _ = self.post()
        _, _, page = self.request("GET", where)
        self.assertIn("Not posted", page)
        self.assertIn("441 posting failed; From is not a valid mailbox list", page)
        self.assertIn("Edit and try again", page)
        self.assertNotIn("Check now", page)

    def test_not_sure_is_settled_by_the_same_article_never_a_new_one(self):
        self.start(password=PASSWORD, commit_then_drop=True, d25=True)
        self.sign_in()
        (_, where, _), sid = self.post()
        _, _, page = self.request("GET", where)
        self.assertIn("Not sure yet", page)
        self.assertNotIn("Edit and try again", page)
        self.request("POST", "/check", {"csrf": self.csrf(), "id": sid})
        _, _, page = self.request("GET", where)
        self.assertIn("We checked, and it did go through.", page)
        posted = [m for m in self.node.articles if m.startswith("<fn-reader.")]
        self.assertEqual(len(posted), 1)

    def test_state_is_per_login(self):
        self.start(password=PASSWORD)
        self.node.seed("fn.test", "welcome", "hi there")
        self.sign_in(user="alice")
        self.request("GET", "/t?g=fn.test&n=1")
        self.cookies = {}
        self.sign_in(user="bob")
        _, _, page = self.request("GET", "/")
        self.assertIn("1 new", page)

    def test_plain_http_off_loopback_is_refused(self):
        with self.assertRaises(SystemExit):
            fn_reader.main(["--node", "127.0.0.1:1", "--tls-cert", str(self.cert),
                            "--state", tempfile.mkdtemp(), "--listen", "0.0.0.0:0"])


class TextTests(unittest.TestCase):
    def test_headers_are_ascii_on_the_wire(self):
        lines = fn_reader.header_value("Subject", "Grüße aus Köln — ein sehr langer Betreff "
                                       "der gefaltet werden muss, weil er so lang ist")
        self.assertTrue(all(line.isascii() for line in lines))
        self.assertTrue(all(line.startswith(" ") for line in lines[1:]))
        self.assertEqual(fn_reader.decoded(" ".join(lines)[len("Subject: "):]),
                         "Grüße aus Köln — ein sehr langer Betreff der gefaltet werden "
                         "muss, weil er so lang ist")

    def test_long_lines_go_quoted_printable(self):
        extra, body = fn_reader.body_lines("x" * 2000)
        self.assertIn("Content-Transfer-Encoding: quoted-printable", extra)
        self.assertTrue(all(len(line) <= 76 for line in body))

    def test_body_escapes_and_links(self):
        out = fn_reader.rendered_body("<b>hi</b> see https://example.org/a?b=1&c=2.\n> quoted")
        self.assertIn("&lt;b&gt;", out)
        self.assertIn("href='https://example.org/a?b=1&amp;c=2'", out)
        self.assertIn("<span class='q'>&gt; quoted</span>", out)

    def test_read_ranges(self):
        ranges = fn_reader.add_range([[1, 3]], 5, 7)
        ranges = fn_reader.add_range(ranges, 4, 4)
        self.assertEqual(ranges, [[1, 7]])
        self.assertEqual(fn_reader.read_within(ranges, 3, 10), 5)


if __name__ == "__main__":
    unittest.main()
