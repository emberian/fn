"""The node's own web face (WEB-005, PRF-337..340, SCN-187), on a scratch
native writable owner.

`operator CONFIG run' with a `[web]' table binds the face beside the NNTP
listener (LISTENING-WEB); this module drives it over HTTP as a browser does
(tests/web_face_drive.mjs drives a real Chromium through the same flow on
hbox).  Every answer is the node's: the invitation code is redeemed by the
node's XREDEEM, the password checked by its AUTHINFO, the post taken and
withdrawn by its served POST path, and the pages are rendered by ACL2 from
the replies the session's own connection got.  There is no Python between
the browser and the node.

Set FN_NATIVE_DEVELOPER_HOST to a developer image and FN_NATIVE_TEST_ROOT to
its source snapshot.  The test creates and removes only its own Store.
"""
import html
import http.client
import os
from pathlib import Path
import re
import socket
import ssl
import subprocess
import tempfile
import time
import unittest
from urllib.parse import urlencode

from tests.native_harness import wait_for_announcement, stop_and_diagnostics

IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", "/nonexistent/fn-host-developer"))
ROOT = Path(os.environ.get("FN_NATIVE_TEST_ROOT", Path(__file__).resolve().parents[1]))
PASSWORD = "wren-secret-9"


def native_environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    env.pop("FN_NATIVE_POST_FAULT", None)
    return env


def free_loopback_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class Browser:
    """Cookies and requests, as a browser keeps and sends them."""

    def __init__(self, port, tls=False):
        self.port, self.tls, self.cookies, self.pages = port, tls, {}, []

    def request(self, method, path, fields=None, origin=True, raw=None):
        host = "127.0.0.1:%d" % self.port
        headers = {"Host": host}
        if self.cookies:
            headers["Cookie"] = "; ".join("%s=%s" % kv for kv in self.cookies.items())
        body = raw
        if fields is not None:
            body = urlencode(fields)
            headers["Content-Type"] = "application/x-www-form-urlencoded"
            if origin:
                headers["Origin"] = ("https://" if self.tls else "http://") + host
        if self.tls:
            context = ssl.create_default_context()
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            conn = http.client.HTTPSConnection("127.0.0.1", self.port, timeout=120,
                                               context=context)
        else:
            conn = http.client.HTTPConnection("127.0.0.1", self.port, timeout=120)
        conn.request(method, path, body=body, headers=headers)
        reply = conn.getresponse()
        page = reply.read().decode("utf-8")
        answer = (reply.status, reply.getheader("Location"), page, dict(reply.getheaders()),
                  reply.msg.get_all("Set-Cookie") or [])
        for value in answer[4]:
            key, _, rest = value.partition("=")
            if "Max-Age=0" in value:
                self.cookies.pop(key, None)
            else:
                self.cookies[key] = rest.split(";")[0]
        conn.close()
        self.pages.append(page)
        return answer

    def form_value(self, page, name):
        # As a browser reads an attribute: its character references decoded.
        return html.unescape(re.search(r"name='%s' value='([^']*)'" % name, page).group(1))


class FaceCases:
    """A friend's first visit to the node's own web face: make the account
    with an invitation code, read, post, see the post, remove it; the checks
    fn_reader's rehearsal made (planning/evidence/release-web-reader-2026-09-27.md)."""

    TLS = False

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fn-web-face-")
        root = cls.root = Path(cls.temporary.name)
        cls.store, cls.config = root / "store", root / "fn.toml"
        cls.port, cls.tls_port, cls.web_port = (free_loopback_port(), free_loopback_port(),
                                                free_loopback_port())
        env = native_environment()
        cert, key = root / "cert.pem", root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                        "-out", str(cert), "-sha256", "-days", "1", "-nodes",
                        "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=60,
                       check=True)
        cls.config.write_text(
            '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n\n[control]\npath = "{}"\n\n'
            '[auth]\nrequired = true\nprotected_only = true\n\n'
            '[web]\nport = {}\nsite = "Friends news"\ndomain = "friends.invalid"\n{}'.format(
                cls.store, cls.port, cls.tls_port, cert, key, root / "control.sock",
                cls.web_port, "tls = true\n" if cls.TLS else ""),
            encoding="ascii")
        done = subprocess.run([str(IMAGE), "--fn", "operator", str(cls.config), "init",
                               "local.general", "control.cancel"], cwd=ROOT, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=240,
                              check=False)
        assert done.returncode == 0, done.stderr.decode(errors="replace")
        cls.owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(cls.config), "run"],
                                     cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE)
        try:
            wait_for_announcement(cls.owner, b"LISTENING-WEB ")
        except AssertionError as error:
            raise AssertionError(str(error) + ": " + stop_and_diagnostics(cls.owner))

    @classmethod
    def tearDownClass(cls):
        stop_and_diagnostics(cls.owner, timeout=30)
        cls.owner.stdout.close()
        cls.owner.stderr.close()
        cls.temporary.cleanup()

    def invite(self):
        result = subprocess.run([str(IMAGE), "--fn", "operator", str(self.config), "account",
                                 "invite", "--expires", "3600"], cwd=ROOT,
                                env=native_environment(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=240, check=False)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, result.stdout)
        return codes[0].decode("ascii")

    def browser(self):
        return Browser(self.web_port, self.TLS)

    def make_account(self, b, user):
        _, _, page, _, _ = b.request("GET", "/redeem")
        return b.request("POST", "/redeem", {
            "pre": b.form_value(page, "pre"), "code": self.invite(), "user": user,
            "password": PASSWORD, "again": PASSWORD})

    def test_1_a_friend_makes_an_account_reads_posts_and_removes(self):
        b = self.browser()
        status, where, page, headers, _ = b.request("GET", "/")
        self.assertEqual((status, where), (303, "/signin"))
        self.assertIn("default-src 'none'", headers["Content-Security-Policy"])
        status, _, page, headers, cookies = b.request("GET", "/signin")
        self.assertEqual(status, 200)
        self.assertIn("Make your account", page)
        self.assertIn("text/html; charset=utf-8", headers["Content-Type"])
        # The invitation: the node's XREDEEM, then AUTHINFO on a new connection.
        status, where, page, _, cookies = self.make_account(b, "wren")
        self.assertEqual((status, where), (303, "/"), page)
        session = [c for c in cookies if c.startswith("fnr_session=")]
        self.assertEqual(len(session), 1)
        self.assertIn("HttpOnly", session[0])
        self.assertIn("SameSite=Lax", session[0])
        if self.TLS:
            self.assertIn("Secure", session[0])
        status, _, page, _, _ = b.request("GET", "/")
        self.assertEqual(status, 200)
        self.assertIn("local.general", page)
        self.assertIn("<span>wren</span>", page)
        csrf = b.form_value(page, "csrf")
        # Post, through the node's served POST path.
        status, _, page, _, _ = b.request("POST", "/post", {
            "csrf": csrf, "g": "local.general", "subject": "Hello from wren",
            "body": "My first post, from the browser. Grüße ✓\r\n.\r\n<b>not bold</b>"})
        self.assertEqual(status, 200, page)
        self.assertIn("Posted!", page)
        status, _, page, _, _ = b.request("GET", "/g?name=local.general")
        self.assertEqual(status, 200)
        self.assertIn("Hello from wren", page)
        number = re.search(r"href='/a\?g=local.general&amp;n=(\d+)'>Hello from wren", page).group(1)
        status, _, page, _, _ = b.request("GET", "/a?g=local.general&n=" + number)
        self.assertEqual(status, 200)
        self.assertIn("My first post, from the browser. Grüße ✓", page)
        self.assertIn("&lt;b&gt;not bold&lt;/b&gt;", page)      # escaped, never markup
        self.assertIn("Remove my post", page)
        remove = re.search(r"href='(/remove\?[^']+)'>Remove my post", page).group(1)
        status, _, page, _, _ = b.request("GET", remove.replace("&amp;", "&"))
        self.assertEqual(status, 200)
        status, _, page, _, _ = b.request("POST", "/remove", {
            "csrf": csrf, "id": b.form_value(page, "id"), "g": "local.general"})
        self.assertEqual(status, 200, page)
        self.assertIn("Your post has been removed", page)
        status, _, page, _, _ = b.request("GET", "/g?name=local.general")
        self.assertNotIn("Hello from wren", page)
        # Sign out; a wrong password is the node's 481, in plain words.
        status, where, _, _, _ = b.request("POST", "/signout", {"csrf": csrf})
        self.assertEqual((status, where), (303, "/signin"))
        self.assertNotIn("fnr_session", b.cookies)
        _, _, page, _, _ = b.request("GET", "/signin")
        status, _, page, _, _ = b.request("POST", "/signin", {
            "pre": b.form_value(page, "pre"), "next": "/", "user": "wren",
            "password": "not-the-password"})
        self.assertEqual(status, 401)
        self.assertIn("don&#39;t match", page)
        status, where, _, _, _ = b.request("POST", "/signin", {
            "pre": b.form_value(page, "pre"), "next": "/", "user": "wren",
            "password": PASSWORD})
        self.assertEqual((status, where), (303, "/"))
        status, _, page, _, _ = b.request("GET", "/")
        self.assertIn("local.general", page)
        # No page carried the password.
        self.assertFalse(any(PASSWORD in p for p in b.pages))

    def test_2_refusals(self):
        b = self.browser()
        # A route that needs a session: sent to sign in, the page kept.
        status, where, _, _, _ = b.request("GET", "/g?name=local.general")
        self.assertEqual((status, where), (303, "/signin?next=%2Fg%3Fname%3Dlocal.general"))
        # A sign-in form without its sign-in token (fnr_pre): 400, re-shown, nothing opened.
        status, _, _, _, _ = b.request("POST", "/signin", {"user": "x"}, origin=False)
        self.assertEqual(status, 400)            # no sign-in token: the form is re-shown
        # Malformed requests: the parser's refusals.
        for raw, code in ((b"GET / HTTP/2.0\r\nHost: a\r\n\r\n", 505),
                          (b"DELETE / HTTP/1.1\r\nHost: a\r\n\r\n", 501),
                          (b"GET / HTTP/1.1\r\n\r\n", 400),
                          (b"POST /post HTTP/1.1\r\nHost: a\r\n\r\n", 411)):
            with socket.create_connection(("127.0.0.1", self.web_port), timeout=30) as s:
                if self.TLS:
                    context = ssl.create_default_context()
                    context.check_hostname = False
                    context.verify_mode = ssl.CERT_NONE
                    s = context.wrap_socket(s)
                s.sendall(raw)
                answer = b""
                while b"\r\n" not in answer:
                    chunk = s.recv(4096)
                    if not chunk:
                        break
                    answer += chunk
            self.assertTrue(answer.startswith(b"HTTP/1.1 %d " % code), (raw, answer[:80]))
        # The style sheet: constant octets, no script anywhere.
        status, _, css, headers, _ = b.request("GET", "/style.css")
        self.assertEqual(status, 200)
        self.assertIn("text/css", headers["Content-Type"])
        self.assertIn("--bar-bg", css)

    def test_3_the_code_works_once(self):
        b = self.browser()
        code = self.invite()
        _, _, page, _, _ = b.request("GET", "/redeem")
        status, _, _, _, _ = b.request("POST", "/redeem", {
            "pre": b.form_value(page, "pre"), "code": code, "user": "robin",
            "password": PASSWORD, "again": PASSWORD})
        self.assertEqual(status, 303)
        c = self.browser()
        _, _, page, _, _ = c.request("GET", "/redeem")
        status, _, page, _, _ = c.request("POST", "/redeem", {
            "pre": c.form_value(page, "pre"), "code": code, "user": "robin2",
            "password": PASSWORD, "again": PASSWORD})
        self.assertEqual(status, 403, page)
        self.assertIn("didn&#39;t work", page)


    def fuzz_requests_are_answered_or_closed(self):
        """A bounded grammar fuzz over the request parser (tests/fuzz_nntp.py's
        approach, for HTTP): every mutated request is answered with a status
        line or closed, and the face keeps serving.  Plain HTTP (the parser is
        the same behind TLS; a half-closed TLS stream is not a client's)."""
        import random
        rng = random.Random(20260928)
        methods = [b"GET", b"POST", b"HEAD", b"PUT", b"G ET", b"", b"get", b"POST\x00"]
        targets = [b"/", b"/g?name=local.general", b"http://a/signin", b"*", b"//x",
                   b"/\xff", b"/" + b"a" * 5000, b"/a?g=%zz&n=-1", b""]
        versions = [b"HTTP/1.1", b"HTTP/1.0", b"HTTP/9.9", b"HTTP/1", b"http/1.1", b""]
        fields = [b"Host: a", b"Host: a\r\nHost: b", b"Content-Length: 5",
                  b"Content-Length: 99999999999999999999", b"Content-Length: 3\r\nContent-Length: 4",
                  b"Transfer-Encoding: chunked", b" folded", b"Cookie: fnr_session=" + b"A" * 43,
                  b"X-Forwarded-For: 1.2.3.4", b"Bad Header: x", b"Origin: http://evil",
                  b"Cookie: ;;;==;", b"Host:" + b"x" * 20000]
        for _ in range(120):
            head = (rng.choice(methods) + b" " + rng.choice(targets) + b" " +
                    rng.choice(versions) + b"\r\n")
            for _ in range(rng.randrange(0, 4)):
                head += rng.choice(fields) + b"\r\n"
            raw = head + b"\r\n" + (b"a=b&" * rng.randrange(0, 3))
            if rng.random() < 0.2:
                raw = raw[:rng.randrange(0, len(raw) + 1)]
            if rng.random() < 0.1:
                raw = raw.replace(b"\r\n", b"\n")
            with socket.create_connection(("127.0.0.1", self.web_port), timeout=60) as s:
                try:
                    s.sendall(raw)
                    s.shutdown(socket.SHUT_WR)
                    answer = b""
                    while True:
                        chunk = s.recv(65536)
                        if not chunk:
                            break
                        answer += chunk
                except (ConnectionError, ssl.SSLError):
                    answer = b""
            self.assertTrue(answer == b"" or re.match(rb"HTTP/1\.1 [1-5]\d\d ", answer),
                            (raw[:120], answer[:120]))
        status, _, _, _, _ = self.browser().request("GET", "/signin")
        self.assertEqual(status, 200)


@unittest.skipUnless(os.access(IMAGE, os.X_OK), "native developer image required")
class NativeWebFaceTests(FaceCases, unittest.TestCase):
    """Plain HTTP from loopback (the way a TLS proxy on the machine reaches it)."""
    TLS = False

    def test_4_fuzzed_requests_are_answered_or_closed(self):
        self.fuzz_requests_are_answered_or_closed()


@unittest.skipUnless(os.access(IMAGE, os.X_OK), "native developer image required")
class NativeWebFaceTlsTests(FaceCases, unittest.TestCase):
    """The same visit with the face serving HTTPS itself ([web] tls = true,
    [listener]'s certificate): the session cookie is Secure."""
    TLS = True


if __name__ == "__main__":
    unittest.main()
