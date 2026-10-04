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

FN_NATIVE_DEVELOPER_HOST names the developer image (default
build/fn-host-developer).  The test creates and removes only its own Store.
"""
import errno
import html
import http.client
import re
import socket
import ssl
import time
import unittest
from urllib.parse import urlencode

from tests.native_harness import EXIT, Client, Node, class_case, client_context, free_port, keep_diagnostics, native_image, requires

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
PASSWORD = "wren-secret-9"


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
        node = cls.node = Node(class_case(cls), IMAGE, name="web-face")
        node.use_tls(alt_name=True, protected_only=False)
        cls.port, cls.tls_port, cls.web_port = node.port, node.tls_port, free_port()
        node.write_config(extra=(
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n\n'
            '[auth]\nrequired = true\nprotected_only = true\n\n'
            '[web]\nport = {}\nsite = "Friends news"\ndomain = "friends.invalid"\n{}'.format(
                node.tls_port, node.cert, node.root / "key.pem", cls.web_port,
                "tls = true\n" if cls.TLS else "")))
        cls.config = node.config
        node.init("local.general", "control.cancel", timeout=240)
        # Three listeners announce: NNTP, NNTP over TLS, and the web face.
        node.listening = 3
        node.start()

    def setUp(self):
        # Every case keeps the class owner's stderr when the runner names
        # FN_NATIVE_TEST_DIAGNOSTIC_DIR: a disconnect is classified from the
        # node's own trace, not from the client's RemoteDisconnected.
        keep_diagnostics(self, [self.node])

    def invite(self):
        result = self.node.operator("account", "invite", "--expires", "3600", timeout=240,
                                    expect=EXIT.OK)
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

    def test_health_is_bounded_readiness_in_the_running_owner_without_login(self):
        # Q10d: the same saved owner answers each request; no account/session
        # or operator image is launched for this network endpoint.
        process = self.node.process
        pid = process.pid
        b = self.browser()
        for _ in range(3):
            status, where, body, headers, cookies = b.request("GET", "/health")
            self.assertEqual((status, where, body), (200, None, "ready\n"))
            self.assertEqual(headers["Content-Type"], "text/plain; charset=utf-8")
            self.assertEqual(headers["Cache-Control"], "no-store")
            self.assertLessEqual(len(body.encode("utf-8")), 23)
            self.assertEqual(cookies, [])
            self.assertEqual(b.cookies, {})
            self.assertIsNone(process.poll())
            self.assertEqual(self.node.process.pid, pid)
        status, where, body, headers, cookies = b.request("HEAD", "/health")
        self.assertEqual((status, where, body, cookies), (200, None, "", []))
        self.assertEqual(headers["Content-Length"], "6")
        status, _, _, headers, _ = b.request("POST", "/health", {})
        self.assertEqual(status, 405)
        self.assertEqual(headers["Allow"], "GET, HEAD")

    def test_stalled_socket_does_not_block_health_reader_or_account_post(self):
        # The old inline accept worker waits its complete request/handshake
        # deadline before it can serve any of these healthy connections.
        slow = socket.create_connection(("127.0.0.1", self.web_port), timeout=10)
        try:
            if not self.TLS:
                slow.sendall(b"GET /heal")
            time.sleep(0.1)
            started = time.monotonic()
            b = self.browser()
            # The sign-in page first: it is the route every face since the
            # inline one serves, so the first measurement isolates the wait
            # behind the stalled socket from any later route's defect.
            status, _, page, _, _ = b.request("GET", "/signin")
            self.assertEqual(status, 200)
            self.assertIn("Make your account", page)
            self.assertLess(time.monotonic() - started, 4,
                            "stalled socket held the HTTP actor before the first page")
            status, _, body, _, _ = b.request("GET", "/health")
            self.assertEqual((status, body), (200, "ready\n"))
            status, where, page, _, _ = self.make_account(
                b, "parallel_tls" if self.TLS else "parallel_plain")
            self.assertEqual((status, where), (303, "/"), page)
            self.assertLess(time.monotonic() - started, 8,
                            "stalled socket held the HTTP actor")
            self.assertIsNone(self.node.process.poll())
        finally:
            slow.close()

    def raw_connection(self, timeout):
        s = socket.create_connection(("127.0.0.1", self.web_port), timeout=timeout)
        if self.TLS:
            context = ssl.create_default_context()
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            s = context.wrap_socket(s)
        return s

    @staticmethod
    def read_answer(s):
        answer = b""
        while True:
            chunk = s.recv(65536)
            if not chunk:
                return answer
            answer += chunk

    def test_two_requests_in_flight_are_answered_out_of_arrival_order(self):
        # A's head arrives in two parts; B arrives whole between them and is
        # answered before A's head is complete.  One connection at a time
        # cannot do this: B would wait out A's request deadline.
        host = b"Host: 127.0.0.1:%d\r\n" % self.web_port
        a = self.raw_connection(30)
        try:
            a.sendall(b"GET /sign")
            time.sleep(0.1)
            started = time.monotonic()
            with self.raw_connection(6) as b:
                b.sendall(b"GET /health HTTP/1.1\r\n" + host + b"\r\n")
                answer = self.read_answer(b)
            self.assertTrue(answer.startswith(b"HTTP/1.1 200 "), answer[:120])
            self.assertTrue(answer.endswith(b"\r\n\r\nready\n"), answer[-120:])
            self.assertLess(time.monotonic() - started, 4, "B waited behind A")
            a.sendall(b"in HTTP/1.1\r\n" + host + b"\r\n")
            answer = self.read_answer(a)
            self.assertTrue(answer.startswith(b"HTTP/1.1 200 "), answer[:120])
            self.assertIn(b"Make your account", answer)
            self.assertIsNone(self.node.process.poll())
        finally:
            a.close()

    def test_compressed_article_uses_physical_windows_through_web_and_restart(self):
        # This selector requires the current physical decoded producer. The
        # ordinary compression report proves the stored form independently.
        user = "decode_tls" if self.TLS else "decode_plain"
        b = self.browser()
        status, where, page, _, _ = self.make_account(b, user)
        self.assertEqual((status, where), (303, "/"), page)
        self.node.operator("policy", "set", "compress-min-octets", "64", expect=EXIT.OK)
        _, _, page, _, _ = b.request("GET", "/")
        line = "decoded window <&> exact retained body " + "abcdefghijklmno" * 4
        body = "\r\n".join([line] * 256)
        status, _, page, _, _ = b.request("POST", "/post", {
            "csrf": b.form_value(page, "csrf"), "g": "local.general",
            "subject": "Physical decoded response", "body": body})
        self.assertEqual(status, 200, page)
        self.assertIn("Posted!", page)
        status, _, page, _, _ = b.request("GET", "/g?name=local.general")
        self.assertEqual(status, 200, page)
        number = re.search(r"href='/a\?g=local.general&amp;n=(\d+)'>Physical decoded response", page).group(1)

        def article_bytes():
            with Client(self.tls_port, implicit_tls=client_context(), timeout=120) as client:
                self.assertTrue(client.command("AUTHINFO USER " + user).startswith(b"381 "))
                self.assertTrue(client.command("AUTHINFO PASS " + PASSWORD).startswith(b"281 "))
                self.assertTrue(client.command("GROUP local.general").startswith(b"211 "))
                status, data = client.multiline("ARTICLE " + number)
                self.assertTrue(status.startswith(b"220 "), status)
                return data

        baseline = article_bytes()
        self.assertIn(body.encode("ascii"), baseline)
        status, _, page, _, _ = b.request("GET", "/a?g=local.general&n=" + number)
        self.assertEqual(status, 200, page)
        self.assertEqual(page.count(html.escape(line, quote=False)), 256)
        first = self.node.process
        self.node.stop(expect=EXIT.OK)
        report = self.node.store("compression", expect=EXIT.OK)
        match = re.search(rb"compressed-records=(\d+)", report.stdout)
        self.assertIsNotNone(match, report.stdout)
        self.assertGreater(int(match.group(1)), 0, report.stdout)
        self.node.start()
        # Restart also drops the old browser's process-local session.
        b = self.browser()
        _, _, page, _, _ = b.request("GET", "/signin")
        status, where, page, _, _ = b.request("POST", "/signin", {
            "pre": b.form_value(page, "pre"), "next": "/", "user": user, "password": PASSWORD})
        self.assertEqual((status, where), (303, "/"), page)
        status, _, page, _, _ = b.request("GET", "/a?g=local.general&n=" + number)
        self.assertEqual(status, 200, page)
        self.assertEqual(page.count(html.escape(line, quote=False)), 256)
        self.assertEqual(article_bytes(), baseline)
        second = self.node.process
        self.node.stop(expect=EXIT.OK)
        for process in (first, second):
            trace = process.stderr.since(0)
            issued = trace.count(b"DECODED-WINDOW issue ")
            self.assertGreater(issued, 0, process.diagnostics())
            self.assertEqual(trace.count(b"DECODED-WINDOW physical "), issued, trace[-8192:])
            self.assertEqual(trace.count(b"DECODED-WINDOW release "), issued, trace[-8192:])
            self.assertIn(b":PARTIAL-FIXED-STORAGE", trace)
            self.assertIn(b"word=:RELEASED", trace)
        self.node.start()  # Keep the class's other existing browser cases usable.

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
                except OSError as error:
                    # The server closed first (a reset before our half
                    # close): shutdown reports ENOTCONN.  A timeout stays
                    # an error.
                    if error.errno != errno.ENOTCONN:
                        raise
                    answer = b""
            self.assertTrue(answer == b"" or re.match(rb"HTTP/1\.1 [1-5]\d\d ", answer),
                            (raw[:120], answer[:120]))
        status, _, _, _, _ = self.browser().request("GET", "/signin")
        self.assertEqual(status, 200)


@requires(IMAGE)
class NativeWebFaceTests(FaceCases, unittest.TestCase):
    """Plain HTTP from loopback (the way a TLS proxy on the machine reaches it)."""
    TLS = False

    def test_4_fuzzed_requests_are_answered_or_closed(self):
        self.fuzz_requests_are_answered_or_closed()


@requires(IMAGE)
class NativeWebFaceTlsTests(FaceCases, unittest.TestCase):
    """The same visit with the face serving HTTPS itself ([web] tls = true,
    [listener]'s certificate): the session cookie is Secure."""
    TLS = True


if __name__ == "__main__":
    unittest.main()
