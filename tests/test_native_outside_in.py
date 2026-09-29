"""Outside-in: a stranger with a terminal and stock tools, against a node
they do not control, can do everything the docs claim.

Ember, 2026-09-29: "do we have a testsuite that curl can successfully do
everything we think we support?"  This module is that suite, and it is an
INDEPENDENT oracle: the node is started through tests/native_harness.Node
(lifecycle only: init, start, stop, the operator's own verbs) and then
driven ONLY by subprocesses of stock tools -- `curl` for the web face,
`openssl s_client` and `nc` for NNTP -- never by the harness's Client or
the web tests' Browser.  One test per documented claim; each docstring
quotes the claim with its doc path.  A claim a stock tool cannot exercise
is a FINDING: a packet in the lane's LANEDUMP and an expected failure here
that names it, never a silent skip.

Every run writes the claim -> command -> result table it observed to
FN_OUTSIDE_IN_EVIDENCE (default build/outside-in/): planning/evidence/
outside-in-2026-09-29.md is that table with a header.  Passwords and
invitation codes are masked in it (the repository is public).

FN_NATIVE_DEVELOPER_HOST names the developer image (default
build/fn-host-developer).  FN_OUTSIDE_IN_LIVE=1 also runs the read-only
class against the public node fn.fg-goose.online (never AUTHINFO with a
real credential, never POST, never XREDEEM); it is off by default.
"""
import html
import json
import os
import queue
import re
import shlex
import subprocess
import sys
import threading
import time
import unittest
import zlib
from pathlib import Path

from tests.native_harness import EXIT, Node, ROOT, class_case, free_port, native_image, requires

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
LIVE = os.environ.get("FN_OUTSIDE_IN_LIVE") == "1"
PUBLIC_NODE = "fn.fg-goose.online"
EVIDENCE_DIR = Path(os.environ.get("FN_OUTSIDE_IN_EVIDENCE", ROOT / "build" / "outside-in"))
PASSWORD = "stranger-secret-7"
OTHER_PASSWORD = "another-secret-8"

# The keywords fn FAQ part 2 lists (docs/articles/fn-faq-2.txt, "generated
# from books/protocol-table.lisp"): HELP must name each one (NNT-038).
FAQ2_COMMANDS = ("CAPABILITIES HELP MODE QUIT GROUP LISTGROUP LAST NEXT ARTICLE HEAD BODY STAT "
                 "OVER XOVER HDR XHDR XPAT LIST NEWGROUPS NEWNEWS DATE POST IHAVE CHECK TAKETHIS "
                 "AUTHINFO STARTTLS XREDEEM XFNCATCHUP").split()


# -----------------------------------------------------------------------------
# The evidence table.  Every test records the stock commands it ran and what
# it saw; tearDownModule writes the table.

ROWS = []


def _mask(text, secrets):
    for secret in secrets:
        if secret:
            text = text.replace(secret, "…")
    return text


class Recorded(unittest.TestCase):
    """A test that records its commands, what it saw and its verdict."""

    SECRETS = (PASSWORD, OTHER_PASSWORD)

    def setUp(self):
        self.commands, self.seen, self.secrets = [], [], list(self.SECRETS)

    def hide(self, secret):
        self.secrets.append(secret)

    def ran(self, argv, transcript=None):
        text = shlex.join(str(a) for a in argv)
        if transcript:
            text += " <<< " + " | ".join(transcript)
        self.commands.append(_mask(text, self.secrets))

    def saw(self, what):
        self.seen.append(_mask(str(what), self.secrets))

    def run(self, result=None):
        result = result or self.defaultTestResult()
        before = tuple(len(getattr(result, name, ())) for name in
                       ("failures", "errors", "skipped", "expectedFailures", "unexpectedSuccesses"))
        try:
            return super().run(result)
        finally:
            after = tuple(len(getattr(result, name, ())) for name in
                          ("failures", "errors", "skipped", "expectedFailures", "unexpectedSuccesses"))
            names = ("FAIL", "ERROR", "skipped", "expected failure (finding)", "UNEXPECTED SUCCESS")
            verdict = "ok"
            for i, name in enumerate(names):
                if after[i] > before[i]:
                    verdict = name
            doc = (self._testMethodDoc or "").strip()
            ROWS.append({"test": self.id().split(".")[-2] + "." + self._testMethodName,
                         "claim": " ".join(doc.split()),
                         "commands": list(getattr(self, "commands", [])),
                         "seen": list(getattr(self, "seen", [])),
                         "verdict": verdict})


def tearDownModule():
    EVIDENCE_DIR.mkdir(parents=True, exist_ok=True)
    (EVIDENCE_DIR / "outside-in.json").write_text(json.dumps(ROWS, indent=1), encoding="utf-8")
    lines = ["| test | claim (doc) | stock command(s) | what the stranger saw | verdict |",
             "| --- | --- | --- | --- | --- |"]
    for row in ROWS:
        cell = lambda items: "<br>".join("`%s`" % i.replace("|", "\\|").replace("`", "'")
                                         for i in items) or "-"
        lines.append("| %s | %s | %s | %s | %s |" % (
            row["test"], row["claim"].replace("|", "\\|"), cell(row["commands"]),
            "<br>".join(s.replace("|", "\\|") for s in row["seen"]) or "-", row["verdict"]))
    (EVIDENCE_DIR / "outside-in.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


# -----------------------------------------------------------------------------
# curl: what a stranger's terminal does to the web face.

class Reply:
    def __init__(self, status, headers, body, exit_code, stderr):
        self.status, self.headers, self.body = status, headers, body
        self.exit, self.stderr = exit_code, stderr

    def header(self, name):
        for key, value in self.headers:
            if key == name.lower():
                return value
        return None

    @property
    def cookies(self):
        return [value for key, value in self.headers if key == "set-cookie"]

    def form_value(self, name):
        # As a browser reads an attribute: its character references decoded.
        match = re.search(r"name='%s' value='([^']*)'" % name, self.body)
        if match is None:
            raise AssertionError("no field %r in the page:\n%s" % (name, self.body[:600]))
        return html.unescape(match.group(1))

    def __repr__(self):
        return "Reply(%s, exit %s)\n%s" % (self.status, self.exit, self.body[:600])


class Curl:
    """`curl` against one face.  JAR is a cookie jar file (-c/-b), the way a
    browser keeps a session; CACERT the node's own certificate."""

    def __init__(self, case, base, cacert=None, jar=None, extra=()):
        self.case, self.base, self.cacert, self.jar = case, base, cacert, jar
        self.extra = list(extra)
        self.n = 0

    def __call__(self, path, *args, data=None, timeout=60, record=True, verify=True):
        scratch = self.case.scratch
        self.n += 1
        body_file = scratch / ("body-%d" % self.n)
        head_file = scratch / ("head-%d" % self.n)
        argv = ["curl", "-sS", "--max-time", str(timeout), "-o", str(body_file), "-D", str(head_file)]
        if self.cacert and verify:
            argv += ["--cacert", str(self.cacert)]
        if self.jar:
            argv += ["-c", str(self.jar), "-b", str(self.jar)]
        argv += self.extra
        if data is not None:
            for key, value in data.items():
                argv += ["--data-urlencode", "%s=%s" % (key, value)]
        argv += list(args) + [self.base + path]
        if record:
            # The stranger's line: no scratch paths, and the form's field
            # names in place of its values (tokens and the password).
            shown, skip = [], False
            for word in argv:
                if skip:
                    skip = False
                    continue
                if word in ("-o", "-D", "--data-urlencode"):
                    skip = True
                    continue
                if self.jar and word == str(self.jar):
                    word = "jar"
                if self.cacert and word == str(self.cacert):
                    word = "node-cert.pem"
                shown.append(word)
            if data is not None:
                shown.insert(-1, "[form: %s]" % " ".join(data))
            self.case.ran(shown)
        done = subprocess.run(argv, capture_output=True, timeout=timeout + 30)
        status, headers = 0, []
        if head_file.exists():
            blocks = [b for b in head_file.read_bytes().split(b"\r\n\r\n") if b.strip()]
            if blocks:
                lines = blocks[-1].decode("iso-8859-1").split("\r\n")
                match = re.match(r"HTTP/\S+ (\d{3})", lines[0])
                status = int(match.group(1)) if match else 0
                for line in lines[1:]:
                    key, _, value = line.partition(":")
                    if _:
                        headers.append((key.strip().lower(), value.strip()))
        body = body_file.read_bytes().decode("utf-8", "replace") if body_file.exists() else ""
        return Reply(status, headers, body, done.returncode, done.stderr.decode("utf-8", "replace"))


# -----------------------------------------------------------------------------
# nc / openssl s_client: an interactive NNTP conversation through a stock
# tool.  The test types commands and reads the replies as a person would;
# nothing is pipelined after a command that needs an answer first.

class Talk:
    def __init__(self, case, argv, timeout=60):
        self.case, self.argv, self.timeout = case, argv, timeout
        self.transcript = []
        self.process = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE)
        self.lines = queue.Queue()
        self.err = []
        self.pumps = [threading.Thread(target=self._pump, daemon=True),
                      threading.Thread(target=self._pump_err, daemon=True)]
        for pump in self.pumps:
            pump.start()
        case.addCleanup(self.close)

    def _pump(self):
        for raw in iter(self.process.stdout.readline, b""):
            self.lines.put(raw)
        self.lines.put(None)

    def _pump_err(self):
        for raw in iter(self.process.stderr.readline, b""):
            self.err.append(raw.decode("utf-8", "replace"))

    def line(self, timeout=None):
        try:
            raw = self.lines.get(timeout=timeout or self.timeout)
        except queue.Empty:
            raise AssertionError("no reply within %s s; sent %r; stderr %r" % (
                timeout or self.timeout, self.transcript[-3:], "".join(self.err)[-400:]))
        if raw is None:
            raise AssertionError("the connection closed; sent %r; stderr %r" % (
                self.transcript[-3:], "".join(self.err)[-400:]))
        return raw.decode("utf-8", "replace").rstrip("\r\n")

    def expect(self, *codes):
        reply = self.line()
        if reply[:3] not in codes:
            raise AssertionError("expected %s, got %r (after %r)" % (
                "/".join(codes), reply, self.transcript[-2:]))
        return reply

    def send(self, text):
        self.transcript.append(text)
        self.process.stdin.write(text.encode("utf-8") + b"\r\n")
        self.process.stdin.flush()

    def command(self, text, *codes):
        self.send(text)
        return self.expect(*codes)

    def block(self):
        out = []
        while True:
            line = self.line()
            if line == ".":
                return out
            out.append(line[1:] if line.startswith("..") else line)

    def multiline(self, text, *codes):
        reply = self.command(text, *codes)
        return reply, self.block()

    def article(self, octets):
        """Send OCTETS (CRLF lines) dot-stuffed and terminated, after a 340."""
        for line in octets.split(b"\r\n"):
            if line.startswith(b"."):
                line = b"." + line
            self.process.stdin.write(line + b"\r\n")
        self.process.stdin.write(b".\r\n")
        self.process.stdin.flush()
        self.transcript.append("<article>")

    def post(self, octets):
        self.command("POST", "340")
        self.article(octets)
        # The 240 read here is the line books/productive-observer.lisp names
        # (fn-pcx-observer-240-code, PRF-1003): the first three octets of
        # *fn-pcx-240-line*, the durable outcome fn-pcx-post-productive reaches.
        return self.expect("240", "441", "480", "502")

    def quit(self):
        reply = self.command("QUIT", "205")
        self.process.stdin.close()
        try:
            self.process.wait(timeout=20)
        except subprocess.TimeoutExpired:
            self.process.kill()
            raise AssertionError("the tool did not exit after the 205")
        self.close()
        return reply

    def close(self):
        if self.process.poll() is None:
            self.process.kill()
            self.process.wait(timeout=10)
        for pump in self.pumps:
            pump.join(timeout=5)
        for pipe in (self.process.stdin, self.process.stdout, self.process.stderr):
            try:
                pipe.close()
            except (OSError, ValueError):
                pass

    def record(self):
        self.case.ran(self.argv, [t for t in self.transcript if not t.startswith("<")])


def article_octets(message_id, group, subject, body, sender, headers=()):
    lines = ["From: " + sender, "Newsgroups: " + group, "Subject: " + subject,
             "Message-ID: " + message_id] + list(headers)
    return ("\r\n".join(lines) + "\r\n\r\n").encode("utf-8") + body.encode("utf-8") + b"\r\n"


# -----------------------------------------------------------------------------
# The scratch node a stranger meets: NNTP on a plain port (STARTTLS) and an
# implicit-TLS port, the web face serving HTTPS itself, logins required and
# only over TLS, one operator-made login (alice) and invitation codes.

class NodeCase(Recorded):
    """The node's lifecycle (the only use of the harness) and the stock-tool
    helpers on it."""

    @classmethod
    def start_node(cls, name, web_extra="tls = true\n", web_host=None, listener_extra=""):
        node = cls.node = Node(class_case(cls), IMAGE, name=name)
        node.use_tls(alt_name=True, protected_only=False)
        cls.web_port = free_port()
        cls.auth_file = node.root / "auth.toml"
        web = '[web]\nport = {}\nsite = "Friends news"\ndomain = "friends.invalid"\n{}'.format(
            cls.web_port, web_extra)
        if web_host:
            web += 'host = "{}"\n'.format(web_host)
        node.write_config(extra=(
            'tls_port = {}\ntls_cert = "{}"\ntls_key = "{}"\n{}\n'
            '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n\n{}'.format(
                node.tls_port, node.cert, node.root / "key.pem", listener_extra, cls.auth_file, web)))
        node.init("local.general", "local.test", "control.cancel", timeout=240)
        node.operator("principal", "set-password", "alice", "--posting",
                      input=(PASSWORD + "\n" + PASSWORD + "\n").encode(), expect=EXIT.OK, timeout=240)
        node.listening = 3
        cls.process = node.start(timeout=240)
        cls.scratch = node.root / "stranger"
        cls.scratch.mkdir(exist_ok=True)
        return node

    def setUp(self):
        super().setUp()
        self.scratch = type(self).scratch

    # --- curl --------------------------------------------------------------

    def face(self, jar=None, extra=()):
        base = "https://127.0.0.1:%d" % self.web_port
        return Curl(self, base, cacert=self.node.cert, jar=jar, extra=extra)

    def jar(self, name):
        path = self.scratch / ("jar-%s-%s" % (name, self._testMethodName))
        if path.exists():
            path.unlink()
        return path

    def invite(self):
        result = self.node.operator("account", "invite", "--expires", "3600", timeout=240,
                                    expect=EXIT.OK)
        codes = re.findall(rb"^[0-9a-f]{32}$", result.stdout, re.M)
        self.assertEqual(len(codes), 1, result.stdout)
        code = codes[0].decode("ascii")
        self.hide(code)
        return code

    def sign_in(self, web, user, password=PASSWORD):
        form = web("/signin")
        self.assertEqual(form.status, 200, form)
        return web("/signin", data={"pre": form.form_value("pre"), "next": "/", "user": user,
                                    "password": password})

    def make_account(self, web, user, password=PASSWORD):
        form = web("/redeem")
        self.assertEqual(form.status, 200, form)
        return web("/redeem", data={"pre": form.form_value("pre"), "code": self.invite(),
                                    "user": user, "password": password, "again": password})

    # --- nc / openssl ---------------------------------------------------------

    def plain(self, port=None):
        return Talk(self, ["nc", "-w", "60", "127.0.0.1", str(port or self.node.port)])

    def tls(self, verify=True, starttls=False):
        argv = ["openssl", "s_client", "-quiet", "-connect",
                "127.0.0.1:%d" % (self.node.port if starttls else self.node.tls_port)]
        if verify:
            argv += ["-CAfile", str(self.node.cert), "-verify_return_error",
                     "-verify_ip", "127.0.0.1"]
        if starttls:
            argv += ["-starttls", "nntp"]
        return Talk(self, argv)

    def login(self, talk, user, password=PASSWORD):
        talk.command("AUTHINFO USER " + user, "381")
        return talk.command("AUTHINFO PASS " + password, "281", "481")

    def reader(self, user="wren", password=PASSWORD):
        """A logged-in implicit-TLS conversation (the greeting consumed)."""
        talk = self.tls()
        talk.expect("200", "201")
        self.assertTrue(self.login(talk, user, password).startswith("281"))
        return talk


# -----------------------------------------------------------------------------

@requires(IMAGE)
class StrangerTests(NodeCase):
    """A stranger at the node's web face (HTTPS, the node's own certificate)
    and its two NNTP ports, with stock tools only."""

    @classmethod
    def setUpClass(cls):
        cls.start_node("stranger")
        cls.state = {}

    # ---- the web face ---------------------------------------------------------

    def test_a01_the_front_door_is_the_sign_in_page(self):
        """docs/web.md: "Open https://news.example.org/ in your browser. You see
        the sign-in page."  docs/web.md: "Every sign-in is the node's own login
        check (AUTHINFO)"."""
        web = self.face()
        front = web("/")
        self.assertEqual((front.status, front.header("location")), (303, "/signin"), front)
        page = web("/signin")
        self.assertEqual(page.status, 200, page)
        self.assertIn("text/html; charset=utf-8", page.header("content-type"))
        self.assertIn(">Sign in</button>", page.body)
        self.assertIn("Make your account", page.body)
        self.assertIn("default-src 'none'", page.header("content-security-policy"))
        self.saw("GET / -> 303 /signin; GET /signin -> 200 text/html, CSP %s" %
                 page.header("content-security-policy"))

    def test_a02_the_certificate_is_checked(self):
        """docs/public-node.md: "Leave certificate checking on".
        docs/human-web-client.md: "Do not use -k: it skips the check, and then
        the connection is not safe."  docs/web.md: the friend needs "the
        node's certificate file, unless it uses a public one"."""
        web = self.face()
        unverified = web("/signin", verify=False)
        self.assertEqual(unverified.exit, 60, unverified.stderr)       # CURLE_PEER_FAILED_VERIFICATION
        verified = web("/signin")
        self.assertEqual((verified.exit, verified.status), (0, 200), verified)
        self.saw("without --cacert: curl exit 60 (%s)" % unverified.stderr.strip()[:80])
        self.saw("with --cacert node.cert: 200")

    def test_a03_make_an_account_from_an_invitation_code(self):
        """docs/reader.md: "The first time, press Make your account, type the
        invitation code you were given, and choose a name and a password."
        docs/web.md: "Then they are in."  docs/web.md: "It never writes a
        password down." (no page carries it)."""
        web = self.face(jar=self.jar("wren"))
        made = self.make_account(web, "wren")
        self.assertEqual((made.status, made.header("location")), (303, "/"), made)
        session = [c for c in made.cookies if c.startswith("fnr_session=")]
        self.assertEqual(len(session), 1, made.cookies)
        for flag in ("HttpOnly", "SameSite=Lax", "Secure"):
            self.assertIn(flag, session[0])
        home = web("/")
        self.assertEqual(home.status, 200, home)
        self.assertIn("local.general", home.body)
        self.assertIn("<span>wren</span>", home.body)
        self.assertNotIn(PASSWORD, made.body + home.body)
        self.state["wren_jar"] = web.jar
        self.saw("POST /redeem -> 303 /; Set-Cookie %s" % session[0].split(";", 1)[1].strip())
        self.saw("GET / -> 200, lists local.general, signed in as wren")

    def test_a04_a_used_or_wrong_code_is_refused(self):
        """docs/web.md: '"That invitation code didn't work". The code was used,
        has expired or was mistyped, or the name is taken.'  docs/operator.md:
        an invitation code "works once"."""
        code = self.invite()
        first = self.face(jar=self.jar("first"))
        form = first("/redeem")
        used = first("/redeem", data={"pre": form.form_value("pre"), "code": code, "user": "robin1",
                                      "password": PASSWORD, "again": PASSWORD})
        self.assertEqual(used.status, 303, used)
        second = self.face(jar=self.jar("second"))
        form = second("/redeem")
        again = second("/redeem", data={"pre": form.form_value("pre"), "code": code, "user": "robin2",
                                        "password": PASSWORD, "again": PASSWORD})
        self.assertEqual(again.status, 403, again)
        self.assertIn("didn&#39;t work", again.body)
        form = second("/redeem")
        typo = second("/redeem", data={"pre": form.form_value("pre"), "code": "mistyped", "user": "robin3",
                                       "password": PASSWORD, "again": PASSWORD})
        self.assertEqual(typo.status, 403, typo)
        self.saw("the code once: 303; the same code again: 403 \"didn't work\"; a mistyped code: 403")

    def test_a05_sign_in_with_the_operator_made_login_and_a_wrong_password(self):
        """docs/web.md: "Accounts made with principal set-password sign in here
        as well."  docs/web.md: '"That name and password don't match." The
        node refused the login.'"""
        web = self.face(jar=self.jar("alice"))
        wrong = self.sign_in(web, "alice", "not-the-password")
        self.assertEqual(wrong.status, 401, wrong)
        self.assertIn("don&#39;t match", wrong.body)
        right = self.sign_in(web, "alice")
        self.assertEqual((right.status, right.header("location")), (303, "/"), right)
        home = web("/")
        self.assertEqual(home.status, 200)
        self.assertIn("<span>alice</span>", home.body)
        self.state["alice_jar"] = web.jar
        self.saw("wrong password: 401 \"That name and password don't match.\"; right: 303 /, signed in")

    def test_a06_post_to_a_group(self):
        """docs/reader.md: "post to this group at the top of a group, then
        Post."  docs/reader.md: '"Posted!" The server took your post.'"""
        web = self.face(jar=self.state["wren_jar"])
        group = web("/g?name=local.general")
        self.assertEqual(group.status, 200, group)
        self.assertIn(">post to this group</a>", group.body)
        compose = web("/new?g=local.general")
        self.assertEqual(compose.status, 200, compose)
        self.assertIn("name='subject'", compose.body)
        posted = web("/post", data={"csrf": compose.form_value("csrf"), "g": "local.general",
                                    "subject": "Hello from a stranger",
                                    "body": "Typed into curl. Grüße ✓\r\n.\r\n<b>not bold</b>"})
        self.assertEqual(posted.status, 200, posted)
        self.assertIn("Posted!", posted.body)
        self.saw("GET /new?g=local.general -> 200 form; POST /post -> 200 \"Posted!\"")

    def test_a07_read_the_group_and_the_post(self):
        """docs/reader.md: "Pick a group. The newest posts are listed ... Open a
        post to read it."  docs/web.md: "text from articles is always
        escaped"."""
        web = self.face(jar=self.state["wren_jar"])
        group = web("/g?name=local.general")
        self.assertEqual(group.status, 200, group)
        match = re.search(r"href='/a\?g=local.general&amp;n=(\d+)'>Hello from a stranger", group.body)
        self.assertIsNotNone(match, group.body[:800])
        self.state["web_post_number"] = match.group(1)
        post = web("/a?g=local.general&n=" + match.group(1))
        self.assertEqual(post.status, 200, post)
        self.assertIn("Typed into curl. Grüße ✓", post.body)
        self.assertIn("&lt;b&gt;not bold&lt;/b&gt;", post.body)
        self.assertNotIn("<b>not bold</b>", post.body)
        self.assertIn("Remove my post", post.body)
        self.saw("GET /g?name=local.general lists the post as #%s; GET /a?g=..&n=%s -> 200, "
                 "the body shown, <b> escaped to &lt;b&gt;" % (match.group(1), match.group(1)))

    def test_a08_remove_my_post(self):
        """docs/reader.md: "You can remove a post you wrote: open it and press
        Remove my post, then Remove it. It disappears from this server."
        docs/web.md: "every post and removal the node's own answer"."""
        web = self.face(jar=self.state["wren_jar"])
        post = web("/a?g=local.general&n=" + self.state["web_post_number"])
        link = re.search(r"href='(/remove\?[^']+)'>Remove my post", post.body)
        self.assertIsNotNone(link, post.body[:800])
        confirm = web(html.unescape(link.group(1)))
        self.assertEqual(confirm.status, 200, confirm)
        self.assertIn(">Remove it</button>", confirm.body)
        removed = web("/remove", data={"csrf": confirm.form_value("csrf"), "id": confirm.form_value("id"),
                                       "g": "local.general"})
        self.assertEqual(removed.status, 200, removed)
        self.assertIn("Your post has been removed", removed.body)
        group = web("/g?name=local.general")
        self.assertNotIn("Hello from a stranger", group.body)
        self.saw("GET /remove?.. -> 200 \"Remove it\"; POST /remove -> 200 \"Your post has been removed\"; "
                 "the group no longer lists it")

    def test_a09_the_server_said_no(self):
        """docs/reader.md: '"The server said no", with its reason. Nothing was
        published.'"""
        web = self.face(jar=self.state["wren_jar"])
        home = web("/")
        refused = web("/post", data={"csrf": home.form_value("csrf"), "g": "no.such.group",
                                     "subject": "into the void", "body": "nothing"})
        self.assertIn("The server said no", refused.body, refused)
        self.saw("POST /post to a group that does not exist -> %d \"The server said no\"" % refused.status)

    def test_a10_a_group_you_may_not_see_does_not_exist_for_you(self):
        """docs/reader.md: "Groups you are not allowed to see do not appear, and
        their addresses say "There's no group by that name here, or you can't
        read it". The server decides that, not the page."  docs/operator.md:
        "A group outside a login's rule does not exist for that login."."""
        web = self.face(jar=self.state["wren_jar"])
        unknown = web("/g?name=no.such.group")
        self.assertIn("no group by that name here, or you can&#39;t read it", unknown.body, unknown)
        self.node.operator("account", "access", "alice", "--read", "local.general",
                           "--post", "local.general", expect=EXIT.OK, timeout=240)
        alice = self.face(jar=self.jar("alice-limited"))
        self.assertEqual(self.sign_in(alice, "alice").status, 303)
        home = alice("/")
        self.assertIn("local.general", home.body)
        self.assertNotIn("local.test", home.body)
        hidden = alice("/g?name=local.test")
        self.assertIn("no group by that name here, or you can&#39;t read it", hidden.body, hidden)
        self.saw("unknown group: %d with the sentence; after `account access alice --read local.general "
                 "--post local.general`: / omits local.test and /g?name=local.test says the same sentence"
                 % unknown.status)

    def test_a11_light_dark_or_automatic_colours(self):
        """docs/reader.md: "Light, Dark or Automatic colours are at the bottom
        of every page."  docs/articles/fn-faq-11.txt: "Light, dark or
        automatic colours."."""
        web = self.face(jar=self.state["wren_jar"])
        home = web("/")
        for value in ("light", "dark", "auto"):
            self.assertIn("name='theme' value='%s'" % value, home.body)
        chosen = web("/theme", data={"theme": "dark"})
        self.assertIn(chosen.status, (200, 303), chosen)
        self.assertTrue(any(c.startswith("fnr_theme=dark") for c in chosen.cookies), chosen.cookies)
        home = web("/")
        self.assertIn("value='dark' class='quiet' aria-pressed='true'", home.body)
        self.saw("POST /theme theme=dark -> %d, Set-Cookie fnr_theme=dark; the Dark button is pressed"
                 % chosen.status)

    def test_a12_sign_out(self):
        """docs/reader.md: "Sign out is at the top."  docs/web.md: a session
        "ends when they sign out"."""
        web = self.face(jar=self.state["alice_jar"])
        home = web("/")
        self.assertEqual(home.status, 200, home)
        out = web("/signout", data={"csrf": home.form_value("csrf")})
        self.assertEqual((out.status, out.header("location")), (303, "/signin"), out)
        self.assertTrue(any(c.startswith("fnr_session=") and "Max-Age=0" in c for c in out.cookies),
                        out.cookies)
        after = web("/")
        self.assertEqual((after.status, after.header("location")), (303, "/signin"), after)
        self.saw("POST /signout -> 303 /signin, the session cookie cleared; GET / -> 303 /signin")

    def test_a13_no_page_carries_a_script(self):
        """docs/web.md: "the pages carry no scripts (Content-Security-Policy:
        default-src 'none')"."""
        web = self.face(jar=self.state["wren_jar"])
        pages = ["/signin", "/redeem", "/", "/g?name=local.general", "/new?g=local.general",
                 "/g?name=no.such.group"]
        for path in pages:
            page = web(path)
            self.assertTrue(page.status in (200, 404) or path.endswith("no.such.group"), (path, page))
            self.assertIn("default-src 'none'", page.header("content-security-policy") or "", path)
            self.assertNotIn("<script", page.body.lower(), path)
        self.saw("%d pages: every one carries CSP default-src 'none' and no <script" % len(pages))

    def test_a14_the_page_fits_a_phone(self):
        """docs/web.md: "from any browser, phone included".
        docs/articles/fn-faq-11.txt: "Phones work."  (What a terminal can
        check: the viewport meta, and a style sheet with no fixed width wider
        than a phone.)"""
        web = self.face(jar=self.state["wren_jar"])
        home = web("/")
        self.assertIn("<meta name='viewport' content='width=device-width, initial-scale=1'>", home.body)
        css = web("/style.css")
        self.assertEqual(css.status, 200, css)
        self.assertIn("text/css", css.header("content-type"))
        wide = [w for w in re.findall(r"(?<!max-)(?<!min-)width\s*:\s*(\d+)px", css.body) if int(w) > 390]
        self.assertEqual(wide, [], "fixed widths wider than a phone: %s" % wide)
        self.saw("viewport meta present; /style.css 200 text/css with no fixed width over 390px")

    def test_a15_http_features_the_docs_do_not_claim_observed(self):
        """Not claimed anywhere in docs/: HEAD, If-Modified-Since, gzip, HTTP/1.0,
        a /health route.  Recorded so the evidence says what a stranger gets;
        the only assertion is that each is answered and the face keeps
        serving."""
        web = self.face()
        head = web("/signin", "-I")
        ims = web("/style.css", "-H", "If-Modified-Since: Thu, 01 Jan 2026 00:00:00 GMT")
        gz = web("/style.css", "--compressed")
        old = web("/signin", "--http1.0")
        health = web("/health")
        for name, reply in (("HEAD", head), ("If-Modified-Since", ims), ("gzip", gz),
                            ("HTTP/1.0", old), ("/health", health)):
            self.assertTrue(100 <= reply.status < 600, (name, reply))
            self.saw("%s -> %d%s" % (name, reply.status, "" if reply.status < 500 else " (5xx!)"))
        self.saw("Cache-Control on /style.css: %s; Content-Encoding: %s; Last-Modified: %s" % (
            ims.header("cache-control"), gz.header("content-encoding"), ims.header("last-modified")))
        self.assertEqual(web("/signin").status, 200)

    # ---- NNTP ---------------------------------------------------------------

    def test_b01_greeting_capabilities_help_and_quit(self):
        """docs/articles/fn-faq-2.txt: "CAPABILITIES: What this node offers you
        now, as a list of labels"; "HELP: The commands this node answers, one
        per line"; "QUIT: Ends the connection".  specs/nntp.md NNT-038: HELP
        lists every command the served dispatcher recognizes."""
        talk = self.plain()
        greeting = talk.expect("200", "201")
        _, caps = talk.multiline("CAPABILITIES", "101")
        self.assertIn("VERSION 2", caps)
        self.assertIn("READER", caps)
        self.assertIn("STARTTLS", caps)
        _, help_lines = talk.multiline("HELP", "100")
        listed = set(" ".join(help_lines).split())
        missing = [c for c in FAQ2_COMMANDS if c not in listed]
        self.assertEqual(missing, [], "HELP does not list: %s\n%s" % (missing, help_lines))
        talk.quit()
        talk.record()
        self.saw("greeting %s; CAPABILITIES %s; HELP names all %d FAQ commands; QUIT 205 and nc exits"
                 % (greeting, caps, len(FAQ2_COMMANDS)))

    def test_b02_a_login_before_tls_is_refused(self):
        """docs/articles/fn-faq-2.txt: "A login before TLS is refused."
        docs/human-web-client.md: "The node refuses a login before the
        connection is encrypted."  specs/nntp.md NNT-034: XREDEEM "Before a TLS
        layer on a listener that requires one both lines are 483"."""
        talk = self.plain()
        talk.expect("200", "201")
        user = talk.command("AUTHINFO USER alice", "483")
        redeem = talk.command("XREDEEM not-a-code alice", "483")
        talk.quit()
        talk.record()
        self.saw("AUTHINFO USER -> %s; XREDEEM CODE -> %s" % (user, redeem))

    def test_b03_no_anonymous_reading(self):
        """docs/public-node.md: "There is no anonymous reading: you need a login
        even to look."  docs/articles/fn-faq-2.txt: "A * needs a login where
        the node requires one (480 otherwise)."."""
        talk = self.tls()
        talk.expect("200", "201")
        replies = [talk.command(c, "480") for c in ("GROUP local.general", "LIST", "ARTICLE 1",
                                                     "OVER 1-", "NEWNEWS * 20260101 000000 GMT")]
        talk.quit()
        talk.record()
        self.saw("before AUTHINFO, over TLS: %s" % sorted(set(replies)))

    def test_b04_starttls_on_the_plain_port_then_log_in(self):
        """docs/public-node.md: "Port 119: starts plain and switches to
        encryption with STARTTLS."  docs/articles/fn-faq-2.txt: "STARTTLS:
        Turns on TLS on this connection before you log in"; "MODE READER says
        whether you may post"; "AUTHINFO: Logs in: AUTHINFO USER name, then
        AUTHINFO PASS password"."""
        talk = self.tls(starttls=True)          # openssl s_client -starttls nntp
        _, caps = talk.multiline("CAPABILITIES", "101")
        self.assertNotIn("STARTTLS", caps)
        self.assertTrue(any(c.startswith("AUTHINFO USER") for c in caps), caps)
        twice = talk.command("STARTTLS", "502")
        talk.command("AUTHINFO USER alice", "381")
        ok = talk.command("AUTHINFO PASS " + PASSWORD, "281")
        mode = talk.command("MODE READER", "200", "201")
        talk.quit()
        talk.record()
        self.saw("after STARTTLS: CAPABILITIES %s; a second STARTTLS %s; login %s; MODE READER %s"
                 % (caps, twice, ok, mode))

    def test_b05_implicit_tls_port_and_its_certificate(self):
        """docs/public-node.md: "Port 563: encrypted from the first byte
        (NNTPS)."  docs/human-web-client.md: "The certificate must name the
        host tin dials."  docs/public-node.md: "Leave certificate checking
        on."."""
        talk = self.tls()
        greeting = talk.expect("200", "201")
        self.assertTrue(self.login(talk, "alice").startswith("281"))
        talk.quit()
        talk.record()
        # A stranger who checks the certificate against the wrong authority
        # never sees a greeting.
        wrong = Talk(self, ["openssl", "s_client", "-quiet", "-connect",
                            "127.0.0.1:%d" % self.node.tls_port, "-verify_return_error",
                            "-CAfile", "/dev/null"])
        wrong.process.stdin.close()
        wrong.process.wait(timeout=30)
        wrong.record()
        self.assertNotEqual(wrong.process.returncode, 0)
        self.assertTrue(wrong.lines.get(timeout=10) is None, "a greeting arrived over an unverified TLS")
        self.saw("port %d: greeting %s from the first byte, login 281 (CAfile = the node's cert, "
                 "-verify_ip 127.0.0.1); with the wrong CA: s_client exit %d, no greeting"
                 % (self.node.tls_port, greeting, wrong.process.returncode))

    def test_b06_a_wrong_password_is_481(self):
        """docs/web.md: "The node refused the login" (481; the page's "don't
        match" is this answer).  RFC 4643 section 2.3.2."""
        talk = self.tls()
        talk.expect("200", "201")
        reply = self.login(talk, "alice", "not-the-password")
        self.assertTrue(reply.startswith("481"), reply)
        talk.quit()
        talk.record()
        self.saw(reply)

    def test_b07_post_then_read_it_back_every_way(self):
        """docs/articles/fn-faq-2.txt: "POST: Sends an article; 340 asks for it,
        240 means it is stored"; "ARTICLE: Sends a whole article, by number, by
        Message-ID, or the current one"; HEAD, BODY, STAT.  docs/operator.md:
        "Every post by a login carries a line like this: Injection-Info: ...;
        posting-account=..."."""
        talk = self.reader()
        mid = "<outside-in-1@stranger.invalid>"
        reply = talk.post(article_octets(mid, "local.general", "A stranger posts over nc-less TLS",
                                         "First line.\r\n.leading dot\r\nLast line.",
                                         "wren <wren@friends.invalid>"))
        self.assertTrue(reply.startswith("240"), reply)
        group = talk.command("GROUP local.general", "211")
        count, first, last = group.split()[1:4]
        by_id = talk.command("STAT " + mid, "223")
        number = by_id.split()[1]
        _, whole = talk.multiline("ARTICLE " + mid, "220")
        self.assertIn("Last line.", whole)
        self.assertIn(".leading dot", whole)
        _, head = talk.multiline("HEAD " + number, "221")
        injection = [h for h in head if h.lower().startswith("injection-info:")]
        self.assertEqual(len(injection), 1, head)
        self.assertIn("posting-account=", injection[0])
        self.assertTrue(any(h.lower().startswith("cancel-lock:") for h in head), head)
        _, body = talk.multiline("BODY", "222")
        self.assertEqual(body[:1], ["First line."])
        current = talk.command("STAT", "223")
        gone = talk.command("ARTICLE <no-such@stranger.invalid>", "430")
        talk.quit()
        talk.record()
        self.state["nntp_mid"], self.state["nntp_number"] = mid, number
        self.saw("POST %s; GROUP %s; STAT by id %s; ARTICLE by id 220; HEAD by number 221 with %s; "
                 "BODY (current) 222; STAT (current) %s; unknown id %s"
                 % (reply, group, by_id, injection[0][:60] + "...", current, gone))

    def test_b08_group_navigation(self):
        """docs/articles/fn-faq-2.txt: "GROUP: Selects a group; answers its count
        and first and last numbers"; "LISTGROUP: Selects a group and lists its
        article numbers, optionally a range"; "LAST: Moves to the previous
        article"; "NEXT: Moves to the next article"."""
        talk = self.reader()
        group = talk.command("GROUP local.general", "211")
        count, first, last = (int(x) for x in group.split()[1:4])
        _, numbers = talk.multiline("LISTGROUP local.general", "211")
        self.assertTrue(numbers, "LISTGROUP listed nothing")
        self.assertTrue(all(first <= int(n) <= last for n in numbers), (group, numbers))
        low, high = int(numbers[0]), int(numbers[-1])
        _, ranged = talk.multiline("LISTGROUP local.general %d-%d" % (low, low), "211")
        self.assertEqual(ranged, [str(low)], ranged)
        talk.command("STAT %d" % low, "223")
        no_previous = talk.command("LAST", "422")
        moved = talk.command("NEXT", "223", "421")
        talk.command("STAT %d" % high, "223")
        no_next = talk.command("NEXT", "421")
        talk.quit()
        talk.record()
        self.saw("GROUP %s; LISTGROUP %d numbers; LISTGROUP with a range %s; LAST at the first %s; "
                 "NEXT %s; NEXT at the last %s" % (group, len(numbers), ranged, no_previous, moved, no_next))

    def test_b09_overview_headers_and_patterns(self):
        """docs/articles/fn-faq-2.txt: "OVER: Overview lines (subject, author,
        date, ids, size) for a range"; "XOVER: OVER's older spelling"; "HDR:
        One header field for a range; also :fn-verified, :fn-control and
        :fn-enrollment"; "XHDR"; "XPAT: XHDR filtered by a wildmat".
        specs/nntp.md NNT-052: LIST OVERVIEW.FMT and the Xref overview
        field."""
        talk = self.reader()
        talk.command("GROUP local.general", "211")
        _, fmt = talk.multiline("LIST OVERVIEW.FMT", "215")
        self.assertEqual(fmt[0].lower(), "subject:")
        self.assertIn("Xref:full", fmt)
        _, over = talk.multiline("OVER 1-", "224")
        self.assertTrue(over, "no overview lines")
        fields = over[-1].split("\t")
        self.assertGreaterEqual(len(fields), 9, fields)
        self.assertTrue(fields[8].startswith("Xref:"), fields[8])
        _, xover = talk.multiline("XOVER 1-", "224")
        self.assertEqual(xover, over)
        _, subjects = talk.multiline("HDR Subject 1-", "225")
        self.assertTrue(any("A stranger posts" in s for s in subjects), subjects)
        # :fn-verified takes a range; :fn-control and :fn-enrollment a
        # Message-ID (books/nntp.lisp; FAQ 2's one line does not say so, and
        # ":fn-control 1-" is 501).
        pseudo = {}
        mid = self.state["nntp_mid"]
        for field, arg in ((":fn-verified", "1-"), (":fn-control", mid), (":fn-enrollment", mid)):
            reply, lines = talk.multiline("HDR %s %s" % (field, arg), "225")
            pseudo[field] = lines[-1] if lines else reply
        _, xhdr = talk.multiline("XHDR Subject 1-", "221")
        self.assertEqual(xhdr, subjects)
        _, matched = talk.multiline("XPAT Subject 1- *stranger*", "221")
        self.assertTrue(any("A stranger posts" in m for m in matched), matched)
        _, none = talk.multiline("XPAT Subject 1- *nothing-like-this*", "221")
        self.assertEqual(none, [])
        _, headers = talk.multiline("LIST HEADERS", "215")
        talk.quit()
        talk.record()
        self.saw("OVERVIEW.FMT %s; OVER %d lines, %d fields, %s; XOVER identical; HDR Subject 225; "
                 "HDR %s; XHDR 221 identical; XPAT *stranger* 1 match; LIST HEADERS %s"
                 % (fmt, len(over), len(fields), fields[8][:40], pseudo, headers))

    def test_b10_list_variants(self):
        """docs/articles/fn-faq-2.txt: "LIST: Lists groups and server data; the
        second word names which."  The CAPABILITIES LIST line names the
        variants offered; docs/public-node.md: "A reader that asks the node
        which groups to start with (LIST SUBSCRIPTIONS)"; specs/nntp.md
        NNT-039: LIST MOTD and LIST NEWSGROUPS descriptions; RFC 2980 2.1.3:
        LIST ACTIVE.TIMES."""
        talk = self.reader()
        _, caps = talk.multiline("CAPABILITIES", "101")
        offered = [c for c in caps if c.startswith("LIST ")]
        self.assertEqual(len(offered), 1, caps)
        variants = offered[0].split()[1:]
        results = {}
        _, active = talk.multiline("LIST", "215")
        self.assertTrue(any(l.startswith("local.general ") for l in active), active)
        for variant in variants:
            reply, lines = talk.multiline("LIST " + variant, "215")
            results[variant] = len(lines)
        _, wild = talk.multiline("LIST ACTIVE local.*", "215")
        self.assertEqual(sorted(l.split()[0] for l in wild), ["local.general", "local.test"])
        sub_reply, subs = talk.multiline("LIST SUBSCRIPTIONS", "215")
        talk.quit()
        talk.record()
        self.saw("LIST 215 (%d groups); offered %s -> lines %s; LIST ACTIVE local.* -> %s; "
                 "LIST SUBSCRIPTIONS %s %s" % (len(active), variants, results,
                                                [l.split()[0] for l in wild], sub_reply, subs))

    def test_b11_the_clock_new_groups_and_new_news(self):
        """docs/articles/fn-faq-2.txt: "DATE: The node's clock, in UTC";
        "NEWGROUPS: Groups created since a date and time (UTC)"; "NEWNEWS:
        Message-IDs of articles accepted since a date, in matching groups"."""
        talk = self.reader()
        date = talk.command("DATE", "111")
        self.assertRegex(date, r"^111 \d{14}$")
        _, groups = talk.multiline("NEWGROUPS 20260101 000000 GMT", "231")
        self.assertTrue(any(g.startswith("local.general ") for g in groups), groups)
        _, ids = talk.multiline("NEWNEWS local.* 20260101 000000 GMT", "230")
        self.assertIn(self.state["nntp_mid"], ids)
        talk.quit()
        talk.record()
        self.saw("%s; NEWGROUPS %d groups; NEWNEWS local.* %d ids including the stranger's post"
                 % (date, len(groups), len(ids)))

    def test_b12_transit_verbs_are_for_peers(self):
        """docs/articles/fn-faq-2.txt: "IHAVE ... (peers only)", "CHECK ...
        (peers only)", "TAKETHIS ... (peers only)", "XFNCATCHUP ... (peers
        only)".  specs/nntp.md NNT-038: "a reader connection answers the three
        transit verbs 502 (RFC 3977 section 3.2.1: understood, not
        permitted)"."""
        talk = self.reader()
        replies = {c: talk.command(c, "502", "480", "500", "501")
                   for c in ("IHAVE <x@stranger.invalid>", "CHECK <x@stranger.invalid>",
                             "TAKETHIS <x@stranger.invalid>", "MODE STREAM", "XFNCATCHUP 0")}
        for verb in ("IHAVE", "CHECK", "TAKETHIS"):
            self.assertTrue(replies[verb + " <x@stranger.invalid>"].startswith("502"), replies)
        talk.quit()
        talk.record()
        self.saw(replies)

    def test_b13_a_command_help_does_not_list_is_500(self):
        """specs/nntp.md NNT-038: "a command HELP does not list is answered 500";
        keystone PRF-194: exactly "500 command not recognized"."""
        talk = self.reader()
        unknown = talk.command("FROBNICATE now", "500")
        self.assertEqual(unknown, "500 command not recognized")
        lower, _ = talk.multiline("help", "100")
        talk.quit()
        talk.record()
        self.saw("FROBNICATE -> %s; lowercase help -> %s" % (unknown, lower))

    def test_b14_redeem_an_invitation_over_nntp(self):
        """docs/public-node.md: "a program can do the same over TLS: send
        XREDEEM CODE LOGIN, then XREDEEM PASS PASSWORD" ... "Start a new
        connection for it: the one that redeemed the code cannot log in."
        docs/operator.md: the code works once.  specs/nntp.md NNT-034: 381,
        then 281 or 482; "XREDEEM PASS with nothing cached is 482"; "on an
        authenticated connection 502".  (CODE in the docs is the code
        itself, the operator's 32 hexadecimal characters; the literal word
        answers 501 -- run 1 of this suite typed it.)"""
        code = self.invite()
        talk = self.tls()
        talk.expect("200", "201")
        nothing = talk.command("XREDEEM PASS " + OTHER_PASSWORD, "482")
        asked = talk.command("XREDEEM %s robin" % code, "381")
        bound = talk.command("XREDEEM PASS " + OTHER_PASSWORD, "281")
        self.assertIn("new connection", bound)
        talk.send("AUTHINFO USER robin")
        same = talk.line()
        if same.startswith("381"):
            same = talk.command("AUTHINFO PASS " + OTHER_PASSWORD, "481", "482", "502", "281")
        self.assertFalse(same.startswith("281"), "the redeeming connection logged in: " + same)
        talk.quit()
        talk.record()
        fresh = self.tls()
        fresh.expect("200", "201")
        ok = self.login(fresh, "robin", OTHER_PASSWORD)
        self.assertTrue(ok.startswith("281"), ok)
        authed = fresh.command("XREDEEM %s robin9" % code, "502")
        fresh.quit()
        fresh.record()
        again = self.tls()
        again.expect("200", "201")
        again.command("XREDEEM %s robin9" % code, "381")
        refused = again.command("XREDEEM PASS " + OTHER_PASSWORD, "482")
        again.quit()
        again.record()
        self.state["robin"] = OTHER_PASSWORD
        self.saw("PASS with nothing cached %s; CODE %s; PASS %s; AUTHINFO on the same connection %s; "
                 "new connection AUTHINFO %s; XREDEEM when authenticated %s; the code again %s"
                 % (nothing, asked, bound, same, ok, authed, refused))

    def test_b15_cancel_your_own_post_and_only_your_own(self):
        """docs/human-web-client.md: "Use your reader's cancel command, logged in
        as yourself. The post disappears on this node ... Another login's
        cancel of your post is kept but does nothing ... Readers then get 430
        withdrawn."  docs/public-node.md: "You can cancel your own posts from
        your reader."."""
        mid = "<outside-in-cancel@stranger.invalid>"
        wren = self.reader()
        self.assertTrue(wren.post(article_octets(mid, "local.general", "To be withdrawn", "soon gone",
                                                 "wren <wren@friends.invalid>")).startswith("240"))
        wren.quit()
        wren.record()
        # tin's cancel: a control article in the same group, Subject "cmsg
        # cancel <id>", Control "cancel <id>" (RFC 5537 section 5.3).
        def cancel(sender, tag):
            return article_octets("<outside-in-cancel-%s@stranger.invalid>" % tag, "local.general",
                                  "cmsg cancel " + mid, "cancel", sender, ("Control: cancel " + mid,))
        robin = self.reader("robin", self.state["robin"])
        other = robin.post(cancel("robin <robin@friends.invalid>", "robin"))
        still = robin.command("STAT " + mid, "223")
        robin.quit()
        robin.record()
        wren = self.reader()
        own = wren.post(cancel("wren <wren@friends.invalid>", "wren"))
        withdrawn = wren.command("STAT " + mid, "430")
        article = wren.command("ARTICLE " + mid, "430")
        wren.quit()
        wren.record()
        self.saw("robin's cancel of wren's post: %s, then STAT %s (kept, nothing withdrawn); wren's own "
                 "cancel: %s, then STAT %s, ARTICLE %s" % (other, still, own, withdrawn, article))

    def test_b16_a_repeated_message_id_is_refused_with_its_reason(self):
        """docs/public-node.md: "A post is either accepted (saved), refused (with
        the reason), or, rarely, uncertain: then send the same article again,
        with the same Message-ID ... the node answers that it already has
        it"."""
        talk = self.reader()
        before = talk.command("GROUP local.general", "211").split()[1]
        same = talk.post(article_octets(self.state["nntp_mid"], "local.general",
                                        "A stranger posts over nc-less TLS",
                                        "First line.\r\n.leading dot\r\nLast line.",
                                        "wren <wren@friends.invalid>"))
        other = talk.post(article_octets(self.state["nntp_mid"], "local.general", "the same id again",
                                         "different text", "wren <wren@friends.invalid>"))
        after = talk.command("GROUP local.general", "211").split()[1]
        self.assertEqual(before, after, "a repeated Message-ID made a new article")
        for reply in (same, other):
            self.assertTrue(reply.startswith("4") or "already" in reply.lower(), reply)
            self.assertGreater(len(reply), 4, "no reason after the code: " + reply)
        talk.quit()
        talk.record()
        self.saw("the same article again -> %s; another article under the same id -> %s; "
                 "the group count stayed %s" % (same, other, after))

    def test_b17_sasl_authentication(self):
        """specs/nntp.md NNT-056: "fn offers three mechanisms" and
        "CAPABILITIES lists AUTHINFO USER SASL ... and SASL with the offered
        mechanisms"; docs/implementation.md: "AUTHINFO SASL offers
        SCRAM-SHA-256 (and -PLUS over TLS 1.3) and PLAIN over TLS".  PLAIN
        (RFC 4616) is what a stranger can drive with `openssl base64`: with
        an initial response, and as RFC 4643 section 2.4's empty challenge
        `383 =` answered on the next line.  SCRAM's proof needs a client
        that computes HMACs, so here it is checked as offered;
        tests/test_native_sasl.py runs its exchange."""
        def plain(user, password):
            out = subprocess.run(["openssl", "base64", "-A"], check=True,
                                 input=b"\0" + user.encode() + b"\0" + password.encode(),
                                 capture_output=True).stdout
            return out.decode("ascii").strip()

        talk = self.tls()
        talk.expect("200", "201")
        _, caps = talk.multiline("CAPABILITIES", "101")
        self.saw("CAPABILITIES over TLS: %s" % caps)
        self.assertIn("USER", next(c for c in caps if c.startswith("AUTHINFO ")).split())
        self.assertIn("SASL", next(c for c in caps if c.startswith("AUTHINFO ")).split())
        sasl = [c.split()[1:] for c in caps if c.startswith("SASL ")]
        self.assertEqual(len(sasl), 1, "one SASL line: %s" % caps)
        self.assertTrue({"SCRAM-SHA-256", "PLAIN"} <= set(sasl[0]), sasl)
        wrong = talk.command("AUTHINFO SASL PLAIN " + plain("wren", "not-" + PASSWORD), "481")
        self.saw("AUTHINFO SASL PLAIN <wrong password> -> " + wrong)
        right = talk.command("AUTHINFO SASL PLAIN " + plain("wren", PASSWORD), "281")
        self.saw("AUTHINFO SASL PLAIN <initial response> -> " + right)
        talk.quit()
        talk.record()

        talk = self.tls()
        talk.expect("200", "201")
        challenge = talk.command("AUTHINFO SASL PLAIN", "383")
        self.assertEqual(challenge, "383 =")
        done = talk.command(plain("wren", PASSWORD), "281")
        self.saw("AUTHINFO SASL PLAIN -> %s; <response> -> %s" % (challenge, done))
        talk.quit()
        talk.record()

    def test_b18_compression(self):
        """specs/nntp.md "Compression: COMPRESS (NNT-054, NNT-055)": RFC 8054
        COMPRESS DEFLATE after login; after the 206 every octet in both
        directions is one raw DEFLATE stream (section 2.2.2).  The stranger's
        side is Python's zlib (raw DEFLATE, wbits -15, a sync flush) over
        openssl s_client; the node's QUIT closes, so the tool's output ends."""
        talk = self.reader()
        _, caps = talk.multiline("CAPABILITIES", "101")
        self.assertIn("COMPRESS DEFLATE", caps)
        self.assertEqual(talk.command("COMPRESS SHRINK", "503")[:3], "503")
        started = talk.command("COMPRESS DEFLATE", "206")
        out = zlib.compressobj(6, zlib.DEFLATED, -15)
        talk.process.stdin.write(out.compress(b"DATE\r\nCAPABILITIES\r\nQUIT\r\n")
                                 + out.flush(zlib.Z_SYNC_FLUSH))
        talk.process.stdin.flush()
        talk.transcript += ["<DATE, CAPABILITIES, QUIT compressed>"]
        raw = b""
        while True:
            try:
                piece = talk.lines.get(timeout=talk.timeout)
            except queue.Empty:
                raise AssertionError("no compressed reply within %s s" % talk.timeout)
            if piece is None:
                break
            raw += piece
        replies = zlib.decompressobj(-15).decompress(raw).split(b"\r\n")
        self.assertTrue(replies[0].startswith(b"111 "), replies[:3])
        self.assertTrue(replies[1].startswith(b"101 "), replies[:3])
        listed = replies[2:replies.index(b".")]
        self.assertIn(b"READER", listed)
        self.assertNotIn(b"COMPRESS DEFLATE", listed)
        self.assertTrue(replies[replies.index(b".") + 1].startswith(b"205 "), replies)
        talk.close()
        talk.record()
        self.saw("COMPRESS DEFLATE -> %s; compressed DATE -> %s; QUIT -> %s" % (
            started, replies[0].decode(), replies[replies.index(b".") + 1].decode()))

    # ---- both faces are one node ---------------------------------------------

    def test_c01_the_web_made_account_logs_in_with_a_newsreader(self):
        """docs/web.md: "The same name and password work in a newsreader like
        tin, too."  docs/articles/fn-faq-11.txt: "The same name and password
        work in tin."."""
        talk = self.tls()
        talk.expect("200", "201")
        reply = self.login(talk, "wren")
        self.assertTrue(reply.startswith("281"), reply)
        talk.quit()
        talk.record()
        self.saw("AUTHINFO USER wren / PASS (the password chosen on /redeem) -> " + reply)

    def test_c02_the_nntp_redeemed_account_signs_in_on_the_web(self):
        """docs/reader.md: "They redeem the code once, on the Make your account
        page, or with fn redeem ... and then sign in."  (The XREDEEM account
        of test_b14 at the web face.)"""
        web = self.face(jar=self.jar("robin"))
        reply = self.sign_in(web, "robin", self.state["robin"])
        self.assertEqual((reply.status, reply.header("location")), (303, "/"), reply)
        self.assertIn("<span>robin</span>", web("/").body)
        self.saw("POST /signin robin -> 303 /, signed in")

    def test_c03_a_post_made_over_nntp_is_on_the_page(self):
        """docs/web.md: "the page shows only what the node answered on that
        friend's own connection" (the same store: a newsreader's post is on
        the page, at the page's number)."""
        web = self.face(jar=self.state["wren_jar"])
        post = web("/a?g=local.general&n=" + self.state["nntp_number"])
        self.assertEqual(post.status, 200, post)
        self.assertIn("A stranger posts over nc-less TLS", post.body)
        self.assertIn("First line.", post.body)
        self.saw("GET /a?g=local.general&n=%s (the NNTP post's number) -> 200 with its subject and body"
                 % self.state["nntp_number"])

    def test_c04_older_posts(self):
        """docs/reader.md: "The newest posts are listed; older posts shows
        more."  (101 posts over one NNTP connection into local.test; the page
        window is 100.)"""
        talk = self.reader()
        for i in range(101):
            reply = talk.post(article_octets("<outside-in-many-%d@stranger.invalid>" % i, "local.test",
                                             "many %03d" % i, "n", "wren <wren@friends.invalid>"))
            self.assertTrue(reply.startswith("240"), (i, reply))
        talk.quit()
        self.ran(talk.argv, ["AUTHINFO ...", "POST x 101 (240 each)", "QUIT"])
        web = self.face(jar=self.state["wren_jar"])
        page = web("/g?name=local.test")
        self.assertEqual(page.status, 200, page)
        self.assertIn("many 100", page.body)
        self.assertNotIn(">many 000<", page.body)
        link = re.search(r"href='(/g\?name=local.test&amp;before=[^']+)'>older posts", page.body)
        self.assertIsNotNone(link, page.body[-600:])
        older = web(html.unescape(link.group(1)))
        self.assertEqual(older.status, 200, older)
        self.assertIn(">many 000<", older.body)
        self.saw("101 posts: /g?name=local.test shows the newest 100 and an 'older posts' link; "
                 "following it shows the first")

    def test_h01_the_operators_health_line_per_state(self):
        """docs/operator.md: `fn operator CONFIG health`: "one line for each
        possible problem, then accepted operator health" ... "clear means
        fine. held means a problem." (The operator's own binary, not a stock
        tool: recorded as the operator's side of the same node.  There is no
        HTTP health route, test_a15.)"""
        result = self.node.operator("health", timeout=240)
        out = result.stdout.decode("utf-8", "replace")
        err = result.stderr.decode("utf-8", "replace")
        self.ran(["fn", "operator", "fn.toml", "health"])
        self.assertRegex(out, r"^health exit=\d+ state=\S+", out)
        states = re.findall(r"^([a-z-]+) (clear|held|unobserved)", out, re.M)
        self.assertGreaterEqual(len(states), 8, out)
        where = ("stdout" if "accepted operator health" in out else
                 "stderr" if "accepted operator health" in err else "NOT PRINTED")
        self.saw("exit %d; %s; 'accepted operator health' on %s" % (
            result.returncode, ", ".join("%s %s" % s for s in states), where))
        self.assertNotEqual(where, "NOT PRINTED",
                            "docs/operator.md shows the command ending with 'accepted operator health'; "
                            "the binary printed neither on stdout nor stderr")

    # ---- last: things that disturb the node ------------------------------------

    def test_z01_too_many_tries_from_one_address(self):
        """docs/web.md: '"Too many tries from here just now." Someone typed a
        wrong password many times from that address.'  docs/operator.md:
        exposure-auth-failures, "how many failed logins per address per
        minute"; "You can change each limit while it runs"."""
        self.node.operator("policy", "set", "exposure-auth-failures", "3", expect=EXIT.OK, timeout=240)
        self.ran(["fn", "operator", "fn.toml", "policy", "set", "exposure-auth-failures", "3"])
        web = self.face(jar=self.jar("guesser"))
        statuses = []
        for _ in range(6):
            reply = self.sign_in(web, "alice", "guess-%d" % len(statuses))
            statuses.append(reply.status)
            if reply.status == 429:
                self.assertIn("Too many tries from here just now", reply.body)
                break
        self.assertIn(429, statuses, statuses)
        talk = self.plain()
        try:
            first = talk.line()
        except AssertionError as closed:
            first = "closed without a greeting (%s)" % str(closed)[:60]
        talk.record()
        talk.close()
        self.saw("sign-in statuses %s (429 = the page); the next plain NNTP connection: %s"
                 % (statuses, first))

    def test_z02_a_restart_ends_sessions_and_keeps_posts(self):
        """docs/web.md: a session "ends ... when the node restarts".
        docs/public-node.md: "The node may be restarted or upgraded; your
        posts are kept across both."."""
        self.node.stop()
        self.node.start(timeout=240)
        web = self.face(jar=self.state["wren_jar"])
        after = web("/")
        self.assertEqual((after.status, after.header("location")), (303, "/signin"), after)
        talk = self.reader()
        kept = talk.command("STAT " + self.state["nntp_mid"], "223")
        many = talk.command("GROUP local.test", "211")
        self.assertEqual(many.split()[1], "101", many)
        talk.quit()
        talk.record()
        self.saw("after restart: GET / with the old cookie -> 303 /signin; STAT %s; GROUP local.test %s"
                 % (kept, many))


# -----------------------------------------------------------------------------

@requires(IMAGE)
class ProxiedFaceTests(NodeCase):
    """The documented Caddy setup: `[web] proxied = true`, plain HTTP on
    loopback (curl plays Caddy); a short idle life and one session."""

    @classmethod
    def setUpClass(cls):
        cls.start_node("proxied", web_extra="proxied = true\nidle_seconds = 2\nmax_sessions = 1\n")

    def face(self, jar=None, extra=()):
        return Curl(self, "http://127.0.0.1:%d" % self.web_port, jar=jar, extra=extra)

    def test_p01_sign_in_through_the_proxy(self):
        """docs/web.md: "With proxied = true the node takes the browser's
        address from the last X-Forwarded-For Caddy adds, and only when the
        request comes from this machine."  specs/human-client.md WEB-005:
        cookies are Secure behind the profile's TLS proxy."""
        web = self.face(jar=self.jar("via-caddy"), extra=["-H", "X-Forwarded-For: 203.0.113.9"])
        reply = self.sign_in(web, "alice")
        self.assertEqual((reply.status, reply.header("location")), (303, "/"), reply)
        session = [c for c in reply.cookies if c.startswith("fnr_session=")]
        self.assertIn("Secure", session[0])
        self.assertIn("HttpOnly", session[0])
        home = web("/")
        self.assertEqual(home.status, 200, home)
        out = web("/signout", data={"csrf": home.form_value("csrf")})
        self.assertEqual(out.status, 303, out)
        self.saw("POST /signin with X-Forwarded-For -> 303 /; cookie %s; signed out"
                 % session[0].split(";", 1)[1].strip())

    def test_p02_a_session_ends_after_idle_seconds(self):
        """docs/web.md: "idle_seconds = 43200: how long a signed-in page stays
        signed in without use" (here 2 seconds)."""
        web = self.face(jar=self.jar("idle"), extra=["-H", "X-Forwarded-For: 203.0.113.10"])
        self.assertEqual(self.sign_in(web, "alice").status, 303)
        self.assertEqual(web("/").status, 200)
        time.sleep(3)
        expired = web("/")
        self.assertEqual((expired.status, expired.header("location")), (303, "/signin"), expired)
        self.saw("signed in, GET / 200; 3 s later GET / -> 303 /signin")

    def test_p03_max_sessions(self):
        """docs/web.md: "max_sessions = 64: how many people can be signed in at
        once" (here 1: the second sign-in is told to try later)."""
        one = self.face(jar=self.jar("one"), extra=["-H", "X-Forwarded-For: 203.0.113.11"])
        self.assertEqual(self.sign_in(one, "alice").status, 303)
        two = self.face(jar=self.jar("two"), extra=["-H", "X-Forwarded-For: 203.0.113.12"])
        reply = self.sign_in(two, "alice")
        self.assertEqual(reply.status, 503, reply)
        self.assertIn("Too many people are signed in just now", reply.body)
        self.saw("first sign-in 303; the second while it lives: 503 \"Too many people are signed in\"")


@requires(IMAGE)
class UnprotectedFaceTests(NodeCase):
    """The face reached over plain HTTP from another address: bound for the
    life of this class on the box's own non-loopback address (no TLS, no
    proxy), which is the only way a stranger on this machine can be a
    non-loopback peer."""

    @classmethod
    def setUpClass(cls):
        addresses = subprocess.run(["hostname", "-I"], capture_output=True, text=True).stdout.split()
        v4 = [a for a in addresses if re.match(r"^\d+\.\d+\.\d+\.\d+$", a)]
        # A bridge or private address before the LAN one: the face is bound
        # there only for this class's life, logins required.
        cls.address = next((a for a in v4 if a.startswith("172.")), v4[0] if v4 else None)
        if cls.address is None:
            raise unittest.SkipTest("no non-loopback IPv4 address on this machine (hostname -I)")
        cls.start_node("unprotected", web_extra="", web_host=cls.address)

    def face(self, jar=None, extra=()):
        return Curl(self, "http://%s:%d" % (self.address, self.web_port), jar=jar, extra=extra)

    def test_u01_signing_in_needs_a_protected_connection(self):
        """docs/web.md: '"Signing in needs a protected connection". The page was
        opened with http://, not through Caddy. Use https://.'"""
        web = self.face(jar=self.jar("plain"))
        page = web("/signin")
        self.assertEqual(page.status, 200, page)
        reply = self.sign_in(web, "alice")
        self.assertEqual(reply.status, 403, reply)
        self.assertIn("Signing in needs a protected connection", reply.body)
        self.assertNotIn("fnr_session=", " ".join(reply.cookies))
        self.saw("http://%s:%d/signin -> 200; POST /signin -> 403 \"Signing in needs a protected connection\""
                 % (self.address, self.web_port))


@requires(IMAGE)
class ListenerAddressTests(Recorded):
    """docs/operator.md: `[listener] host` "takes one or more addresses, comma
    separated, IPv4 or IPv6 ([::1], 192.0.2.7), or localhost"; docs/web.md:
    "the [web] table is refused: port-taken"."""

    @classmethod
    def setUpClass(cls):
        node = cls.node = Node(class_case(cls), IMAGE, name="addresses", listener=False)
        cls.port, cls.web_port = free_port(), free_port()
        node.write_config(listener=False, extra=(
            '[listener]\nhost = "::1"\nport = {}\n\n[auth]\nrequired = false\n'.format(cls.port)))
        node.init("local.general", timeout=240)
        cls.scratch = node.root / "stranger"
        cls.scratch.mkdir(exist_ok=True)

    def test_l01_an_ipv6_listener(self):
        """docs/operator.md: `[listener] host` takes "IPv4 or IPv6 ([::1], ...)".
        docs/agents.md: "For an IPv6 address, use brackets: [::1]:1119"."""
        self.node.start(timeout=240)
        talk = Talk(self, ["nc", "-6", "-w", "60", "::1", str(self.port)])
        greeting = talk.expect("200", "201")
        _, caps = talk.multiline("CAPABILITIES", "101")
        self.assertIn("VERSION 2", caps)
        talk.quit()
        talk.record()
        self.node.stop()
        self.saw("nc -6 ::1 %d: greeting %s; CAPABILITIES 101" % (self.port, greeting))

    def test_l02_a_web_port_the_newsreader_port_uses_is_refused(self):
        """docs/web.md: "If it does not accept the [web] table, it does not
        start, and says why (for example the [web] table is refused:
        port-taken when port is one the node's newsreader ports already
        use)."."""
        self.node.write_config(listener=False, extra=(
            '[listener]\nhost = "127.0.0.1"\nport = {0}\n\n[auth]\nrequired = false\n\n'
            '[web]\nport = {0}\n'.format(self.port)))
        process, stderr = self.node.try_start(timeout=240)
        self.assertIsNotNone(stderr, "the node started with the web port equal to the listener port")
        self.assertIn("port-taken", stderr)
        self.ran(["fn", "operator", "fn.toml", "run"])
        self.saw("exit %s: %s" % (process.returncode, stderr.strip().splitlines()[-1][:120]))


# -----------------------------------------------------------------------------

@unittest.skipUnless(LIVE, "FN_OUTSIDE_IN_LIVE=1 runs the read-only checks against " + PUBLIC_NODE)
class PublicNodeTests(Recorded):
    """docs/public-node.md, read-only, from wherever this runs: the public
    certificate, both ports, no anonymous reading.  Never AUTHINFO with a
    credential, never POST, never XREDEEM."""

    def talk(self, port, starttls=False):
        argv = ["openssl", "s_client", "-quiet", "-connect", "%s:%d" % (PUBLIC_NODE, port),
                "-verify_return_error", "-verify_hostname", PUBLIC_NODE, "-servername", PUBLIC_NODE]
        if starttls:
            argv += ["-starttls", "nntp"]
        return Talk(self, argv, timeout=90)

    def test_v01_port_563_with_a_public_certificate(self):
        """docs/public-node.md: "Port 563: encrypted from the first byte
        (NNTPS)"; "The certificate is a normal public one (Let's Encrypt), so
        you do not need a certificate file"; "There is no anonymous reading:
        you need a login even to look."."""
        talk = self.talk(563)
        greeting = talk.expect("200", "201")
        _, caps = talk.multiline("CAPABILITIES", "101")
        self.assertIn("VERSION 2", caps)
        self.assertTrue(any(c.startswith("AUTHINFO") for c in caps), caps)
        refused = talk.command("GROUP fn.announce", "480")
        listing = talk.command("LIST", "480")
        talk.quit()
        talk.record()
        self.saw("%s; CAPABILITIES %s; GROUP fn.announce %s; LIST %s" % (greeting, caps, refused, listing))

    def test_v02_port_119_with_starttls(self):
        """docs/public-node.md: "Port 119: starts plain and switches to
        encryption with STARTTLS."  docs/articles/fn-faq-2.txt: "A login
        before TLS is refused."."""
        plain = Talk(self, ["nc", "-w", "60", PUBLIC_NODE, "119"], timeout=90)
        greeting = plain.expect("200", "201")
        _, caps = plain.multiline("CAPABILITIES", "101")
        self.assertIn("STARTTLS", caps)
        before = plain.command("AUTHINFO USER nobody", "483", "480", "502")
        plain.quit()
        plain.record()
        talk = self.talk(119, starttls=True)
        _, after = talk.multiline("CAPABILITIES", "101")
        self.assertNotIn("STARTTLS", after)
        self.assertTrue(any(c.startswith("AUTHINFO USER") for c in after), after)
        talk.quit()
        talk.record()
        self.saw("%s; STARTTLS offered; AUTHINFO before TLS %s; after -starttls nntp: %s" % (greeting, before, after))

    def test_v03_help_lists_the_documented_commands(self):
        """docs/articles/fn-faq-2.txt's command list (generated from
        books/protocol-table.lisp) on the public node's HELP."""
        talk = self.talk(563)
        talk.expect("200", "201")
        _, help_lines = talk.multiline("HELP", "100")
        listed = set(" ".join(help_lines).split())
        missing = [c for c in FAQ2_COMMANDS if c not in listed]
        talk.quit()
        talk.record()
        self.assertEqual(missing, [], help_lines)
        self.saw("HELP names all %d" % len(FAQ2_COMMANDS))


if __name__ == "__main__":
    unittest.main()
