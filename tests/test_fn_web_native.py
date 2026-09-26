"""The loopback web client against a scratch native writable fn owner.

Set FN_NATIVE_DEVELOPER_HOST to a frozen developer image and FN_NATIVE_TEST_ROOT
to its source snapshot. This test creates and removes only its own Store.
The web client is a separate Python process; the second fixture exercises its
current source against the pinned native image's existing NNTP and modelled
post-publication death cut, without rebuilding the native image.
"""
import html
import http.client
import json
import os
from pathlib import Path
import re
import select
import socket
import subprocess
import sys
import tempfile
import threading
import unittest
from types import SimpleNamespace
from urllib.parse import urlencode

from tests.native_process import wait_for_announcement, stop_and_diagnostics

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import fn_web  # noqa: E402
import fn_verify  # noqa: E402

IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", "/nonexistent/fn-host-developer"))
ROOT = Path(os.environ.get("FN_NATIVE_TEST_ROOT", Path(__file__).resolve().parents[1]))


@unittest.skipUnless(os.access(IMAGE, os.X_OK), "frozen native developer image required")
class NativeWebClientTests(unittest.TestCase):
    def test_web_post_and_thread_read_use_the_native_owner(self):
        with tempfile.TemporaryDirectory(prefix="fn-web-native-") as temporary:
            store = Path(temporary) / "store"
            initialized = subprocess.run(
                [str(IMAGE), "--fn", "store", str(store), "init", "fn.agents"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=120, check=False)
            self.assertEqual(initialized.returncode, 0,
                             initialized.stderr.decode(errors="replace"))
            owner = subprocess.Popen(
                [str(IMAGE), "--fn", "owner", "run", str(store), "0", "0", "8"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            server = thread = None
            try:
                ready = select.select([owner.stdout], [], [], 120)[0]
                self.assertTrue(ready, "native owner did not announce a port")
                line = owner.stdout.readline()
                self.assertTrue(line.startswith(b"LISTENING "),
                                line)
                nntp_port = int(line.split()[1])
                args = SimpleNamespace(host="127.0.0.1", port=nntp_port,
                                       timeout=15.0, plain=True, cafile=None)
                server = fn_web.WebServer(0, fn_web.Backend(args, "", ""))
                thread = threading.Thread(target=server.serve_forever, daemon=True)
                thread.start()

                def request(method, path, data=None, subject="Native web post",
                            body_text="Native owner body <visible>"):
                    conn = http.client.HTTPConnection("127.0.0.1",
                                                      server.server_port, timeout=30)
                    headers = {}
                    if method == "POST":
                        compose_status, compose_page = request("GET", "/compose?group=fn.agents")
                        self.assertEqual(compose_status, 200)
                        token = re.search(r"name='submission_id' value='([^']+)'", compose_page).group(1)
                        headers["Content-Type"] = "application/x-www-form-urlencoded"
                        headers["Origin"] = "http://127.0.0.1:%d" % server.server_port
                        data = urlencode({"csrf": server.token, "submission_id": token,
                                          "group": "fn.agents",
                                          "subject": subject, "sender": "Human <h@local.invalid>",
                                          "references": "", "body": body_text})
                    conn.request(method, path, body=data, headers=headers)
                    result = conn.getresponse()
                    answer = result.status, result.read().decode("utf-8")
                    location = result.getheader("Location")
                    conn.close()
                    if answer[0] == 303:
                        return request("GET", location)
                    return answer

                status, page = request("GET", "/")
                self.assertEqual(status, 200)
                self.assertIn("fn.agents", page)
                status, page = request("POST", "/post", subject="Native web first",
                                       body_text="First native owner body <visible>")
                self.assertEqual(status, 200)
                self.assertIn("<span class='badge accepted'>accepted</span>", page)
                status, page = request("POST", "/post", subject="Native web second",
                                       body_text="Second native owner body")
                self.assertEqual(status, 200)
                self.assertIn("<span class='badge accepted'>accepted</span>", page)

                status, page = request(
                    "GET", "/g?name=fn.agents&start=1&end=1")
                self.assertEqual(status, 200)
                self.assertIn("Native web first", page)
                self.assertNotIn("Native web second", page)
                self.assertNotIn("rel='prev'", page)
                self.assertIn("start=2&amp;end=41", page)

                status, page = request(
                    "GET", "/g?name=fn.agents&start=2&end=2")
                self.assertEqual(status, 200)
                self.assertIn("Native web second", page)
                self.assertNotIn("Native web first", page)
                self.assertIn("start=1&amp;end=1", page)
                self.assertNotIn("rel='next'", page)

                status, page = request("GET", "/a?group=fn.agents&number=1")
                self.assertEqual(status, 200)
                self.assertIn("First native owner body &lt;visible&gt;", page)
                self.assertIn("Viewing does not acknowledge application processing", page)
            finally:
                if server is not None:
                    server.shutdown()
                    server.server_close()
                if thread is not None:
                    thread.join(5)
                owner.terminate()
                try:
                    owner.communicate(timeout=30)
                except subprocess.TimeoutExpired:
                    owner.kill()
                    owner.communicate(timeout=30)

    def test_durable_draft_lost_post_reply_and_restart_keep_one_native_article(self):
        with tempfile.TemporaryDirectory(prefix="fn-web-outbox-native-") as temporary:
            base = Path(temporary)
            store, outbox = base / "store", base / "outbox"
            environment = dict(os.environ)
            environment["ACL2_CUSTOMIZATION"] = "NONE"
            environment.pop("ACL2_SYSTEM_BOOKS", None)
            environment.pop("FN_NATIVE_POST_FAULT", None)
            initialized = subprocess.run(
                [str(IMAGE), "--fn", "store", str(store), "init", "fn.agents"],
                cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, timeout=120, check=False)
            self.assertEqual(initialized.returncode, 0,
                             initialized.stderr.decode(errors="replace"))
            with socket.socket() as probe:
                probe.bind(("127.0.0.1", 0))
                port = probe.getsockname()[1]
            args = SimpleNamespace(host="127.0.0.1", port=port,
                                   timeout=15.0, plain=True, cafile=None)
            backend = fn_web.Backend(args, "", "")
            owner = server = thread = None

            def start_owner(fault=False):
                env = dict(environment)
                if fault:
                    env["FN_NATIVE_POST_FAULT"] = "record-attempted:kill"
                process = subprocess.Popen(
                    [str(IMAGE), "--fn", "owner", "run", str(store),
                     str(port), "0", "8"], cwd=ROOT, env=env,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                line = wait_for_announcement(process, b"LISTENING ", timeout=120)
                self.assertEqual(int(line.split()[1]), port)
                return process

            def start_web():
                web = fn_web.WebServer(0, backend, outbox)
                worker = threading.Thread(target=web.serve_forever, daemon=True)
                worker.start()
                return web, worker

            def request(method, path, fields=None):
                conn = http.client.HTTPConnection("127.0.0.1", server.server_port,
                                                  timeout=45)
                headers = {}
                payload = None
                if method == "POST":
                    headers = {"Content-Type": "application/x-www-form-urlencoded",
                               "Origin": "http://127.0.0.1:%d" % server.server_port}
                    payload = urlencode({"csrf": server.token, "group": "fn.agents",
                                         "subject": "Native durable draft",
                                         "sender": "Human <h@local.invalid>",
                                         "references": "", "body": "saved draft"} | fields)
                conn.request(method, path, body=payload, headers=headers)
                reply = conn.getresponse()
                answer = reply.status, dict(reply.getheaders()), reply.read().decode("utf-8")
                conn.close()
                if method == "GET" and path.startswith("/compose") and answer[0] == 303:
                    return request("GET", answer[1]["Location"])
                return answer

            def restart_web():
                nonlocal server, thread
                server.shutdown()
                server.server_close()
                thread.join(5)
                server, thread = start_web()

            try:
                owner = start_owner(fault=True)
                server, thread = start_web()
                composed = request("GET", "/compose?group=fn.agents")
                self.assertEqual(composed[0], 200)
                token = re.search(r"name='submission_id' value='([^']+)'",
                                  composed[2]).group(1)
                saved = request("POST", "/post", {"submission_id": token,
                    "action": "save", "subject": "", "body": "rough draft"})
                self.assertEqual(saved[0], 303)
                self.assertEqual(list((store / "transactions").glob("*.txn")), [])
                restart_web()
                self.assertIn("rough draft", request("GET", "/draft?id=" + token)[2])
                final_body = "native final source survives a lost reply"
                posted = request("POST", "/post", {"submission_id": token,
                    "action": "post", "subject": "Native final", "body": final_body})
                self.assertEqual(posted[0], 303)
                result = request("GET", posted[1]["Location"])
                self.assertIn("badge uncertain", result[2])
                # Uncertain stays its own outcome: the exact text is kept on
                # the page, reposting is warned against, and no edit path
                # can turn it into a second article.
                self.assertIn("Do not write this again as a new post", result[2])
                self.assertIn(final_body, result[2])
                self.assertNotIn("Edit as a new post", result[2])
                self.assertEqual(request("GET", "/compose?group=fn.agents&edit=" + token)[0],
                                 400)
                self.assertEqual(owner.wait(timeout=30), -9,
                                 stop_and_diagnostics(owner, timeout=1))
                owner.stdout.close()
                owner.stderr.close()
                owner = None
                saved_record = json.loads((outbox / (token + ".json")).read_text())
                self.assertEqual(saved_record["result"]["word"], "uncertain")
                msgid = saved_record["message_id"]
                source = subprocess.run(
                    [str(IMAGE), "--fn", "store", str(store), "inspect", msgid],
                    cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, timeout=60, check=False)
                self.assertEqual(source.returncode, 0,
                                 source.stderr.decode(errors="replace"))
                exact_article = ("\r\n".join(saved_record["lines"]) + "\r\n").encode()
                self.assertTrue(source.stdout.endswith(exact_article))
                self.assertIn(final_body.encode(), source.stdout)
                before_files = {p.name: p.read_bytes()
                                for p in (store / "transactions").glob("*.txn")}
                self.assertEqual(len(before_files), 1)

                owner = start_owner()
                restart_web()
                self.assertIn("badge uncertain", request("GET", "/result?id=" + token)[2])
                observed = request("GET", request(
                    "POST", "/settle", {"submission_id": token})[1]["Location"])
                self.assertIn("now serves this Message-ID", observed[2])
                self.assertIn("badge uncertain", observed[2])
                duplicate = request("POST", "/post", {"submission_id": token,
                    "action": "post", "subject": "Another article", "body": "do not send"})
                self.assertEqual(duplicate[0], 303)
                self.assertEqual({p.name: p.read_bytes()
                                  for p in (store / "transactions").glob("*.txn")},
                                 before_files)
                restart_web()
                self.assertIn("now serves this Message-ID",
                              request("GET", "/result?id=" + token)[2])
                self.assertIn("badge uncertain", request("GET", "/result?id=" + token)[2])
            finally:
                if server is not None:
                    server.shutdown()
                    server.server_close()
                if thread is not None:
                    thread.join(5)
                if owner is not None:
                    stop_and_diagnostics(owner, timeout=30)
                    owner.stdout.close()
                    owner.stderr.close()


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


@unittest.skipUnless(os.access(IMAGE, os.X_OK), "frozen native developer image required")
class NativeProtectedWebClientTests(unittest.TestCase):
    """The web client against a native owner with STARTTLS, [auth] required and
    protected_only, which is the deployed node's policy: every page is one
    verified TLS connection and one AUTHINFO login, and every outcome shown is
    the node's."""

    USER, SECRET = "ember-test", "web-client-secret-7"

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fn-web-protected-")
        root = cls.root = Path(cls.temporary.name)
        cls.store, cls.auth, cls.config = root / "store", root / "credentials.toml", root / "fn.toml"
        cls.port = free_loopback_port()
        env = native_environment()
        done = subprocess.run([str(IMAGE), "--fn", "store", str(cls.store), "init", "fn.agents"],
                              cwd=ROOT, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=180, check=False)
        assert done.returncode == 0, done.stderr.decode(errors="replace")
        cls.cert, key = root / "cert.pem", root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                        "-out", str(cls.cert), "-sha256", "-days", "1", "-nodes",
                        "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=60, check=True)
        cls.other_cert = root / "other.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048",
                        "-keyout", str(root / "other-key.pem"), "-out", str(cls.other_cert),
                        "-sha256", "-days", "1", "-nodes", "-subj", "/CN=other",
                        "-addext", "subjectAltName=IP:127.0.0.1"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=60, check=True)
        cls.config.write_text(
            '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n\n[auth]\nrequired = true\n'
            'protected_only = true\npath = "{}"\n'.format(
                cls.store, cls.port, cls.cert, key, cls.auth), encoding="ascii")
        enrolled = subprocess.run(
            [sys.executable, "bin/fn", "--config", str(cls.config), "principal",
             "set-password", cls.USER, "--password", cls.SECRET, "--posting"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=600, check=False)
        assert enrolled.returncode == 0, enrolled.stderr.decode(errors="replace")
        cls.owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(cls.config), "run"],
                                     cwd=ROOT, env=env, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE)
        line = wait_for_announcement(cls.owner, b"LISTENING ")
        assert line == "LISTENING {}\n".format(cls.port).encode(), line

    @classmethod
    def tearDownClass(cls):
        stop_and_diagnostics(cls.owner, timeout=30)
        cls.owner.stdout.close()
        cls.owner.stderr.close()
        cls.temporary.cleanup()

    def backend(self, secret=None, cert=None):
        args = SimpleNamespace(host="127.0.0.1", port=self.port, timeout=30.0,
                               plain=False, cafile=str(cert or self.cert))
        return fn_web.Backend(args, self.USER, secret or self.SECRET)

    def start_web(self, marks_path=None):
        backend = self.backend()
        marks = fn_web.ReadMarks(marks_path, backend.node, self.USER)
        server = fn_web.WebServer(0, backend, None, marks)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(thread.join, 5)
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        return server

    def http(self, server, method, path, fields=None, follow=True):
        conn = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=60)
        headers, payload = {}, None
        if method == "POST":
            headers = {"Content-Type": "application/x-www-form-urlencoded",
                       "Origin": "http://127.0.0.1:%d" % server.server_port}
            payload = urlencode(dict({"csrf": server.token}, **(fields or {})))
        conn.request(method, path, body=payload, headers=headers)
        reply = conn.getresponse()
        answer = reply.status, reply.getheader("Location"), reply.read().decode("utf-8")
        conn.close()
        self.assertNotIn(self.SECRET, answer[2])
        if follow and answer[0] == 303:
            return self.http(server, "GET", answer[1])
        return answer

    def post(self, server, subject, body, reply=None, sender="Tester <t@local.invalid>"):
        form = self.http(server, "GET", "/compose?group=fn.agents" +
                         ("&reply=%d" % reply if reply else ""))
        self.assertEqual(form[0], 200, form[2])
        token = re.search(r"name='submission_id' value='([^']+)'", form[2]).group(1)
        references = re.search(r"name='references' value='([^']*)'", form[2]).group(1)
        shown_subject = re.search(r"name='subject' maxlength='240' required value='([^']*)'",
                                  form[2]).group(1)
        answer = self.http(server, "POST", "/post", {
            "submission_id": token, "group": "fn.agents", "action": "post",
            "subject": subject if subject is not None else html_unescape(shown_subject),
            "sender": sender, "references": html_unescape(references), "body": body})
        return token, html_unescape(references), html_unescape(shown_subject), answer

    def nntp_article(self, number):
        result = self.backend().article("fn.agents", number)
        self.assertEqual(result.word, "done", result.detail)
        return result.data["articles"][0]

    def test_login_over_tls_is_the_nodes_answer_and_the_command_line_exits_by_it(self):
        checked = self.backend().login_check()
        self.assertEqual(checked.word, "done", checked.detail)
        self.assertTrue(checked.data["tls"]["version"].startswith("TLSv1."))
        wrong = self.backend(secret="not-the-secret").login_check()
        self.assertEqual(wrong.word, "refused")
        self.assertTrue(wrong.detail.startswith("481"), wrong.detail)
        pinned = self.backend(cert=self.other_cert).login_check()
        self.assertEqual(pinned.word, "refused")
        self.assertIn("did not verify", pinned.detail)

        tool = Path(__file__).resolve().parents[1] / "tools" / "fn_web.py"
        base = [sys.executable, str(tool), "--node", "127.0.0.1:%d" % self.port,
                "--tls-cert", str(self.cert), "--user", self.USER, "--port", "0",
                "--no-marks"]
        env = dict(os.environ, FN_CLIENT_PASSWORD="not-the-secret")
        bad = subprocess.run(base, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, timeout=120, check=False)
        self.assertEqual(bad.returncode, 1, bad.stderr)
        self.assertIn(b"refused 481", bad.stderr)
        self.assertNotIn(b"not-the-secret", bad.stdout + bad.stderr)
        unreachable = subprocess.run(
            base[:3] + ["127.0.0.1:%d" % free_loopback_port()] + base[4:], env=env,
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=120, check=False)
        self.assertEqual(unreachable.returncode, 3, unreachable.stderr)
        no_password = subprocess.run(base, env={k: v for k, v in os.environ.items()
                                                if k != "FN_CLIENT_PASSWORD"},
                                     stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, timeout=60, check=False)
        self.assertEqual(no_password.returncode, 2, no_password.stderr)
        good = subprocess.Popen(base, env=dict(os.environ, FN_CLIENT_PASSWORD=self.SECRET),
                                stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
        try:
            ready = select.select([good.stdout], [], [], 120)[0]
            self.assertTrue(ready, "web client did not start")
            banner = good.stdout.readline().decode()
            if not banner:
                good.wait(timeout=30)
                self.fail("web client exited %s: %s" % (good.returncode,
                                                        good.stderr.read().decode()))
            self.assertIn(self.USER + " at 127.0.0.1:%d" % self.port, banner)
            self.assertIn("certificate verified", banner)
            self.assertIn("open http://127.0.0.1:", banner)
            page_port = int(re.search(r"http://127\.0\.0\.1:(\d+)/", banner).group(1))
            conn = http.client.HTTPConnection("127.0.0.1", page_port, timeout=60)
            conn.request("GET", "/")
            page = conn.getresponse().read().decode()
            conn.close()
            self.assertIn("fn.agents", page)
            self.assertNotIn(self.SECRET, page)
        finally:
            good.terminate()
            good.communicate(timeout=30)

    def test_thread_reply_outcomes_verdict_unread_and_resume(self):
        marks_path = self.root / "marks" / "web.json"
        server = self.start_web(marks_path)
        home = self.http(server, "GET", "/")
        self.assertIn(self.USER + " at 127.0.0.1:%d over TLS" % self.port, home[2])

        _, _, _, root_answer = self.post(server, "Thread root", "root body")
        self.assertIn("<span class='badge accepted'>accepted</span>", root_answer[2])
        self.assertIn("<p class='reason'>240", root_answer[2])
        root_number = int(self.backend().slot("fn.agents", 1).data["high"])
        root_article = self.nntp_article(root_number)
        _, _, _, other = self.post(server, "Unrelated", "not in the thread")
        self.assertIn("badge accepted", other[2])

        _, refs, subject, reply_answer = self.post(server, None, "first reply",
                                                   reply=root_number)
        self.assertEqual(subject, "Re: Thread root")
        self.assertEqual(refs, root_article["message_id"])
        self.assertIn("badge accepted", reply_answer[2])
        reply_number = root_number + 2
        reply_article = self.nntp_article(reply_number)
        _, refs2, subject2, deep = self.post(server, None, "second reply", reply=reply_number)
        self.assertEqual(subject2, "Re: Thread root")
        self.assertEqual(refs2, root_article["message_id"] + " " + reply_article["message_id"])
        self.assertIn("badge accepted", deep[2])
        stored = self.nntp_article(reply_number + 1)
        self.assertEqual(fn_client_first(stored["headers"], "references"), refs2)
        self.assertEqual(fn_client_first(stored["headers"], "subject"), "Re: Thread root")

        # Threaded view: root, its reply, the reply's reply, then the unrelated article.
        group = self.http(server, "GET", "/g?name=fn.agents")
        self.assertEqual(group[0], 200)
        # The article links (/a) in thread order; each reply also carries a
        # conversation link (/t, reader-daily), and the two unrelated roots
        # carry none.
        order = [int(n) for n in re.findall(r"href='/a\?[^']*number=(\d+)'>", group[2])]
        self.assertEqual(order, [root_number, reply_number, reply_number + 1, root_number + 1])
        conversations = [int(n) for n in re.findall(r"href='/t\?[^']*number=(\d+)'>conversation<",
                                                    group[2])]
        self.assertEqual(conversations, [reply_number, reply_number + 1])
        margins = [int(m) for m in re.findall(r"margin-left:(\d+)px", group[2])]
        self.assertEqual(margins, [0, 18, 36, 0])

        # Refused: the node's own 441 reason reaches the page, and only a
        # refused article may seed a new draft.
        token, _, _, refused = self.post(server, "Bad sender", "refused body",
                                         sender="not a mailbox")
        self.assertIn("<span class='badge refused'>refused</span>", refused[2])
        reason = re.search(r"<p class='reason'>([^<]*)</p>", refused[2]).group(1)
        self.assertTrue(reason.startswith("441"), reason)
        self.assertNotIn("uncertain", reason.lower())
        self.assertIn("Edit as a new post", refused[2])
        edit = self.http(server, "GET", "/compose?group=fn.agents&edit=" + token)
        self.assertEqual(edit[0], 200)
        self.assertIn("refused body", edit[2])
        self.assertNotEqual(token, re.search(r"name='submission_id' value='([^']+)'",
                                             edit[2]).group(1))
        self.assertEqual(self.backend().slot("fn.agents", 1).data["high"], reply_number + 1)

        # Verdict: unsigned posts carry the node's absent report, as a badge on
        # the article and on its row; nothing here upgrades it.
        article = self.http(server, "GET", "/a?group=fn.agents&number=%d" % root_number)
        self.assertEqual(article[0], 200)
        self.assertIn("<span class='badge absent'>node verdict: absent</span>", article[2])
        # The node's whole recorded verdict line, as its historical record
        # (reader-daily f1941527 moved it under this heading).
        self.assertIn("<dt>The node's historical verdict</dt><dd><span class='badge absent'>"
                      "absent</span> <code>absent: no-field</code>", article[2])
        group = self.http(server, "GET", "/g?name=fn.agents")
        self.assertIn("<span class='badge absent' title='absent: no-field'>absent</span>",
                      group[2])

        # Unread counts are this client's marks; opening one article reduced them.
        high = reply_number + 1
        home = self.http(server, "GET", "/")
        self.assertIn("%d unread" % (high - 1), home[2])
        self.assertEqual(group[2].count("class='unread-dot'"), high - 1)
        saved = json.loads(marks_path.read_text())
        self.assertEqual(saved["user"], self.USER)
        self.assertEqual(saved["groups"]["fn.agents"]["last"],
                         {"number": root_number, "message_id": root_article["message_id"]})

        # Resume from (group, number, Message-ID): the node is asked what the
        # number carries now; a mismatch is reported, never guessed around.
        self.assertIn("/resume?group=fn.agents&amp;number=%d" % root_number, article[2])
        moved = self.http(server, "GET", "/resume?" + urlencode(
            {"group": "fn.agents", "number": root_number, "id": root_article["message_id"]}),
            follow=False)
        self.assertEqual(moved[0], 303)
        self.assertEqual(moved[1], "/g?name=fn.agents&start=%d&end=%d"
                         % (root_number + 1, root_number + 40))
        wrong = self.http(server, "GET", "/resume?" + urlencode(
            {"group": "fn.agents", "number": root_number,
             "id": reply_article["message_id"]}))
        self.assertEqual(wrong[0], 409)
        self.assertIn("not the same article", wrong[2])
        self.assertIn("Now the node serves <code>" +
                      html.escape(root_article["message_id"]), wrong[2])
        last = self.http(server, "GET", "/resume?" + urlencode(
            {"group": "fn.agents", "number": high,
             "id": stored["message_id"]}))
        self.assertIn("Nothing newer", last[2])

        # The 409 page's lookup carries the group, and the node answers the
        # article's local number there (RFC 3977 section 6.2.1.2), so the
        # lookup is a resume point; without a group it has none.
        self.assertIn("/find?" + html.escape(urlencode(
            {"id": reply_article["message_id"], "group": "fn.agents"})), wrong[2])
        found = self.http(server, "GET", "/find?" + urlencode(
            {"id": reply_article["message_id"], "group": "fn.agents"}))
        self.assertEqual(found[0], 200)
        self.assertIn("Local #%d in fn.agents" % reply_number, found[2])
        self.assertIn("/resume?" + html.escape(urlencode(
            {"group": "fn.agents", "number": reply_number,
             "id": reply_article["message_id"]})), found[2])
        bare = self.http(server, "GET", "/find?" + urlencode(
            {"id": root_article["message_id"]}))
        self.assertEqual(bare[0], 200)
        self.assertNotIn("Local #", bare[2])
        # LIST COUNTS: the group card says how many articles the node holds.
        self.assertIn("%d articles" % high, self.http(server, "GET", "/")[2])

        marked = self.http(server, "POST", "/mark", {"group": "fn.agents",
                                                     "through": str(high)})
        self.assertEqual(marked[0], 200)
        self.assertNotIn("class='unread-dot'", marked[2])
        restarted = self.start_web(marks_path)
        self.assertIn("nothing unread", self.http(restarted, "GET", "/")[2])


def native_openssl():
    """OpenSSL 3.5 for ML-DSA-65 keys: FN_TEST_OPENSSL, else the prefix
    tools/hbox_native.sh exports, else the PATH's."""
    named = os.environ.get("FN_TEST_OPENSSL")
    if named:
        return named
    prefix = os.environ.get("FN_OPENSSL_PREFIX")
    if prefix and os.access(Path(prefix) / "bin" / "openssl", os.X_OK):
        return str(Path(prefix) / "bin" / "openssl")
    return "openssl"


def dot_stuff(octets):
    return b"".join((b"." + line if line.startswith(b".") else line)
                    for line in octets.splitlines(keepends=True))


@unittest.skipUnless(os.access(IMAGE, os.X_OK), "frozen native developer image required")
class NativeProvenanceWebTests(unittest.TestCase):
    """PKT-175 and PKT-253 on the native owner: an article signed by the image's
    own hybrid-sign-carrier and POSTed over a protected login; the page's
    fourth fact is the node's HDR :fn-enrollment through an enrollment, a
    rotation and a revocation, beside the unchanged historical verdict; the
    fifth is this reader's own check with its own keyring."""

    USER, SECRET = "ember-provenance", "web-provenance-secret-3"
    ED_PUBLIC = "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
    ED_SECRET = "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
    ED_PUBLIC_2 = "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c"
    PRINCIPAL = bytes([0x55]) * 32

    @classmethod
    def invoke(cls, *args, timeout=180):
        done = subprocess.run([str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
                              env=native_environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout, check=False)
        assert done.returncode == 0, "%s -> %d: %s" % (
            args[:2], done.returncode, done.stderr.decode(errors="replace")[-2000:])
        return done

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fn-web-provenance-")
        root = cls.root = Path(cls.temporary.name)
        openssl = native_openssl()
        cls.control = root / "control.sock"
        cls.port = free_loopback_port()
        cls.cert, key = root / "cert.pem", root / "key.pem"
        subprocess.run([openssl, "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                        "-out", str(cls.cert), "-sha256", "-days", "1", "-nodes",
                        "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=60, check=True)
        cls.config = root / "fn.toml"
        cls.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n'.format(
                root / "store", cls.port, cls.cert, key, cls.control,
                root / "credentials.toml"), encoding="ascii")
        cls.invoke("operator", cls.config, "init", "fn.agents")
        enrolled = subprocess.run(
            [sys.executable, "bin/fn", "--config", str(cls.config), "principal",
             "set-password", cls.USER, "--password", cls.SECRET, "--posting"],
            cwd=ROOT, env=native_environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=900, check=False)
        assert enrolled.returncode == 0, enrolled.stderr.decode(errors="replace")

        cls.principal = root / "principal.bin"
        cls.principal.write_bytes(cls.PRINCIPAL)
        cls.ed_public, cls.ed_secret = root / "ed-public.bin", root / "ed-secret.bin"
        cls.ed_public.write_bytes(bytes.fromhex(cls.ED_PUBLIC))
        cls.ed_secret.write_bytes(bytes.fromhex(cls.ED_SECRET + cls.ED_PUBLIC))
        cls.ed_public_2 = root / "ed-public-2.bin"
        cls.ed_public_2.write_bytes(bytes.fromhex(cls.ED_PUBLIC_2))
        for stem in ("ml", "ml-2"):
            subprocess.run([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                            str(root / (stem + "-private.pem"))], timeout=60, check=True)
            subprocess.run([openssl, "pkey", "-in", str(root / (stem + "-private.pem")),
                            "-pubout", "-out", str(root / (stem + "-public.pem"))],
                           timeout=60, check=True)
        cls.ml_private, cls.ml_public = root / "ml-private.pem", root / "ml-public.pem"
        cls.ml_public_2 = root / "ml-2-public.pem"
        verifier = Path(fn_web.VERIFIER)

        def keyring(path, ed, ml, generation):
            entry = subprocess.run([sys.executable, str(verifier), "keyring-entry",
                                    str(cls.principal), str(ed), str(ml),
                                    "--generation", str(generation)],
                                   stdout=subprocess.PIPE, timeout=60, check=True)
            path.write_text(json.dumps({"format": "fn-verify-keyring-v1",
                                        "principals": [json.loads(entry.stdout)]}))
            return path
        # The reader's own keyrings: one pins the signing keys, one pins only
        # the keys the principal rotated to (a reader who learned of the rotation).
        cls.reader_keyring = keyring(root / "reader.json", cls.ed_public, cls.ml_public, 1)
        cls.rotated_keyring = keyring(root / "rotated.json", cls.ed_public_2,
                                      cls.ml_public_2, 2)

        cls.owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(cls.config), "run"],
                                     cwd=ROOT, env=native_environment(),
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            line = wait_for_announcement(cls.owner, b"LISTENING ")
            assert line == "LISTENING {}\n".format(cls.port).encode(), line
            cls.invoke("hybrid-enroll", cls.control, "1", cls.principal, cls.ed_public,
                       cls.ml_public)
            source = (b"From: agent@example.invalid\r\nDate: Sat, 26 Sep 2026 12:00:00 +0000"
                      b"\r\nNewsgroups: fn.agents\r\nSubject: signed provenance\r\n"
                      b"Message-ID: <provenance-signed@example.invalid>\r\n\r\n"
                      b"signed body\r\n")
            (root / "signed.eml").write_bytes(source)
            cls.invoke("hybrid-sign-carrier", cls.principal, cls.ed_public, cls.ed_secret,
                       cls.ml_public, cls.ml_private, root / "signed.eml",
                       root / "signed-carried.eml")
            cls.signed_reply = cls.post((root / "signed-carried.eml").read_bytes())
            cls.plain_reply = cls.post(source.replace(b"provenance-signed", b"provenance-plain")
                                       .replace(b"signed provenance", b"plain provenance"))
        except BaseException:
            print("owner stderr:\n" + stop_and_diagnostics(cls.owner, timeout=60), flush=True)
            cls.temporary.cleanup()
            raise

    @classmethod
    def post(cls, octets):
        node = fn_verify.Node("127.0.0.1", cls.port, cafile=str(cls.cert),
                              credentials=(cls.USER, cls.SECRET), timeout=120.0)
        try:
            status = node.command("POST")
            assert status.startswith("340"), status
            node.sock.sendall(dot_stuff(octets) + b".\r\n")
            return node.line()
        finally:
            node.close()

    @classmethod
    def tearDownClass(cls):
        stop_and_diagnostics(cls.owner, timeout=60)
        cls.owner.stdout.close()
        cls.owner.stderr.close()
        cls.temporary.cleanup()

    def page(self, msgid, keyring):
        args = SimpleNamespace(host="127.0.0.1", port=self.port, timeout=60.0, plain=False,
                               cafile=str(self.cert), keyring=str(keyring) if keyring else None)
        server = fn_web.WebServer(0, fn_web.Backend(args, self.USER, self.SECRET))
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            conn = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=120)
            conn.request("GET", "/find?" + urlencode({"id": msgid, "group": "fn.agents"}))
            reply = conn.getresponse()
            answer = reply.status, reply.read().decode("utf-8")
            conn.close()
        finally:
            server.shutdown()
            server.server_close()
            thread.join(5)
        self.assertEqual(answer[0], 200, answer[1][-2000:])
        self.assertNotIn(self.SECRET, answer[1])
        return answer[1]

    def fact(self, page, name):
        found = re.search("<dt>" + re.escape(name) + "</dt><dd>(.*?)</dd>", page)
        self.assertIsNotNone(found, name)
        return found.group(1)

    def test_enrollment_rotation_and_revocation_beside_the_historical_verdict(self):
        self.assertTrue(self.signed_reply.startswith("240"), self.signed_reply)
        self.assertTrue(self.plain_reply.startswith("240"), self.plain_reply)
        p = "55" * 32
        signed, plain = "<provenance-signed@example.invalid>", "<provenance-plain@example.invalid>"

        def facts(msgid, keyring):
            page = self.page(msgid, keyring)
            return (self.fact(page, "The node's historical verdict"),
                    self.fact(page, "Current enrollment or authorization"),
                    self.fact(page, "Independent verification here"))

        verdict, current, own = facts(signed, self.reader_keyring)
        self.assertIn("<span class='badge active'>active</span> principal %s is enrolled "
                      "now at keyring generation 1" % p, current)
        self.assertIn("<code>active %s keyring 1</code>" % p, current)
        self.assertIn("<span class='badge verified-here'>verified-here</span> verified here: "
                      "principal " + p, own)
        _, plain_current, plain_own = facts(plain, self.reader_keyring)
        self.assertIn("<span class='badge none'>none</span> the node&#x27;s recorded verdict "
                      "names no principal", plain_current)
        self.assertIn("<span class='badge failed-here'>failed-here</span> failed here: "
                      "no-carrier", plain_own)
        _, _, no_keyring = facts(signed, None)
        self.assertIn("<span class='badge not-performed'>not-performed</span> not performed: "
                      "no keyring", no_keyring)

        # Rotation: the principal enrolls new keys at generation 2.  The node's
        # current fact moves; its historical verdict does not.
        self.invoke("hybrid-enroll", self.control, "2", self.principal, self.ed_public_2,
                    self.ml_public_2)
        verdict_2, current_2, _ = facts(signed, self.reader_keyring)
        self.assertEqual(verdict_2, verdict)
        self.assertIn("<span class='badge retired'>retired</span> principal %s has enrolled "
                      "again since: its current keyring generation is 2" % p, current_2)
        _, _, rotated_own = facts(signed, self.rotated_keyring)
        self.assertIn("<span class='badge failed-here'>failed-here</span> failed here: "
                      "key-not-pinned", rotated_own)

        # Revocation at generation 3.
        self.invoke("hybrid-revoke", self.control, "3", self.principal)
        verdict_3, current_3, own_3 = facts(signed, self.reader_keyring)
        self.assertEqual(verdict_3, verdict)
        self.assertIn("<span class='badge revoked'>revoked</span> principal %s is revoked: "
                      "its newest keyring entry is the revocation at generation 3" % p,
                      current_3)
        # The reader's own check is its own: its keyring still pins the keys.
        self.assertIn("verified-here", own_3)


def fn_client_first(fields, name):
    return fn_web.fn_client.first(fields, name)


def html_unescape(text):
    return html.unescape(text)


if __name__ == "__main__":
    unittest.main()
