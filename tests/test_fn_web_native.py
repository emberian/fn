"""The loopback web client against a scratch native writable fn owner.

Set FN_NATIVE_DEVELOPER_HOST to a frozen developer image and FN_NATIVE_TEST_ROOT
to its source snapshot. This test creates and removes only its own Store.
The web client is a separate Python process; the second fixture exercises its
current source against the pinned native image's existing NNTP and modelled
post-publication death cut, without rebuilding the native image.
"""
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
                    env["FN_NATIVE_POST_FAULT"] = "postpublish:kill"
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
                observed = request("GET", "/settle?id=" + token)
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


if __name__ == "__main__":
    unittest.main()
