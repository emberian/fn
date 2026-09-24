"""The loopback web client against a scratch native writable fn owner.

Set FN_NATIVE_DEVELOPER_HOST to a frozen developer image and FN_NATIVE_TEST_ROOT
to its source snapshot. This test creates and removes only its own Store.
"""
import http.client
import os
from pathlib import Path
import re
import select
import subprocess
import sys
import tempfile
import threading
import unittest
from types import SimpleNamespace
from urllib.parse import urlencode

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


if __name__ == "__main__":
    unittest.main()
