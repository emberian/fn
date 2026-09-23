"""The loopback web client against a scratch native writable fn owner.

Set FN_NATIVE_DEVELOPER_HOST to a frozen developer image and FN_NATIVE_TEST_ROOT
to its source snapshot. This test creates and removes only its own Store.
"""
import http.client
import os
from pathlib import Path
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

                def request(method, path, data=None):
                    conn = http.client.HTTPConnection("127.0.0.1",
                                                      server.server_port, timeout=30)
                    headers = {}
                    if method == "POST":
                        headers["Content-Type"] = "application/x-www-form-urlencoded"
                        headers["Origin"] = "http://127.0.0.1:%d" % server.server_port
                        data = urlencode({"csrf": server.token, "group": "fn.agents",
                                          "subject": "Native web post", "sender": "Human <h@local.invalid>",
                                          "references": "", "body": "Native owner body <visible>"})
                    conn.request(method, path, body=data, headers=headers)
                    result = conn.getresponse()
                    answer = result.status, result.read().decode("utf-8")
                    conn.close()
                    return answer

                status, page = request("GET", "/")
                self.assertEqual(status, 200)
                self.assertIn("fn.agents", page)
                status, page = request("POST", "/post")
                self.assertEqual(status, 200)
                self.assertIn("<span class='badge accepted'>accepted</span>", page)
                status, page = request("GET", "/g?name=fn.agents")
                self.assertEqual(status, 200)
                self.assertIn("Native web post", page)
                status, page = request("GET", "/a?group=fn.agents&number=1")
                self.assertEqual(status, 200)
                self.assertIn("Native owner body &lt;visible&gt;", page)
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
