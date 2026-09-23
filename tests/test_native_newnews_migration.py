"""Read carried schema-0 and newly stamped articles through a T2b reader.

Set FN_PRE_T2_NATIVE_DEVELOPER_HOST and FN_T2B_NATIVE_DEVELOPER_HOST to
frozen developer images. The test stages its own Store; it never uses a live
node. The pre-T2 image is needed only to create the legacy record.
"""

import os
from pathlib import Path
import select
import socket
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
OLD = Path(os.environ.get("FN_PRE_T2_NATIVE_DEVELOPER_HOST",
                          "/nonexistent/fn-pre-t2-developer"))
NEW = Path(os.environ.get("FN_T2B_NATIVE_DEVELOPER_HOST",
                          "/nonexistent/fn-t2b-developer"))


@unittest.skipUnless(os.access(OLD, os.X_OK) and os.access(NEW, os.X_OK),
                     "frozen pre-T2 and T2b developer images are required")
class NativeNewnewsMigrationTests(unittest.TestCase):
    def command(self, image, store, verb, *arguments):
        env = dict(os.environ)
        env["FN_HOST"] = "native"
        env["FN_NATIVE_HOST"] = str(image)
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             verb, *map(str, arguments)], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=90,
            check=False)
        self.assertEqual(result.returncode, 0,
                         f"{image.name} {verb}: {result.stderr.decode(errors='replace')}")

    def newnews(self, store):
        process = subprocess.Popen(
            [str(NEW), "--fn", "reader", "0", "1", str(store)], cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=os.environ.copy())
        try:
            port = None
            while port is None:
                ready = select.select([process.stdout], [], [], 90)[0]
                self.assertTrue(ready, "native reader did not announce a port")
                line = process.stdout.readline()
                if not line:
                    self.fail("native reader exited: " +
                              process.stderr.read().decode(errors="replace"))
                if line.startswith(b"LISTENING "):
                    port = int(line.split()[1])
            chunks = []
            with socket.create_connection(("127.0.0.1", port), timeout=30) as client:
                client.sendall(b"NEWNEWS fn.letters 19700101 000000 GMT\r\n"
                               b"NEWNEWS fn.letters 20990101 000000 GMT\r\n"
                               b"QUIT\r\n")
                client.shutdown(socket.SHUT_WR)
                client.settimeout(30)
                while True:
                    chunk = client.recv(4096)
                    if not chunk:
                        break
                    chunks.append(chunk)
            self.assertEqual(process.wait(timeout=60), 0)
            reply = b"".join(chunks)
            greeting, separator, responses = reply.partition(b"\r\n")
            self.assertEqual(separator, b"\r\n", reply)
            self.assertTrue(greeting.startswith(b"201 "), reply)
            return responses
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
            process.stdout.close()
            process.stderr.close()

    def test_legacy_horizon_and_new_stamp_on_reopened_store(self):
        with tempfile.TemporaryDirectory(prefix="fn-newnews-migration-") as temporary:
            base = Path(temporary)
            store = base / "store"
            payload = base / "article"
            payload.write_bytes(b"From: a@example.invalid\r\n"
                                b"Newsgroups: fn.letters\r\n\r\nold\r\n")
            old_id = b"<old-newnews@example.invalid>"
            new_id = b"<new-newnews@example.invalid>"
            self.command(OLD, store, "init")
            self.command(OLD, store, "post", "--message-id", old_id.decode(),
                         "--payload", payload, "--group", "fn.letters")

            heading = b"230 list of new articles by message-id follows\r\n"
            closing = b"205 closing connection\r\n"
            old_only = self.newnews(store)
            # This reader has no pinned wall observation. With no later stamped
            # article, :legacy has horizon :none and is conservatively reported
            # at both thresholds, including one in the future.
            self.assertEqual(old_only,
                             heading + old_id + b"\r\n.\r\n"
                             + heading + old_id + b"\r\n.\r\n" + closing)

            payload.write_bytes(payload.read_bytes().replace(b"old", b"new"))
            self.command(NEW, store, "post", "--message-id", new_id.decode(),
                         "--payload", payload, "--group", "fn.letters")
            mixed = self.newnews(store)
            # The new article's durable stamp supplies the legacy upper bound.
            # Both are new since 1970; neither is new since 2099.
            self.assertEqual(mixed,
                             heading + new_id + b"\r\n" + old_id
                             + b"\r\n.\r\n" + heading + b".\r\n" + closing)


if __name__ == "__main__":
    unittest.main()
