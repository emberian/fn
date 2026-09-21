"""Public native operator submission through the serialized local owner."""
import os
from pathlib import Path
import select
import signal
import socket
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    env.pop("FN_NATIVE_CONTROL_TEST_STOP", None)
    env.pop("FN_NATIVE_OWNER_TEST_SIGTERM", None)
    env.pop("FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP", None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeControlTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-control-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "init", "fn.test"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.config.write_text(
            "[store]\npath = \"{}\"\n"
            "[listener]\nhost = \"127.0.0.1\"\nport = {}\n"
            "[control]\npath = \"{}\"\n".format(
                self.store, self.port, self.control), encoding="ascii")

    @staticmethod
    def article(message_id):
        return (b"From: author@example.invalid\r\n"
                b"Newsgroups: fn.test\r\n"
                b"Subject: exact native control\r\n"
                b"Date: Mon, 21 Sep 2026 09:00:00 +0000\r\n"
                b"Message-ID: " + message_id.encode("ascii") +
                b"\r\n\r\nexact payload bytes\r\n")

    def start_owner(self, extra_env=None):
        env = environment()
        if extra_env:
            env.update(extra_env)
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        seen_control = False
        deadline_lines = []
        for _ in range(4):
            ready = select.select([process.stdout], [], [], 180)[0]
            self.assertTrue(ready, "native operator did not become ready")
            line = process.stdout.readline()
            deadline_lines.append(line)
            if line.startswith(b"CONTROL "):
                seen_control = True
            if line.startswith(b"LISTENING "):
                self.assertTrue(seen_control, deadline_lines)
                return process
            if process.poll() is not None:
                self.fail("owner failed: {} {}".format(
                    deadline_lines, process.stderr.read().decode("utf-8", "replace")))
        self.fail("owner readiness output was malformed: {!r}".format(deadline_lines))

    def post(self, message_id, payload, env=None):
        path = self.root / (message_id.strip("<>").replace("@", "-") + ".eml")
        path.write_bytes(payload)
        return subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), "post",
             "--message-id", message_id, "--payload", str(path),
             "--group", "fn.test"],
            cwd=ROOT, env=env or environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=60, check=False)

    def inspect(self, message_id):
        return self.inspect_store(self.store, message_id)

    def inspect_store(self, store, message_id):
        return subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), "inspect", message_id],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)

    def test_shared_control_path_is_not_stolen_by_another_store(self):
        owner = self.start_owner()
        second_store = self.root / "second-store"
        second_config = self.root / "second.toml"
        initialized = subprocess.run(
            [str(IMAGE), "--fn", "store", str(second_store), "init", "fn.test"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        second_config.write_text(
            "[store]\npath = \"{}\"\n"
            "[listener]\nhost = \"127.0.0.1\"\nport = {}\n"
            "[control]\npath = \"{}\"\n".format(
                second_store, free_port(), self.control), encoding="ascii")
        second = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(second_config), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
        try:
            second_stdout, second_stderr = second.communicate(timeout=60)
            self.assertEqual(second.returncode, 1, second_stderr.decode())
            self.assertNotIn(b"CONTROL ", second_stdout)
            self.assertIn(b"control path is already owned", second_stderr)

            message_id = "<control-lease@example.invalid>"
            payload = self.article(message_id)
            accepted = self.post(message_id, payload)
            self.assertEqual(accepted.returncode, 0, accepted.stderr.decode())
        finally:
            if second.poll() is None:
                second.kill()
                second.wait(timeout=10)
            second.stdout.close()
            second.stderr.close()
            owner.send_signal(signal.SIGTERM)
            self.assertEqual(owner.wait(timeout=30), 0,
                             owner.stderr.read().decode("utf-8", "replace"))
            owner.stdout.close()
            owner.stderr.close()

        observed = self.inspect(message_id)
        self.assertEqual(observed.returncode, 0, observed.stderr.decode())
        self.assertEqual(observed.stdout, payload)
        absent = self.inspect_store(second_store, message_id)
        self.assertNotEqual(absent.returncode, 0)

    def test_two_clients_sigterm_cleanup_and_restart(self):
        owner = self.start_owner({"FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP": "1"})
        ids = ["<native-control-a@example.invalid>",
               "<native-control-b@example.invalid>"]
        payloads = [self.article(value) for value in ids]
        paths = []
        clients = []
        try:
            for index, payload in enumerate(payloads):
                path = self.root / "concurrent-{}.eml".format(index)
                path.write_bytes(payload)
                paths.append(path)
                clients.append(subprocess.Popen(
                    [str(IMAGE), "--fn", "operator", str(self.config), "post",
                     "--message-id", ids[index], "--payload", str(path),
                     "--group", "fn.test"], cwd=ROOT, env=environment(),
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE))
            for client in clients:
                stdout, stderr = client.communicate(timeout=60)
                self.assertEqual(client.returncode, 0, stderr.decode())
                self.assertEqual(stdout, b"")
            # Keep one served client active while SIGTERM asks the main owner
            # thread to take its ordinary stop/join/close path.
            active = socket.create_connection(("127.0.0.1", self.port), timeout=30)
            self.addCleanup(active.close)
            self.assertTrue(active.makefile("rb", buffering=0).readline().startswith(b"200 "))
            active_control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            active_control.settimeout(30)
            active_control.connect(str(self.control))
            active_control.sendall(b"F")  # hold an incomplete bounded frame
            self.addCleanup(active_control.close)
            owner.send_signal(signal.SIGTERM)
            ready = select.select([owner.stdout], [], [], 30)[0]
            self.assertTrue(ready, "owner did not enter ordinary cleanup")
            self.assertEqual(owner.stdout.readline(), b"OWNER-CLEANUP\n")
            owner.send_signal(signal.SIGTERM)
            self.assertEqual(owner.wait(timeout=30), 0,
                             owner.stderr.read().decode("utf-8", "replace"))
            self.assertEqual(active_control.recv(1), b"")
            self.assertFalse(self.control.exists())
        finally:
            if owner.poll() is None:
                owner.kill()
                owner.wait(timeout=10)
            owner.stdout.close()
            owner.stderr.close()

        for message_id, payload in zip(ids, payloads):
            observed = self.inspect(message_id)
            self.assertEqual(observed.returncode, 0, observed.stderr.decode())
            self.assertEqual(observed.stdout, payload)

        restarted = self.start_owner()
        try:
            duplicate = self.post(ids[0], payloads[0])
            self.assertEqual(duplicate.returncode, 0, duplicate.stderr.decode())
            self.assertIn(b"DUPLICATE", duplicate.stderr)
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            restarted.send_signal(signal.SIGTERM)
            self.assertEqual(restarted.wait(timeout=30), 0,
                             restarted.stderr.read().decode("utf-8", "replace"))
        finally:
            if restarted.poll() is None:
                restarted.kill()
                restarted.wait(timeout=10)
            restarted.stdout.close()
            restarted.stderr.close()

    def test_prelisten_sigterm_skips_modules_and_reopens(self):
        env = environment()
        env["FN_NATIVE_OWNER_TEST_SIGTERM"] = "after-install"
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            stdout, stderr = process.communicate(timeout=60)
            self.assertEqual(process.returncode, 0, stderr.decode())
            self.assertIn(b"OWNER-PRELISTEN\n", stdout)
            self.assertNotIn(b"CONTROL ", stdout)
            self.assertNotIn(b"LISTENING ", stdout)
            self.assertFalse(self.control.exists())
        finally:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=10)

        restarted = self.start_owner()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            restarted.send_signal(signal.SIGTERM)
            self.assertEqual(restarted.wait(timeout=30), 0,
                             restarted.stderr.read().decode("utf-8", "replace"))
        finally:
            if restarted.poll() is None:
                restarted.kill()
                restarted.wait(timeout=10)
            restarted.stdout.close()
            restarted.stderr.close()

    def test_lost_reply_after_submission_is_uncertain_and_recovers(self):
        owner = self.start_owner({"FN_NATIVE_CONTROL_TEST_STOP": "after-submit"})
        message_id = "<native-control-lost@example.invalid>"
        payload = self.article(message_id)
        payload_path = self.root / "lost.eml"
        payload_path.write_bytes(payload)
        client = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "post",
             "--message-id", message_id, "--payload", str(payload_path),
             "--group", "fn.test"], cwd=ROOT, env=environment(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            ready = select.select([owner.stdout], [], [], 60)[0]
            self.assertTrue(ready, "owner did not reach post-recovery cut")
            self.assertEqual(owner.stdout.readline(), b"CONTROL-SUBMITTED\n")
            owner.kill()
            owner.wait(timeout=10)
            stdout, stderr = client.communicate(timeout=30)
            self.assertEqual(client.returncode, 3, stderr.decode())
            self.assertEqual(stdout, b"")
            self.assertIn(b"uncertain operator post", stderr)
        finally:
            if client.poll() is None:
                client.kill()
                client.wait(timeout=10)
            if owner.poll() is None:
                owner.kill()
                owner.wait(timeout=10)
            owner.stdout.close()
            owner.stderr.close()

        observed = self.inspect(message_id)
        self.assertEqual(observed.returncode, 0, observed.stderr.decode())
        self.assertEqual(observed.stdout, payload)
        restarted = self.start_owner()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client_socket:
                stream = client_socket.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            restarted.send_signal(signal.SIGTERM)
            self.assertEqual(restarted.wait(timeout=30), 0,
                             restarted.stderr.read().decode("utf-8", "replace"))
        finally:
            if restarted.poll() is None:
                restarted.kill()
                restarted.wait(timeout=10)
            restarted.stdout.close()
            restarted.stderr.close()

    def test_disabled_posting_refuses_cli_and_served_post(self):
        with self.config.open("a", encoding="ascii") as stream:
            stream.write("[posting]\nenabled = false\n")
        owner = self.start_owner()
        message_id = "<native-control-disabled@example.invalid>"
        try:
            refused = self.post(message_id, self.article(message_id))
            self.assertEqual(refused.returncode, 1, refused.stderr.decode())
            self.assertIn(b"posting-disabled", refused.stderr.lower())
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"201 "))
                stream.write(b"POST\r\n")
                self.assertTrue(stream.readline().startswith(b"440 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            owner.send_signal(signal.SIGTERM)
            self.assertEqual(owner.wait(timeout=30), 0,
                             owner.stderr.read().decode("utf-8", "replace"))
        finally:
            if owner.poll() is None:
                owner.kill()
                owner.wait(timeout=10)
            owner.stdout.close()
            owner.stderr.close()

    def test_control_worker_ceiling_returns_busy(self):
        owner = self.start_owner()
        blockers = []
        try:
            # ACL2 fixes the active control worker ceiling at 16. Each partial
            # frame occupies one worker without entering owner admission.
            for _ in range(16):
                client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                client.settimeout(30)
                client.connect(str(self.control))
                client.sendall(b"F")
                blockers.append(client)
            time.sleep(1)
            message_id = "<native-control-busy@example.invalid>"
            refused = self.post(message_id, self.article(message_id))
            self.assertEqual(refused.returncode, 1, refused.stderr.decode())
            self.assertIn(b"busy", refused.stderr.lower())
        finally:
            for client in blockers:
                client.close()
            owner.send_signal(signal.SIGTERM)
            self.assertEqual(owner.wait(timeout=30), 0,
                             owner.stderr.read().decode("utf-8", "replace"))
            owner.stdout.close()
            owner.stderr.close()

    def test_partial_frame_has_one_absolute_deadline(self):
        owner = self.start_owner()
        client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        client.settimeout(30)
        try:
            client.connect(str(self.control))
            started = time.monotonic()
            client.sendall(b"F")
            readable = False
            while time.monotonic() - started < 12:
                if select.select([client], [], [], 0.5)[0]:
                    readable = True
                    break
                client.sendall(b"F")
            elapsed = time.monotonic() - started
            self.assertTrue(readable, "per-chunk reads reset the frame deadline")
            self.assertGreaterEqual(elapsed, 8)
            self.assertLess(elapsed, 12)
            self.assertNotEqual(client.recv(4096), b"")
        finally:
            client.close()
            owner.send_signal(signal.SIGTERM)
            self.assertEqual(owner.wait(timeout=30), 0,
                             owner.stderr.read().decode("utf-8", "replace"))
            owner.stdout.close()
            owner.stderr.close()


if __name__ == "__main__":
    unittest.main()
