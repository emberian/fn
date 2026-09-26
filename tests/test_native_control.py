"""Public native operator submission through the serialized local owner."""
import os
from pathlib import Path
import re
import select
import signal
import socket
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
# The stop cut after a control submission, and the owner's SIGTERM and
# cleanup-pause cuts, are selected by environment variables that only a
# developer image honours; a production image refuses to start with any of
# them (host/native/io.lisp, `fnn-developer-selector-gate').
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
DEVELOPER_REASON = (
    "build/fn-host-developer (or FN_NATIVE_DEVELOPER_HOST) is required: {} is "
    "a developer-image selector and a production image refuses to start with it")
# The registered developer selectors, as host/native/io.lisp declares them.
SELECTORS = tuple(re.findall(r'"(FN_[A-Z_]+)"', re.search(
    r"\(defparameter \+fnn-developer-selectors\+\s+'\((.*?)\)\)",
    (ROOT / "host/native/io.lisp").read_text(encoding="ascii"), re.S).group(1)))
EXIT_USAGE = 5
# The structured local-control replies, as ACL2 defines them: each tagged
# reply the control books construct, `(list :<kind>-reply status ...)'.
STRUCTURED_REPLY_KINDS = {
    kind
    for book in ("books/consumer-local-control.lisp",
                 "books/topic-history-local-control.lisp")
    for kind in re.findall(r"\(list\s+(:[a-z-]+-reply)\b",
                           (ROOT / book).read_text(encoding="ascii"))}


def executable(path):
    return path.is_file() and os.access(path, os.X_OK)


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    for name in SELECTORS:
        env.pop(name, None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


# What `operator post` stores (books/owner.lisp fn-own-operator-submit): the
# injecting agent's Path line and Injection-Info line, then the submitted
# octets unchanged.  These articles supply Date and Message-ID, so no
# Injection-Date is added (RFC 5537 section 3.5 item 11;
# fn-inj-no-injection-date-when-date-and-message-id-are-supplied).  These
# stores set no `path-identity`, so the agent is the owner's fallback identity
# (host/owner-host.lisp `*fn-owner-agent*').
INJECTION_PREFIX = re.compile(
    rb"\APath: fn\.example\.invalid!not-for-mail\r\n"
    rb"Injection-Info: fn\.example\.invalid\r\n")


class NativeControlCutGateTests(unittest.TestCase):
    """Every developer selector passes one gate, at process start.

    The stop cut after a control submission was gated where it was read, on a
    worker thread after the owner had answered, so a production image turned
    an accepted article into exit 4 (campaign dabebb84, F4); the control fault
    was gated inside the owner's serialized action and answered 3 with nothing
    written (F5); four other selectors had no gate (F6).  These need no image.
    The deployed functions (fnn-main, the readers, the control reply, the
    stop) are run against stubs by tests/native_developer_selectors_raw.lisp,
    through tests/test_native_owner.py.
    """

    def test_every_selector_is_read_only_through_the_accessor(self):
        # A new selector read straight from the environment would bypass the
        # startup gate; the accessor faults on a name the table lacks.
        for path in sorted((ROOT / "host/native").glob("*.lisp")):
            source = path.read_text(encoding="utf-8")
            direct = re.findall(r'posix-getenv\s+"(FN_[A-Z_]+)"', source)
            guarded = {name for name in direct if name.startswith((
                "FN_NATIVE_", "FN_BP_", "FN_TCPCL_TEST_",
                "FN_CHECKPOINT_TEST_", "FN_APP_JOURNAL_TEST_")) or
                name == "FN_IMMUTABLE_PUBLISH_TEST_FAIL"}
            self.assertEqual(
                sorted(guarded - {"FN_NATIVE_PROFILE", "FN_NATIVE_IMAGE"}), [],
                "{} reads a selector around the gate".format(path.name))
            for name in re.findall(r'\(fnn-developer-selector\s+"([A-Z_]+)"\)', source):
                self.assertIn(name, SELECTORS, path.name)
        self.assertGreaterEqual(len(SELECTORS), 9)

    def test_the_gate_runs_before_dispatch(self):
        source = (ROOT / "host/native/io.lisp").read_text(encoding="ascii")
        main = source[source.index("(defun fnn-main ()"):]
        self.assertLess(main.index("(fnn-developer-selector-gate argv)"),
                        main.index("(fnn-dispatch argv)"))

    def test_the_reply_is_the_owners_status(self):
        source = (ROOT / "host/native/control.lisp").read_text(encoding="ascii")
        body = source[source.index("(defun fnn-control-handle-client"):
                      source.index("(defun fnn-control-client-done")]
        # Every structured reply the ACL2 control books construct carries the
        # owner's status second; the after-submit hook must see that status
        # for each of them, so the host's list is exactly the ACL2 set.
        member = re.search(r"\(member \(first status\)\s+'\(([^()]*)\)\)", body)
        self.assertIsNotNone(member, "after-submit reply-kind test not found")
        self.assertEqual(set(member.group(1).split()), STRUCTURED_REPLY_KINDS)
        boundary = (ROOT / "host/native-control-host.lisp").read_text(encoding="ascii")
        for kind in STRUCTURED_REPLY_KINDS:
            self.assertIn(f"(defun fn-native-control-host-{kind[1:]}-encode", boundary)
        self.assertIn("(second status) status))", body)
        self.assertIn("(fnn-control-send-reply socket status)", body)
        self.assertLess(body.index("(fnn-control-test-after-submit"),
                        body.index("(fnn-control-send-reply socket status)"))

    def test_the_stop_is_directed_at_the_calling_thread(self):
        source = (ROOT / "host/native/control.lisp").read_text(encoding="ascii")
        body = source[source.index("(defun fnn-control-stop-calling-thread"):
                      source.index("(defun fnn-control-test-after-submit")]
        self.assertIn('"pthread_kill"', body)
        self.assertIn('"pthread_self"', body)
        self.assertNotIn("sb-posix:getpid", body)

    def test_feed_stop_follows_fnfd_flush_and_precedes_socket_send(self):
        source = (ROOT / "host/native/feed-service.lisp").read_text(encoding="ascii")
        reply = source[source.index("(defun fnn-feed-reply-step"):
                       source.index("(defun fnn-feed-lost")]
        self.assertLess(reply.index("(fnn-owner-feed-flush service)"),
                        reply.index("(values word"))
        consume = source[source.index("(defun fnn-feed-consume"):
                         source.index("(defun fnn-feed-pump-link")]
        self.assertLess(consume.index("(fnn-feed-reply-step service"),
                        consume.index("(fnn-control-stop-calling-thread)"))
        self.assertLess(consume.index("(fnn-control-stop-calling-thread)"),
                        consume.index("(fnn-feed-send link command)"))


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

    def assert_injected(self, stored, payload):
        """`stored' is `payload' injected by this node: RFC 5537 3.5."""
        prefix = INJECTION_PREFIX.match(stored)
        self.assertIsNotNone(prefix, stored[:160])
        self.assertEqual(stored[prefix.end():], payload)

    def start_owner(self, extra_env=None, image=None):
        env = environment()
        if extra_env:
            env.update(extra_env)
        process = subprocess.Popen(
            [str(image or IMAGE), "--fn", "operator", str(self.config), "run"],
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
        self.assert_injected(observed.stdout, payload)
        absent = self.inspect_store(second_store, message_id)
        self.assertNotEqual(absent.returncode, 0)

    def test_two_clients_sigterm_cleanup_and_restart(self):
        if not executable(DEVELOPER):
            raise unittest.SkipTest(
                DEVELOPER_REASON.format("FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP"))
        owner = self.start_owner({"FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP": "1"},
                                 image=DEVELOPER)
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
            self.assert_injected(observed.stdout, payload)

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
        if not executable(DEVELOPER):
            raise unittest.SkipTest(
                DEVELOPER_REASON.format("FN_NATIVE_OWNER_TEST_SIGTERM"))
        env = environment()
        env["FN_NATIVE_OWNER_TEST_SIGTERM"] = "after-install"
        process = subprocess.Popen(
            [str(DEVELOPER), "--fn", "operator", str(self.config), "run"],
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
        # The stop is directed at the worker thread that holds the reply
        # (host/native/control.lisp `fnn-control-stop-calling-thread'), so the
        # reply cannot leave before the stop and the client's exit 3 below is
        # deterministic.  With a process-directed SIGSTOP it was not: 2 of 5
        # clients got ACCEPTED on the dabebb84 image (campaign F3).
        if not executable(DEVELOPER):
            raise unittest.SkipTest(
                DEVELOPER_REASON.format("FN_NATIVE_CONTROL_TEST_STOP"))
        owner = self.start_owner({"FN_NATIVE_CONTROL_TEST_STOP": "after-submit"},
                                 image=DEVELOPER)
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
        self.assert_injected(observed.stdout, payload)
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

    def store_digest(self):
        return sorted((str(path.relative_to(self.store)),
                       path.read_bytes() if path.is_file() else None)
                      for path in self.store.rglob("*")
                      if path.name != "writer.lock")

    def test_the_production_image_refuses_every_selector_at_startup(self):
        # One gate, before any store is opened: exit 5 naming the variable,
        # no control socket, no listener, the store's bytes unchanged.  This
        # replaces the mid-request refusals of campaign dabebb84 F4 to F6.
        before = self.store_digest()
        for name in SELECTORS:
            with self.subTest(selector=name):
                env = environment()
                env[name] = "x"
                started = subprocess.run(
                    [str(IMAGE), "--fn", "operator", str(self.config), "run"],
                    cwd=ROOT, env=env, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, timeout=120, check=False)
                self.assertEqual(started.returncode, EXIT_USAGE,
                                 started.stderr.decode())
                self.assertIn(name.encode("ascii"), started.stderr)
                self.assertEqual(started.stdout, b"")
                self.assertFalse(self.control.exists())
                recovered = subprocess.run(
                    [str(IMAGE), "--fn", "store", str(self.store), "recover"],
                    cwd=ROOT, env=env, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, timeout=120, check=False)
                self.assertEqual(recovered.returncode, EXIT_USAGE,
                                 recovered.stderr.decode())
                self.assertEqual(recovered.stdout, b"")
        payload = self.root / "positional.eml"
        payload.write_bytes(self.article("<native-positional@example.invalid>"))
        injected = subprocess.run(
            [str(IMAGE), "--fn", "store", str(self.store), "post",
             "<native-positional@example.invalid>", str(payload), "-",
             "postpublish", "fn.test"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=120, check=False)
        self.assertEqual(injected.returncode, EXIT_USAGE, injected.stderr.decode())
        self.assertIn(b"FAULT argument", injected.stderr)
        self.assertEqual(self.store_digest(), before)

    def test_operator_post_is_injected_and_refuses_what_post_refuses(self):
        """`operator post` injects as the served POST does (INN lab of
        2026-09-22, finding 1), and refuses what injection refuses: a From
        with no address (RFC 5536 3.1.2; the agents run's `From: yue`), a
        supplied Xref (the server's field), and a Message-ID the article does
        not carry.  A supplied Path is accepted as the served POST accepts it
        (D32, RFC 5537 3.4): the node's identity is prepended and the
        supplied tail kept verbatim."""
        owner = self.start_owner()
        try:
            message_id = "<native-control-injected@example.invalid>"
            payload = self.article(message_id)
            accepted = self.post(message_id, payload)
            self.assertEqual(accepted.returncode, 0, accepted.stderr.decode())

            yue_id = "<native-control-yue@example.invalid>"
            yue = self.article(yue_id).replace(b"From: author@example.invalid",
                                              b"From: yue")
            refused = self.post(yue_id, yue)
            self.assertEqual(refused.returncode, 1, refused.stderr.decode())

            path_id = "<native-control-path@example.invalid>"
            supplied_path = self.post(path_id, b"Path: elsewhere!not-for-mail\r\n"
                                      + self.article(path_id))
            self.assertEqual(supplied_path.returncode, 0, supplied_path.stderr.decode())

            xref_id = "<native-control-xref@example.invalid>"
            refused_xref = self.post(xref_id, b"Xref: elsewhere fn.test:1\r\n"
                                     + self.article(xref_id))
            self.assertEqual(refused_xref.returncode, 1, refused_xref.stderr.decode())

            other = self.post("<native-control-other@example.invalid>",
                              self.article("<native-control-named@example.invalid>"))
            self.assertEqual(other.returncode, 1, other.stderr.decode())
            owner.send_signal(signal.SIGTERM)
            self.assertEqual(owner.wait(timeout=30), 0,
                             owner.stderr.read().decode("utf-8", "replace"))
        finally:
            if owner.poll() is None:
                owner.kill()
                owner.wait(timeout=10)
            owner.stdout.close()
            owner.stderr.close()
        observed = self.inspect(message_id)
        self.assertEqual(observed.returncode, 0, observed.stderr.decode())
        self.assert_injected(observed.stdout, payload)
        for absent in (yue_id, xref_id, "<native-control-other@example.invalid>"):
            self.assertNotEqual(self.inspect(absent).returncode, 0, absent)
        pathed = self.inspect(path_id)
        self.assertEqual(pathed.returncode, 0, pathed.stderr.decode())
        head = pathed.stdout.split(b"\r\n\r\n", 1)[0].split(b"\r\n")
        self.assertEqual([line for line in head if line.startswith(b"Path: ")],
                         [b"Path: fn.example.invalid!elsewhere!not-for-mail"])
        self.assertTrue(pathed.stdout.endswith(self.article(path_id)), pathed.stdout)

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
