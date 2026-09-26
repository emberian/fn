"""Read-only groups on a running node (O2; NNT-040, PRF-196, SCN-125).

Subjects:

* `operator CONFIG group policy NAME n|y`, offline and live, stages
  (:set-group-status NAME STATUS 0 nil), configuration delta code 21
  (books/native-admin.lisp `fn-native-admin-plan-deltas`; the fold's keystone
  `fn-cfg-set-group-status-sets-the-status`, books/config-invariants.lisp).
* The served POST step refuses an ordinary article naming a closed group with
  the 441 of `fn-post-refusal-line :group-read-only`, and LIST ACTIVE lists
  that group with status `n` from the same list
  (`fn-gst-post-gate-refuses-exactly-a-listed-n-group`,
  books/group-status.lisp, called by books/nntp-post.lisp
  `fn-nntp-post-step`).
* A connection keeps the configuration it pinned; a new connection sees the
  change; a restart replays it.

The source checks are always active.  The executable witnesses need the saved
image; when it is absent they skip and name the image they wanted.
"""
import os
from pathlib import Path
import select
import signal
import socket
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))

EXIT_OK, EXIT_REFUSED = 0, 1
READ_ONLY = (b"441 posting failed; a group this article names is read-only here "
             b"(LIST ACTIVE status n)")


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    env.pop("FN_HOST", None)
    return env


def executable(image):
    return image.is_file() and os.access(image, os.X_OK)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


class GroupPolicySourceTests(unittest.TestCase):
    def test_the_post_step_gates_an_accepted_article(self):
        post = (ROOT / "books" / "nntp-post.lisp").read_text(encoding="ascii")
        start = post.index("(defun fn-nntp-post-step ")
        body = post[start:post.index("(defun", start + 10)]
        self.assertIn("(fn-post-gated-decision", body)
        self.assertIn("(fn-post-reader-env config observation)", body)
        start = post.index("(defun fn-post-gated-decision")
        gated = post[start:post.index("(defthm", start)]
        self.assertLess(gated.index("(fn-inj-decide"), gated.index("(fn-gst-post-gate"))
        self.assertIn("(fn-inj-refuse :group-read-only)", gated)

    def test_the_owner_installs_the_closed_list(self):
        agent = (ROOT / "books" / "owner-agent.lisp").read_text(encoding="ascii")
        self.assertIn("(fn-cfg-closed-names (fn-cfg-value cfg)", agent)
        host = (ROOT / "host" / "owner-host.lisp").read_text(encoding="ascii")
        start = host.index("(defun fn-owner-posting-configure")
        body = host[start:host.index("(defun", start + 10)]
        self.assertIn("(fn-inj-config-closed cfg)", body)

    def test_the_delta_code_is_21(self):
        config = (ROOT / "books" / "config.lisp").read_text(encoding="ascii")
        self.assertIn("((equal kind :set-group-status) 21)", config)
        self.assertIn("((equal code 21) :set-group-status)", config)


@unittest.skipUnless(executable(IMAGE),
                     "build/fn-host (or FN_NATIVE_HOST) is required: the served "
                     "POST and LIST ACTIVE run only in a saved image")
class GroupPolicyImageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-group-policy-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.assertEqual(self.operator("init", "fn.test").returncode, EXIT_OK)
        created = self.operator("group", "create", "fn.ro")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())

    def operator(self, *words, timeout=180):
        return subprocess.run(
            [str(IMAGE), "--fn", "operator", str(self.config), *words],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False)

    def start_owner(self):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        self.addCleanup(self.reap, process)
        for _ in range(4):
            self.assertTrue(select.select([process.stdout], [], [], 180)[0],
                            "the owner did not become ready")
            line = process.stdout.readline()
            if line.startswith(b"LISTENING "):
                return process
            if process.poll() is not None:
                self.fail("owner failed: {}".format(
                    process.stderr.read().decode("utf-8", "replace")))
        self.fail("the owner's readiness output was malformed")

    def stop_owner(self, process):
        process.send_signal(signal.SIGTERM)
        self.assertEqual(process.wait(timeout=60), EXIT_OK,
                         process.stderr.read().decode("utf-8", "replace"))

    def reap(self, process):
        if process.poll() is None:
            process.send_signal(signal.SIGKILL)
            process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def reader(self):
        connection = socket.create_connection(("127.0.0.1", self.port), timeout=60)
        self.addCleanup(connection.close)
        stream = connection.makefile("rb")
        self.addCleanup(stream.close)
        greeting = stream.readline()
        self.assertTrue(greeting.startswith(b"20"), greeting)
        return connection, stream

    @staticmethod
    def command(connection, stream, line, multiline):
        connection.sendall(line.encode("ascii") + b"\r\n")
        status = stream.readline()
        lines = []
        if multiline and status[:1] == b"2":
            while True:
                row = stream.readline()
                if row in (b".\r\n", b""):
                    break
                lines.append(row)
        return status, lines

    def active(self, connection, stream):
        status, rows = self.command(connection, stream, "LIST ACTIVE", True)
        self.assertTrue(status.startswith(b"215"), status)
        return {row.split()[0]: row.split()[3] for row in rows}

    def post(self, connection, stream, group, tag):
        status, _ = self.command(connection, stream, "POST", False)
        self.assertTrue(status.startswith(b"340"), status)
        article = ("From: poster@example.invalid\r\nSubject: {}\r\n"
                   "Newsgroups: {}\r\nMessage-ID: <{}@example.invalid>\r\n\r\n"
                   "Hello.\r\n.\r\n").format(tag, group, tag)
        connection.sendall(article.encode("ascii"))
        return stream.readline().rstrip(b"\r\n")

    def test_read_only_group_offline_live_and_after_restart(self):
        # Offline: refused by name for an unknown group and an unserved value.
        self.assertEqual(self.operator("group", "policy", "fn.absent", "n").returncode,
                         EXIT_REFUSED)
        self.assertNotEqual(self.operator("group", "policy", "fn.ro", "m").returncode,
                            EXIT_OK)
        closed = self.operator("group", "policy", "fn.ro", "n")
        self.assertEqual(closed.returncode, EXIT_OK, closed.stderr.decode())

        owner = self.start_owner()
        pinned, pinned_stream = self.reader()
        self.assertEqual(self.active(pinned, pinned_stream),
                         {b"fn.ro": b"n", b"fn.test": b"y"})
        # POST to the closed group, alone and cross-posted: 441 by name.
        self.assertEqual(self.post(pinned, pinned_stream, "fn.ro", "ro-1"), READ_ONLY)
        self.assertEqual(self.post(pinned, pinned_stream, "fn.test,fn.ro", "ro-2"),
                         READ_ONLY)
        # The open group accepts, and nothing of the refused posts is stored.
        self.assertTrue(self.post(pinned, pinned_stream, "fn.test", "ok-1")
                        .startswith(b"240"))
        status, _ = self.command(pinned, pinned_stream,
                                 "STAT <ro-1@example.invalid>", False)
        self.assertTrue(status.startswith(b"430"), status)

        # Live: reopen the group.  A new connection sees "y" and posts; the
        # connection that pinned the old configuration keeps its answer.
        opened = self.operator("group", "policy", "fn.ro", "y")
        self.assertEqual(opened.returncode, EXIT_OK, opened.stderr.decode())
        fresh, fresh_stream = self.reader()
        self.assertEqual(self.active(fresh, fresh_stream),
                         {b"fn.ro": b"y", b"fn.test": b"y"})
        self.assertTrue(self.post(fresh, fresh_stream, "fn.ro", "ro-3")
                        .startswith(b"240"))
        # Live again: close it; a new connection is refused.
        closed = self.operator("group", "policy", "fn.ro", "n")
        self.assertEqual(closed.returncode, EXIT_OK, closed.stderr.decode())
        third, third_stream = self.reader()
        self.assertEqual(self.post(third, third_stream, "fn.ro", "ro-4"), READ_ONLY)
        self.stop_owner(owner)

        # A restart replays the last record: fn.ro is "n".
        restarted = self.start_owner()
        after, after_stream = self.reader()
        self.assertEqual(self.active(after, after_stream),
                         {b"fn.ro": b"n", b"fn.test": b"y"})
        self.assertEqual(self.post(after, after_stream, "fn.ro", "ro-5"), READ_ONLY)
        self.stop_owner(restarted)


if __name__ == "__main__":
    unittest.main()
