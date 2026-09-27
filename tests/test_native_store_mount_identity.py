"""The store's filesystem identity, required at every open (PKT-579, PRF-232,
STO-031, SCN-159), and the durability policy at the owner's start (PKT-648).

`init' records the identity of the filesystem the store root is on
(books/store-mount-identity.lisp); every open observes it again and ACL2
decides.  The unprivileged cases here move a store between two filesystems
the test can always reach: a temporary directory and the tree the test runs
from.  On hbox the first is tmpfs (/tmp) and the second ZFS (/tank), which is
the missing-mount case in miniature: the same path now resolves onto a
different filesystem.  The loop-mounted ext4 case (a real node volume
unmounted under a running layout) needs root and is the record's
hand-run evidence, not this module.

Every case asserts the exit code and ACL2's line by name; nothing here
decides what the node should answer.
"""
import os
from pathlib import Path
import select
import shutil
import signal
import socket
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
EXIT_OK, EXIT_REFUSED = 0, 1
RECORD = "filesystem-identity.fnmi"


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


def same_filesystem(a, b):
    return os.stat(a).st_dev == os.stat(b).st_dev


class MountIdentitySourceTests(unittest.TestCase):
    """What the source says, whether or not an image was built."""

    def test_every_open_checks_the_filesystem_before_reading(self):
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="utf-8")
        acquire = io[io.index("(defun fnn-acquire "):io.index("(defun fnn-store-close ")]
        self.assertLess(acquire.index("(fnn-check-filesystem-identity store)"),
                        acquire.index("(fnn-load-config store)"))
        check = io[io.index("(defun fnn-check-filesystem-identity"):
                   io.index("(defun fnn-publish-filesystem-record")]
        self.assertIn("'fn-smid-open-decision", check)
        self.assertIn("'fn-smid-start-verdict", check)
        self.assertIn("'fn-smid-refusal-text", check)

    def test_the_owner_start_asks_the_policy(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="utf-8")
        install = owner[owner.index("(defun fnn-owner-install "):]
        self.assertLess(install.index("(fnn-check-filesystem-identity store t)"),
                        install.index("(fnn-owner-recover-core store records"))


@unittest.skipUnless(executable(IMAGE), "native image not built")
class MountIdentityNativeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-mount-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.tmp = Path(self.temporary.name)
        scratch = ROOT / "build" / "mount-identity"
        scratch.mkdir(parents=True, exist_ok=True)
        self.other = Path(tempfile.mkdtemp(prefix="other-", dir=scratch))
        self.addCleanup(shutil.rmtree, self.other, True)

    def fn(self, *words, timeout=180):
        return subprocess.run([str(IMAGE), "--fn", *map(str, words)], cwd=ROOT,
                              env=environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout, check=False)

    def expect(self, result, code, what):
        self.assertEqual(result.returncode, code, "%s: %s%s" % (
            what, result.stdout.decode(errors="replace"),
            result.stderr.decode(errors="replace")))
        return result.stdout.decode(errors="replace") + result.stderr.decode(errors="replace")

    def test_init_records_and_the_open_on_the_same_filesystem_opens(self):
        store = self.tmp / "store"
        self.expect(self.fn("store", store, "init", "fn.test"), EXIT_OK, "init")
        self.assertTrue((store / RECORD).is_file())
        self.expect(self.fn("store", store, "recover"), EXIT_OK, "recover")
        # A copy on the same filesystem is the same store to this check.
        copy = self.tmp / "copy"
        shutil.copytree(store, copy)
        self.expect(self.fn("store", copy, "recover"), EXIT_OK, "recover the copy")

    def test_a_store_on_another_filesystem_is_refused_by_name_then_rebound(self):
        if same_filesystem(self.tmp, self.other):
            self.skipTest("the temporary directory and the tree share a filesystem")
        store = self.tmp / "store"
        self.expect(self.fn("store", store, "init", "fn.test"), EXIT_OK, "init")
        moved = self.other / "store"
        shutil.copytree(store, moved)
        for words in (("recover",), ("status",)):
            text = self.expect(self.fn("store", moved, *words), EXIT_REFUSED,
                               "open on another filesystem")
            self.assertIn("store filesystem changed: expected ", text)
            self.assertIn("mount the node volume or run `store rebind-filesystem`", text)
        rebound = self.expect(self.fn("store", moved, "rebind-filesystem"), EXIT_OK, "rebind")
        self.assertIn("rebound store filesystem: ", rebound)
        self.assertIn("; was ", rebound)
        self.expect(self.fn("store", moved, "recover"), EXIT_OK, "recover after rebind")
        # The original, untouched, still opens where it was made.
        self.expect(self.fn("store", store, "recover"), EXIT_OK, "the original")

    def test_an_empty_directory_where_the_store_was_is_refused_as_unrecorded(self):
        # The volume is not mounted: the store path is an empty directory on
        # the filesystem underneath.  Nothing is created there.
        empty = self.tmp / "store"
        empty.mkdir()
        text = self.expect(self.fn("store", empty, "recover"), EXIT_REFUSED, "empty root")
        self.assertIn("store filesystem unrecorded: ", text)
        self.assertEqual(list(empty.iterdir()), [])

    def test_a_removed_or_corrupted_record_is_refused_by_name(self):
        store = self.tmp / "store"
        self.expect(self.fn("store", store, "init", "fn.test"), EXIT_OK, "init")
        record = store / RECORD
        octets = bytearray(record.read_bytes())
        octets[12] ^= 1
        record.write_bytes(bytes(octets))
        text = self.expect(self.fn("store", store, "recover"), EXIT_REFUSED, "corrupted")
        self.assertIn("store filesystem record invalid: ", text)
        record.unlink()
        # A complete store with no record is a store made before the record:
        # it opens offline with a warning, and its owner does not start.
        text = self.expect(self.fn("store", store, "recover"), EXIT_OK, "removed")
        self.assertIn("warning: store filesystem unrecorded: ", text)
        config = self.tmp / "fn.toml"
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                          '[control]\npath = "{}"\n'.format(store, free_port(), self.tmp / "c.sock"),
                          encoding="ascii")
        started = subprocess.run([str(IMAGE), "--fn", "operator", str(config), "run"],
                                 cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=180, check=False)
        text = self.expect(started, EXIT_REFUSED, "start without a record")
        self.assertIn("store filesystem unrecorded: ", text)
        rebound = self.expect(self.fn("store", store, "rebind-filesystem"), EXIT_OK, "rebind")
        self.assertIn("; no valid record before", rebound)
        text = self.expect(self.fn("store", store, "recover"), EXIT_OK, "recover after rebind")
        self.assertNotIn("unrecorded", text)

    # --- PKT-648: the durability policy at the owner's start -----------------

    def operator_node(self, where):
        store = where / "store"
        config = where / "fn.toml"
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                          '[control]\npath = "{}"\n'.format(store, free_port(), where / "c.sock"),
                          encoding="ascii")
        self.expect(self.fn("operator", config, "init", "fn.test"), EXIT_OK, "operator init")
        return config

    def start(self, config):
        process = subprocess.Popen([str(IMAGE), "--fn", "operator", str(config), "run"],
                                   cwd=ROOT, env=environment(), stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, bufsize=0)
        self.addCleanup(self.reap, process)
        for _ in range(4):
            if not select.select([process.stdout], [], [], 180)[0]:
                break
            line = process.stdout.readline()
            if line.startswith(b"LISTENING "):
                return process, None
            if process.poll() is not None or not line:
                break
        process.wait(timeout=60)
        return process, process.stderr.read().decode(errors="replace")

    def reap(self, process):
        if process.poll() is None:
            process.send_signal(signal.SIGTERM)
            try:
                process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=10)
        for stream in (process.stdout, process.stderr):
            if stream and not stream.closed:
                stream.close()

    def memory_filesystem(self):
        with open("/proc/self/mountinfo", "rb") as table:
            lines = table.read().split(b"\n")
        best = b""
        kind = None
        path = os.path.realpath(self.tmp).encode()
        for line in lines:
            fields = line.split(b" ")
            if len(fields) < 10 or b"-" not in fields[6:]:
                continue
            mount = fields[4]
            dash = fields.index(b"-", 6)
            if (path == mount or path.startswith(mount.rstrip(b"/") + b"/")) and len(mount) >= len(best):
                best, kind = mount, fields[dash + 1]
        return kind in (b"tmpfs", b"ramfs")

    def test_a_policy_store_on_a_memory_filesystem_is_refused_at_start_then_allowed(self):
        if not os.path.exists("/proc/self/mountinfo") or not self.memory_filesystem():
            self.skipTest("the temporary directory is not on tmpfs here")
        config = self.operator_node(self.tmp)
        # status and health warn; an ordinary open does not.  An operator
        # store made without a mission has policy 0.
        status = self.expect(self.fn("operator", config, "status"), EXIT_OK, "status")
        self.assertIn("warning: store filesystem tmpfs at ", status)
        recovered = self.expect(self.fn("operator", config, "recover"), EXIT_OK, "recover")
        self.assertNotIn("warning: store filesystem", recovered)
        process, err = self.start(config)
        self.assertIsNone(err, "a policy-0 store on tmpfs starts")
        self.reap(process)
        # The operator requires durability: the start is refused by name.
        on = self.expect(self.fn("operator", config, "store", "rebind-filesystem",
                                 "--storage-require-durable", "on"), EXIT_OK, "policy on")
        self.assertIn("storage-require-durable=on", on)
        process, err = self.start(config)
        self.assertEqual(process.returncode, EXIT_REFUSED, err)
        self.assertIn("start refused: store filesystem tmpfs at ", err)
        self.assertIn("this store requires durable storage (storage-require-durable)", err)
        # And accepts the risk again.
        self.expect(self.fn("operator", config, "store", "rebind-filesystem",
                            "--storage-require-durable", "off"), EXIT_OK, "policy off")
        process, err = self.start(config)
        self.assertIsNone(err, "policy 0 again starts")


if __name__ == "__main__":
    unittest.main()
