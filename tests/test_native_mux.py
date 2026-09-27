"""SCN-153: served connections on the I/O loops, and the capacity against memory.

Lane connection-multiplexing (2026-09-26; PKT-605; HST-024; PRF-223).  Over
each image (developer and production):

1. A capacity the machine cannot hold beside the store is refused by name at
   `run` (books/connection-budget.lisp fn-cbud-run-decide): exit 1, the line
   `refused connections-exceed-memory capacity=C holds=B per-connection=K
   KiB machine=M MB`, and nothing listens.
2. Under a capacity it holds, the service log names the bound (`connections
   holds=B per-connection=K KiB`), 300 held connections add no thread (the
   loops serve them; the worker-per-connection host added 300), each costs
   the node less than 64 KiB of resident memory at rest, and every one of
   them is served (a GROUP on each).
3. A live raise past the bound is refused by name (`connections-exceed-
   memory`) and changes nothing; a raise within it is published, and the
   capacity is then exactly what is admitted (the busy 400 after it).

    tools/hbox_native.sh --images developer,production . tests.test_native_mux
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import resource
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
PRODUCTION = os.environ.get("FN_NATIVE_HOST")
DEVELOPER = os.environ.get("FN_NATIVE_DEVELOPER_HOST")
BUSY = b"400 too many connections; try again later\r\n"
HOLDS = re.compile(rb"connections holds=(\d+) per-connection=(\d+) KiB")
REFUSED = re.compile(r"refused connections-exceed-memory capacity=(\d+) holds=(\d+) "
                     r"per-connection=(\d+) KiB machine=(\d+) MB")
CAPACITY = re.compile(
    r"^exposure capacity connections=(\d+) capacity=(\d+) per-address=(\d+) trusted=(\S+)$",
    re.M)
HELD = 300


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def first_line(sock, timeout=30):
    sock.settimeout(timeout)
    data = b""
    try:
        while not data.endswith(b"\n"):
            chunk = sock.recv(1)
            if not chunk:
                return data
            data += chunk
    except socket.timeout:
        return b"<timeout>"
    except (ConnectionResetError, BrokenPipeError):
        return b"<reset>"
    return data


def rss_kib(pid):
    out = subprocess.run(["ps", "-o", "rss=", "-p", str(pid)],
                         stdout=subprocess.PIPE, text=True).stdout.strip()
    return int(out)


def thread_count(pid):
    """Linux: /proc; OpenBSD: ps -H lists each kernel-visible thread."""
    status = Path("/proc/%d/status" % pid)
    if status.exists():
        for row in status.read_text().splitlines():
            if row.startswith("Threads:"):
                return int(row.split()[1])
    return len(subprocess.run(["ps", "-H", "-o", "pid=", "-p", str(pid)],
                              stdout=subprocess.PIPE, text=True).stdout.split())


def raise_nofile():
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    want = 4096 if hard == resource.RLIM_INFINITY else min(4096, hard)
    resource.setrlimit(resource.RLIMIT_NOFILE, (max(soft, want), hard))


class MuxCase:
    IMAGE: str | None = None

    def setUp(self):
        if not self.IMAGE:
            self.skipTest("image variable unset")
        raise_nofile()
        self.image = Path(self.IMAGE)
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-mux-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.process = None
        self.held = []
        self.addCleanup(self.stop)
        store = self.base / "store"
        self.port = free_port()
        self.command(["--fn", "store", store, "init", "fn.test"])
        self.config = self.base / "fn.toml"
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                store, self.port, self.base / "control.sock", self.base / "fn.log"),
            encoding="ascii")

    def command(self, arguments, expected=0):
        result = subprocess.run([str(self.image)] + list(map(str, arguments)),
                                cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=180, check=False)
        if expected is not None:
            self.assertEqual(result.returncode, expected, result)
        return result

    def policy(self, value, expected=0):
        return self.command(["--fn", "operator", self.config, "policy", "set",
                             "exposure-connections", value], expected=expected)

    def capacity(self):
        result = self.command(["--fn", "operator", self.config, "status"], expected=None)
        found = CAPACITY.findall(result.stdout.decode("ascii", "replace"))
        self.assertEqual(len(found), 1, result)
        return int(found[0][0]), int(found[0][1])

    def start(self):
        err = open(self.base / "stderr.log", "ab")
        self.addCleanup(err.close)
        self.process = subprocess.Popen(
            [str(self.image), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=err,
            preexec_fn=raise_nofile)

    def stop(self):
        for sock in self.held:
            sock.close()
        self.held = []
        if self.process is not None and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.communicate(timeout=60)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.communicate(timeout=60)

    def open_one(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=30)
        return sock, first_line(sock)

    def test_a_capacity_the_machine_cannot_hold_is_refused_at_start(self):
        self.policy(4000000)
        self.start()
        _, _ = self.process.communicate(timeout=300)
        self.assertEqual(self.process.returncode, 1)
        stderr = (self.base / "stderr.log").read_text("ascii", "replace")
        found = REFUSED.search(stderr)
        self.assertIsNotNone(found, stderr[-2000:])
        capacity, holds, per, machine = map(int, found.groups())
        self.assertEqual(capacity, 4000000)
        self.assertLess(holds, capacity)
        self.assertGreater(per, 0)
        self.assertGreater(machine, 0)
        self.assertIn(found.group(0), (self.base / "fn.log").read_text("ascii", "replace"))
        with self.assertRaises(OSError):
            socket.create_connection(("127.0.0.1", self.port), timeout=2).close()

    def test_connections_cost_no_thread_and_the_bound_is_kept_live(self):
        self.policy(HELD + 20)
        self.start()
        wait_for_announcement(self.process, b"LISTENING ")
        log = (self.base / "fn.log").read_bytes()
        found = HOLDS.search(log)
        self.assertIsNotNone(found, log[-2000:])
        holds, per = int(found.group(1)), int(found.group(2))
        self.assertGreaterEqual(holds, HELD + 20)
        pid = self.process.pid
        sock, line = self.open_one()
        self.assertTrue(line.startswith(b"20"), line)
        self.held.append(sock)
        time.sleep(1)
        threads_before = thread_count(pid)
        rss_before = rss_kib(pid)
        for _ in range(HELD - 1):
            sock, line = self.open_one()
            self.assertTrue(line.startswith(b"20"), (len(self.held), line))
            self.held.append(sock)
        time.sleep(2)
        threads_after = thread_count(pid)
        rss_after = rss_kib(pid)
        # The loops serve them: no thread per connection.
        self.assertLessEqual(threads_after, threads_before + 1,
                             (threads_before, threads_after))
        per_connection = (rss_after - rss_before) / (HELD - 1)
        print("NATIVE-MUX holds={} per-connection-figure={} KiB threads={}->{} "
              "rss={}->{} kB rss-per-connection={:.1f} kB".format(
                  holds, per, threads_before, threads_after, rss_before, rss_after,
                  per_connection))
        self.assertLess(per_connection, 64, (rss_before, rss_after))
        # Every held connection is served.
        for sock in self.held:
            sock.sendall(b"GROUP fn.test\r\n")
        for sock in self.held:
            self.assertTrue(first_line(sock).startswith(b"211 "))

        # A live raise past the bound is refused by name and changes nothing.
        refused = self.policy(holds + 1, expected=None)
        self.assertNotEqual(refused.returncode, 0, refused)
        text = (refused.stdout + refused.stderr).decode("ascii", "replace").lower()
        self.assertIn("connections-exceed-memory", text)
        self.assertEqual(self.capacity(), (HELD, HELD + 20))
        # Within it: published, and exactly that many are admitted.
        self.policy(HELD + 25)
        self.assertEqual(self.capacity(), (HELD, HELD + 25))
        for _ in range(25):
            sock, line = self.open_one()
            self.assertTrue(line.startswith(b"20"), line)
            self.held.append(sock)
        sock, line = self.open_one()
        sock.close()
        self.assertEqual(line, BUSY)


class DeveloperImageMux(MuxCase, unittest.TestCase):
    IMAGE = DEVELOPER


class ProductionImageMux(MuxCase, unittest.TestCase):
    IMAGE = PRODUCTION


if __name__ == "__main__":
    unittest.main()
