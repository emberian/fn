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

from pathlib import Path
import re
import resource
import socket
import subprocess
import time
import unittest

from tests.native_harness import EXIT, Node, native_image, requires

PRODUCTION = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
BUSY = b"400 too many connections; try again later\r\n"
HOLDS = re.compile(rb"connections holds=(\d+) per-connection=(\d+) KiB")
REFUSED = re.compile(r"refused connections-exceed-memory capacity=(\d+) holds=(\d+) "
                     r"per-connection=(\d+) KiB machine=(\d+) MB")
CAPACITY = re.compile(
    r"^exposure capacity connections=(\d+) capacity=(\d+) per-address=(\d+) trusted=(\S+)$",
    re.M)
HELD = 300


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
    """IMAGE's owner with the exposure bound set by policy; the held
    connections are raw sockets (the subject is how many the owner holds)."""
    IMAGE: Path

    def setUp(self):
        # Before the owner starts: it inherits the raised descriptor limit.
        raise_nofile()
        self.held = []
        self.node = Node(self, self.IMAGE)
        self.addCleanup(self.close_held)  # runs before the node's stop
        self.log = self.node.root / "fn.log"
        self.node.write_config(extra='[log]\npath = "{}"\n'.format(self.log))
        self.port = self.node.port
        self.node.store("init", "fn.test", expect=EXIT.OK)

    def close_held(self):
        for sock in self.held:
            sock.close()
        self.held = []

    def policy(self, value, expected=EXIT.OK):
        return self.node.operator("policy", "set", "exposure-connections", value,
                                  expect=expected)

    def capacity(self):
        result = self.node.operator("status")
        found = CAPACITY.findall(result.stdout.decode("ascii", "replace"))
        self.assertEqual(len(found), 1, result)
        return int(found[0][0]), int(found[0][1])

    def open_one(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=30)
        return sock, first_line(sock)

    def test_a_capacity_the_machine_cannot_hold_is_refused_at_start(self):
        self.policy(4000000)
        owner = self.node.start(ready=None)
        self.node.exited(EXIT.REFUSED, timeout=300)
        stderr = owner.stderr.since(0).decode("ascii", "replace")
        found = REFUSED.search(stderr)
        self.assertIsNotNone(found, stderr[-2000:])
        capacity, holds, per, machine = map(int, found.groups())
        self.assertEqual(capacity, 4000000)
        self.assertLess(holds, capacity)
        self.assertGreater(per, 0)
        self.assertGreater(machine, 0)
        self.assertIn(found.group(0), self.log.read_text("ascii", "replace"))
        with self.assertRaises(OSError):
            socket.create_connection(("127.0.0.1", self.port), timeout=2).close()

    def test_connections_cost_no_thread_and_the_bound_is_kept_live(self):
        self.policy(HELD + 20)
        owner = self.node.start()
        log = self.log.read_bytes()
        found = HOLDS.search(log)
        self.assertIsNotNone(found, log[-2000:])
        holds, per = int(found.group(1)), int(found.group(2))
        self.assertGreaterEqual(holds, HELD + 20)
        pid = owner.pid
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


@requires(DEVELOPER)
class DeveloperImageMux(MuxCase, unittest.TestCase):
    IMAGE = DEVELOPER


@requires(PRODUCTION)
class ProductionImageMux(MuxCase, unittest.TestCase):
    IMAGE = PRODUCTION


if __name__ == "__main__":
    unittest.main()
