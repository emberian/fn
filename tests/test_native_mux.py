"""SCN-153: served connections on the I/O loops, and the capacity against memory.

Lane connection-multiplexing (2026-09-26; PKT-605; HST-024; PRF-223).  Over
each image (developer and production):

1. A capacity the memory cannot hold is bounded by name at `run`: the run's
   capacity is the memory gate's C' (books/admission-memory.lisp
   fn-adm-capacity; PRF-223's statement since L-RUN-LAUNCH), the service
   log's line `memory capacity=C' of C bound-by=TERM ...` names it below the
   configured C, and the run serves.
2. Under a capacity it holds, the service log names it (`memory
   capacity=C' of C bound-by=configured`), 300 held connections add no
   thread (the loops serve them; the worker-per-connection host added 300),
   each costs the node less than 64 KiB of resident memory at rest, and
   every one of them is served (a GROUP on each).
3. A live raise the memory gate does not hold is refused by name
   (`connections-exceed-memory`, host/owner-host.lisp
   fn-owner-memory-candidate-refusal) and changes nothing; a raise it holds
   is published, the capacity recomputed (fn-owner-memory-recapacity), and
   is then exactly what is admitted (the busy 400 after it).

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
MEMORY = re.compile(rb"memory capacity=(\d+) of (\d+) bound-by=(\S+)")
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

    def test_a_capacity_the_memory_cannot_hold_is_bounded_at_start(self):
        self.policy(4000000)
        self.node.start()
        found = MEMORY.search(self.log.read_bytes())
        self.assertIsNotNone(found, self.log.read_bytes()[-2000:])
        held, configured, term = int(found.group(1)), int(found.group(2)), found.group(3)
        self.assertEqual(configured, 4000000)
        self.assertGreater(held, 0)
        self.assertLess(held, configured)
        self.assertNotEqual(term, b"configured")
        sock, line = self.open_one()
        sock.close()
        self.assertTrue(line.startswith(b"20"), line)

    def test_connections_cost_no_thread_and_the_bound_is_kept_live(self):
        self.policy(HELD + 20)
        owner = self.node.start()
        log = self.log.read_bytes()
        found = MEMORY.search(log)
        self.assertIsNotNone(found, log[-2000:])
        holds = int(found.group(1))
        self.assertEqual((holds, int(found.group(2)), found.group(3)),
                         (HELD + 20, HELD + 20, b"configured"))
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
        print("NATIVE-MUX capacity={} threads={}->{} "
              "rss={}->{} kB rss-per-connection={:.1f} kB".format(
                  holds, threads_before, threads_after, rss_before, rss_after,
                  per_connection))
        self.assertLess(per_connection, 64, (rss_before, rss_after))
        # Every held connection is served.
        for sock in self.held:
            sock.sendall(b"GROUP fn.test\r\n")
        for sock in self.held:
            self.assertTrue(first_line(sock).startswith(b"211 "))

        # A live raise the memory gate does not hold is refused by name and
        # changes nothing.
        refused = self.policy(4000000, expected=None)
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
