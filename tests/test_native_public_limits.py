"""SCN-142: the reader port holds exactly the operator's connection capacity.

The native gate of PRF-211 (books/public-exposure.lisp,
fn-exp-open-refuses-exactly-at-the-capacity and the trusted-range
keystones), on the developer image and the production image alike.  One
owner on 127.0.0.1 per image:

1. `policy set exposure-connections 40` before the start (above the 31 every
   run was held to before PRF-211): 40 connections are admitted and the 41st
   reads `400 too many connections; try again later` and is closed.
2. `policy set exposure-connections 45` LIVE: five more are admitted and the
   46th reads the same 400.
3. `health` and `status` print `exposure capacity connections=N capacity=C
   per-address=P trusted=W`.
4. With every connection closed, `exposure-per-address 2` and
   `exposure-trusted 127.0.2.0/24` LIVE: six connections from 127.0.2.9 are
   all admitted; from 127.0.3.9 two are admitted and the third reads `400 too
   many connections from this address; try again later`.

Strangers are other loopback source addresses (127.0.0.0/8 routes to lo on
Linux).  Run on hbox:
    tools/hbox_native.sh --images developer,production . tests.test_native_public_limits
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import socket
import time
import unittest

from tests.native_harness import EXIT, Node, native_image, requires

PRODUCTION = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
BUSY = b"400 too many connections; try again later\r\n"
ADDRESS = b"400 too many connections from this address; try again later\r\n"
CAPACITY = re.compile(
    r"^exposure capacity connections=(\d+) capacity=(\d+) per-address=(\d+) trusted=(\S+)$",
    re.M)


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


def closed_after(sock, timeout=10):
    """True when the server closed the connection (EOF or reset)."""
    sock.settimeout(timeout)
    try:
        return sock.recv(1) == b""
    except (ConnectionResetError, BrokenPipeError):
        return True
    except socket.timeout:
        return False


class PublicLimitsCase:
    """The campaign, over one image (IMAGE set by the subclass).  The held
    connections are raw sockets: their count is the subject."""

    IMAGE = None

    def setUp(self):
        self.node = Node(self, self.IMAGE)
        self.base, self.port, self.config = self.node.root, self.node.port, self.node.config
        self.held = []
        self.addCleanup(self.stop)

    def policy(self, slot, value):
        self.node.operator("policy", "set", slot, value, expect=EXIT.OK)

    def report(self, verb):
        result = self.node.operator(verb)
        text = result.stdout.decode("ascii", "replace")
        found = CAPACITY.findall(text)
        self.assertEqual(len(found), 1, (verb, result.returncode, text,
                                         result.stderr.decode("ascii", "replace")))
        connections, capacity, per_address, trusted = found[0]
        return int(connections), int(capacity), int(per_address), trusted

    def stop(self):
        for sock in self.held:
            sock.close()
        process = self.node.process
        if process is not None:
            self.node.stop(expect=None)
        evidence = os.environ.get("FN_LIMITS_EVIDENCE")
        if evidence:
            target = Path(evidence) / self.__class__.__name__
            target.mkdir(parents=True, exist_ok=True)
            source = self.base / "fn.log"
            if source.exists():
                (target / "fn.log").write_bytes(source.read_bytes())
            if process is not None:
                (target / "stderr.log").write_bytes(process.stderr.since(0))

    def open_from(self, source):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=30,
                                        source_address=(source, 0))
        return sock, first_line(sock)

    def admit(self, source, count):
        for _ in range(count):
            sock, line = self.open_from(source)
            self.assertTrue(line.startswith(b"200 ") or line.startswith(b"201 "),
                            (source, len(self.held), line))
            self.held.append(sock)

    def refused(self, source, expected_line):
        sock, line = self.open_from(source)
        try:
            self.assertEqual(line, expected_line, (source, len(self.held)))
            self.assertTrue(closed_after(sock), "the refused connection stayed open")
        finally:
            sock.close()

    def release_all(self):
        for sock in self.held:
            sock.close()
        self.held = []
        deadline = time.monotonic() + 60
        while time.monotonic() < deadline:
            if self.report("health")[0] == 0:
                return
            time.sleep(0.5)
        self.fail("the owner still holds connections 60 s after they closed")

    def test_capacity_and_trusted_range(self):
        self.node.store("init", "fn.test", expect=EXIT.OK)
        self.node.write_config(extra='[log]\npath = "{}"\n'
                               '[auth]\nrequired = false\nprotected_only = false\npath = "{}"\n'
                               .format(self.base / "fn.log", self.base / "auth.toml"))
        self.policy("exposure-connections", "40")
        process = self.node.start()

        # 1. Exactly the capacity, then the named 400.
        self.assertEqual(self.report("status")[:2], (0, 40))
        self.admit("127.0.0.1", 40)
        self.refused("127.0.0.1", BUSY)
        self.assertEqual(self.report("health"), (40, 40, 40, "none"))

        # 2. Raised live: five more, then the 400 again.
        self.policy("exposure-connections", "45")
        self.admit("127.0.0.1", 5)
        self.refused("127.0.0.1", BUSY)
        self.assertEqual(self.report("status")[:2], (45, 45))
        self.assertIsNone(process.poll(), "the owner exited")

        # 4. The trusted range, live.
        self.release_all()
        self.policy("exposure-per-address", "2")
        self.policy("exposure-trusted", "127.0.2.0/24")
        self.admit("127.0.2.9", 6)
        self.admit("127.0.3.9", 2)
        self.refused("127.0.3.9", ADDRESS)
        self.assertEqual(self.report("health"), (8, 45, 2, "127.0.2.0/24"))
        # A malformed range is refused by the operator and changes nothing.
        bad = self.node.operator("policy", "set", "exposure-trusted", "127.0.2.0/33")
        self.assertNotEqual(bad.returncode, 0, bad)
        self.assertEqual(self.report("status")[3], "127.0.2.0/24")
        self.assertIsNone(process.poll(), "the owner exited")


@requires(DEVELOPER)
class DeveloperImagePublicLimits(PublicLimitsCase, unittest.TestCase):
    IMAGE = DEVELOPER


@requires(PRODUCTION)
class ProductionImagePublicLimits(PublicLimitsCase, unittest.TestCase):
    IMAGE = PRODUCTION


if __name__ == "__main__":
    unittest.main()
