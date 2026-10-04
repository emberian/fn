#!/usr/bin/env python3
"""SCN-1141 (PRF-1327): the TLS key exchange is a decided policy.

`[tls] key_exchange = hybrid-preferred | hybrid-required`
(books/tls-key-exchange.lisp).  The node sets its server contexts' groups to
X25519MLKEM768 first and the classical groups after it when its OpenSSL
(FN_OPENSSL_PREFIX, by default the shipped 3.5.8) knows the hybrid group:

  * under hybrid-preferred `openssl s_client -starttls nntp -groups
    X25519MLKEM768` negotiates it, a classical-only client still connects,
    the service log names each session's group, and `status` and `health`
    end with the tallies;
  * under hybrid-required a node whose library cannot offer the hybrid group
    (a prefix of the system's 3.0 to 3.4 pair) is refused by name at `run`,
    before it listens; under hybrid-preferred the same library serves
    classical groups;
  * a missing OpenSSL prefix, and an unknown policy word, are refused by name.

Needs the OpenSSL 3.5.8 toolchain (FN_TEST_OPENSSL_PREFIX, default
/tank/fn/toolchains/openssl-3.5.8) for the client and the node's library.
"""

from __future__ import annotations

import ctypes.util
import os
import re
import subprocess
import time
import unittest
from pathlib import Path

from tests.native_harness import EXIT, ROOT, Node, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST")
PREFIX = Path(os.environ.get("FN_TEST_OPENSSL_PREFIX", "/tank/fn/toolchains/openssl-3.5.8"))
CLIENT = PREFIX / "bin" / "openssl"
HYBRID = "X25519MLKEM768"


def have_toolchain() -> bool:
    return CLIENT.exists() and (PREFIX / "lib" / "libssl.so.3").exists()


def client_environment() -> dict:
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = str(PREFIX / "lib")
    return env


def system_prefix(root: Path) -> Path | None:
    """A prefix of the system's libcrypto/libssl pair (no ML-KEM before 3.5)."""
    pair = []
    for name in ("crypto", "ssl"):
        found = ctypes.util.find_library(name)
        if not found:
            return None
        for directory in ("/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu", "/lib64",
                          "/usr/lib64", "/usr/lib", "/lib"):
            path = Path(directory) / ("lib{}.so.3".format(name))
            if path.exists():
                pair.append(path)
                break
        else:
            return None
    prefix = root / "system-openssl"
    (prefix / "lib").mkdir(parents=True)
    for path in pair:
        (prefix / "lib" / path.name).symlink_to(path)
    return prefix


def system_openssl_has_hybrid(prefix: Path) -> bool:
    """Whether the symlinked system pair knows X25519MLKEM768 (3.5+): then the
    refusal under hybrid-required cannot be exercised on this box."""
    result = subprocess.run(["openssl", "list", "-kem-algorithms"], capture_output=True, text=True)
    return "MLKEM" in result.stdout


@unittest.skipUnless(have_toolchain(), "OpenSSL 3.5.8 toolchain required: {}".format(PREFIX))
@requires(IMAGE)
class NativeTlsKeyExchangeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.node = Node(self, IMAGE, env={"FN_OPENSSL_PREFIX": str(PREFIX)})
        self.root, self.port = self.node.root, self.node.port
        self.node.store("init", "fn.test", expect=EXIT.OK)
        self.certificate = self.root / "server-certificate.pem"
        self.private_key = self.root / "server-private-key.pem"
        subprocess.run(
            [str(CLIENT), "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(self.private_key),
             "-out", str(self.certificate), "-sha256", "-days", "1", "-nodes",
             "-subj", "/CN=localhost"],
            cwd=ROOT, env=client_environment(), stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL, timeout=60, check=True)
        self.log = self.root / "fn.log"

    def configure(self, key_exchange: str | None) -> None:
        self.node.write_config(
            extra='tls_cert = "{}"\ntls_key = "{}"\n'.format(self.certificate, self.private_key),
            tls=('key_exchange = "{}"\n'.format(key_exchange) if key_exchange else None),
            protected_only=True)
        with self.node.config.open("a", encoding="utf-8") as handle:
            handle.write('\n[log]\npath = "{}"\n'.format(self.log))

    def s_client(self, groups: str, commands: bytes = b"DATE\r\nQUIT\r\n") -> str:
        """`openssl s_client -starttls nntp -groups GROUPS`, the 3.5.8 tool."""
        result = subprocess.run(
            [str(CLIENT), "s_client", "-starttls", "nntp", "-groups", groups,
             "-connect", "127.0.0.1:{}".format(self.port), "-servername", "localhost",
             "-brief"],
            input=commands, env=client_environment(), capture_output=True, timeout=60)
        return (result.stdout + result.stderr).decode("utf-8", "replace")

    def wait_for_log(self, pattern: str, timeout: float = 15) -> str:
        deadline = time.monotonic() + timeout
        text = ""
        while time.monotonic() < deadline:
            text = self.log.read_text(errors="replace") if self.log.exists() else ""
            if re.search(pattern, text):
                return text
            time.sleep(0.2)
        self.fail("the service log never matched {!r}: {}".format(pattern, text[-2000:]))

    def test_preferred_negotiates_the_hybrid_and_serves_classical_readers(self) -> None:
        self.configure("hybrid-preferred")
        process = self.node.start()
        try:
            hybrid = self.s_client(HYBRID)
            self.assertIn("Negotiated TLS1.3 group: {}".format(HYBRID), hybrid, hybrid)
            self.assertIn("111 ", hybrid, "the hybrid session answered no DATE: " + hybrid)
            classical = self.s_client("X25519")
            self.assertIn("Negotiated TLS1.3 group: X25519", classical, classical)
            self.assertNotIn(HYBRID, classical.replace("Negotiated TLS1.3 group: X25519", ""))
            self.assertIn("111 ", classical, "the classical session answered no DATE: " + classical)
            # The service log names each session's group (ACL2's line).
            text = self.wait_for_log(r"tls established group=X25519\b")
            self.assertIn("tls established group={}".format(HYBRID), text)
            # status and health end with the tallies, the policy and the groups served.
            status = self.node.operator("status")
            self.assertRegex(status.stdout.decode(),
                             r"tls key-exchange policy=hybrid-preferred serving=hybrid "
                             r"hybrid=1 classical=1 unknown=0")
            health = self.node.operator("health")
            self.assertRegex(health.stdout.decode(),
                             r"tls key-exchange policy=hybrid-preferred serving=hybrid "
                             r"hybrid=1 classical=1 unknown=0")
            self.assertIsNone(process.poll(), "a client stopped the owner")
        finally:
            self.node.stop(expect=None, process=process, grace=20)

    def test_required_serves_the_hybrid_with_a_library_that_offers_it(self) -> None:
        self.configure("hybrid-required")
        process = self.node.start()
        try:
            self.assertIn("Negotiated TLS1.3 group: {}".format(HYBRID), self.s_client(HYBRID))
            status = self.node.operator("status")
            self.assertIn("tls key-exchange policy=hybrid-required serving=hybrid hybrid=1",
                          status.stdout.decode())
        finally:
            self.node.stop(expect=None, process=process, grace=20)

    def test_required_is_refused_by_name_with_a_library_that_cannot_offer_it(self) -> None:
        prefix = system_prefix(self.root)
        if prefix is None or system_openssl_has_hybrid(prefix):
            self.skipTest("the system's OpenSSL pair offers ML-KEM (or cannot be found)")
        self.node.env["FN_OPENSSL_PREFIX"] = str(prefix)
        self.configure("hybrid-required")
        result = self.node.operator("run", "--once")
        self.assertEqual(result.returncode, EXIT.REFUSED, result.stderr.decode())
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"tls key-exchange hybrid-required", result.stderr)
        self.assertIn(b"X25519MLKEM768", result.stderr)

    def test_preferred_serves_classical_groups_with_a_library_that_cannot_offer_it(self) -> None:
        prefix = system_prefix(self.root)
        if prefix is None or system_openssl_has_hybrid(prefix):
            self.skipTest("the system's OpenSSL pair offers ML-KEM (or cannot be found)")
        self.node.env["FN_OPENSSL_PREFIX"] = str(prefix)
        self.configure("hybrid-preferred")
        process = self.node.start()
        try:
            self.assertIn("111 ", self.s_client("X25519"))
            # A client that insists on the hybrid group alone cannot connect.
            self.assertNotIn("111 ", self.s_client(HYBRID))
            status = self.node.operator("status")
            self.assertIn("tls key-exchange policy=hybrid-preferred serving=classical hybrid=0",
                          status.stdout.decode())
        finally:
            self.node.stop(expect=None, process=process, grace=20)

    def test_a_missing_openssl_prefix_is_refused_by_name(self) -> None:
        self.node.env["FN_OPENSSL_PREFIX"] = str(self.root / "no-such-openssl")
        self.configure(None)
        result = self.node.operator("run", "--once")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn(b"LISTENING ", result.stdout)
        self.assertIn(b"no OpenSSL libcrypto/libssl pair under", result.stderr)
        self.assertIn(str(self.root / "no-such-openssl").encode(), result.stderr)

    def test_an_unknown_policy_word_is_refused(self) -> None:
        self.configure("classical")
        result = self.node.operator("run", "--once")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn(b"LISTENING ", result.stdout)


if __name__ == "__main__":
    unittest.main()
