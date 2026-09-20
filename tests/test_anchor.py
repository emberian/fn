"""The external freshness anchor: the client, the seam, and the restore rule.

Every vector under `tests/vectors/` is a real Roughtime response captured from
roughtime.int08h.com:2002 on 2026-09-19, so these tests need no network.  They
do need Ed25519: `cryptography` is an optional dependency and every test that
needs it skips with its reason when it is absent.  Nothing here treats a
missing library as a verified signature.
"""

import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import crypto_host, roughtime, run_store  # noqa: E402

VECTORS = ROOT / "tests" / "vectors"
PRIMARY = VECTORS / "roughtime-int08h-2026-09-19.json"
LATER1 = VECTORS / "roughtime-int08h-2026-09-19-later1.json"
LATER2 = VECTORS / "roughtime-int08h-2026-09-19-later2.json"

NEEDS_CRYPTO = unittest.skipUnless(
    crypto_host.available(), crypto_host.unavailable_reason() or "")


def captured(path):
    return json.loads(Path(path).read_bytes())


def reparse(record, packet=None, key=None):
    return roughtime.parse_response(
        packet if packet is not None else bytes.fromhex(record["response_hex"]),
        bytes.fromhex(record["nonce_hex"]),
        key if key is not None else bytes.fromhex(record["key_id_hex"]),
        record["server"])


class CryptoSeam(unittest.TestCase):
    def test_absent_library_is_not_a_verdict(self):
        """Whatever the environment, no path answers True without Ed25519."""
        if crypto_host.available():
            self.assertTrue(isinstance(crypto_host.verify(b"", b"", b""), bool))
            self.assertFalse(crypto_host.verify(b"", b"m", b""))
        else:
            with self.assertRaises(crypto_host.CryptoUnavailable):
                crypto_host.verify(b"\x00" * 32, b"m", b"\x00" * 64)

    def test_no_other_module_imports_cryptography(self):
        """`tools/crypto_host.py` is the only importer of `cryptography`."""
        offenders = []
        for path in sorted((ROOT / "tools").glob("*.py")):
            if path.name == "crypto_host.py":
                continue
            if "cryptography" in path.read_text():
                offenders.append(path.name)
        self.assertEqual(offenders, [])

    @NEEDS_CRYPTO
    def test_round_trip_and_rejection(self):
        private, public = crypto_host.generate_keypair()
        signature = crypto_host.sign(private, b"anchor")
        self.assertTrue(crypto_host.verify(public, b"anchor", signature))
        self.assertFalse(crypto_host.verify(public, b"anchoR", signature))
        self.assertFalse(crypto_host.verify(public, b"anchor", signature[:-1]))


class RoughtimeClient(unittest.TestCase):
    @NEEDS_CRYPTO
    def test_captured_response_verifies_under_the_pinned_key(self):
        record = captured(PRIMARY)
        anchor = reparse(record)
        self.assertEqual(anchor.midpoint, record["midpoint_us"])
        self.assertEqual(anchor.radius, record["radius_us"])
        self.assertEqual(len(anchor.signature), 64)
        self.assertEqual(len(anchor.delegation_signature), 64)
        self.assertEqual(len(anchor.dele), 72)
        self.assertEqual(len(anchor.srep), 100)

    @NEEDS_CRYPTO
    def test_pinned_key_is_the_one_in_the_server_file(self):
        servers = roughtime.load_servers()
        import base64
        self.assertEqual(
            base64.b64decode(servers["int08h"]["public_key_base64"]).hex(),
            captured(PRIMARY)["key_id_hex"])

    @NEEDS_CRYPTO
    def test_a_different_pinned_key_does_not_verify(self):
        record = captured(PRIMARY)
        wrong = b"\xc8" + bytes.fromhex(record["key_id_hex"])[1:]
        with self.assertRaises(roughtime.RoughtimeError):
            reparse(record, key=wrong)

    @NEEDS_CRYPTO
    def test_one_flipped_octet_breaks_the_response(self):
        record = captured(PRIMARY)
        packet = bytearray(bytes.fromhex(record["response_hex"]))
        packet[-1] ^= 0x01
        with self.assertRaises(roughtime.RoughtimeError):
            reparse(record, packet=bytes(packet))

    @NEEDS_CRYPTO
    def test_a_foreign_nonce_is_not_in_the_tree(self):
        """The Merkle proof is what binds the response to this client."""
        record = captured(PRIMARY)
        foreign = dict(record, nonce_hex=(b"\x00" * 32).hex())
        with self.assertRaises(roughtime.RoughtimeError):
            reparse(foreign)

    def test_merkle_root_folds_the_path(self):
        record = captured(PRIMARY)
        nonce = bytes.fromhex(record["nonce_hex"])
        top = roughtime.decode_message(bytes.fromhex(record["response_hex"]))
        index = int.from_bytes(top[b"INDX"], "little")
        self.assertEqual(
            roughtime.merkle_root(nonce, top[b"PATH"], index),
            bytes.fromhex(record["root_hex"]))

    def test_request_is_padded_to_the_minimum(self):
        packet = roughtime.request_packet(b"\x11" * 32)
        self.assertGreaterEqual(len(packet), roughtime.MIN_REQUEST_OCTETS)
        self.assertEqual(roughtime.decode_message(packet)[b"NONC"], b"\x11" * 32)


class Acl2OwnsTheSignedOctets(unittest.TestCase):
    """ACL2 rebuilds both signed messages; the wire must agree octet for octet."""

    @classmethod
    def setUpClass(cls):
        cls.bridge = run_store.Acl2Store()

    @classmethod
    def tearDownClass(cls):
        cls.bridge.close()

    @NEEDS_CRYPTO
    def test_reconstruction_matches_the_captured_response(self):
        anchor = reparse(captured(PRIMARY))
        signed = self.bridge.anchor_signed_octets(
            anchor.radius, anchor.midpoint, anchor.root)
        self.assertEqual(signed, roughtime.RESPONSE_CONTEXT + anchor.srep)
        delegation = self.bridge.anchor_delegation_octets(anchor.fields())
        self.assertEqual(delegation, roughtime.DELEGATION_CONTEXT + anchor.dele)

    @NEEDS_CRYPTO
    def test_the_verdict_is_over_the_octets_acl2_produced(self):
        anchor = reparse(captured(PRIMARY))
        self.assertTrue(run_store.anchor_verdict(self.bridge, anchor))

    @NEEDS_CRYPTO
    def test_the_model_orders_the_three_captures(self):
        fields = [reparse(captured(path)).fields()
                  for path in (PRIMARY, LATER1, LATER2)]
        pinned = run_store.pinned_keys()
        # A node holding the primary accepts a later capture ...
        status, _ = self.bridge.anchor_accept(pinned, fields[0], 0, fields[1], True)
        self.assertEqual(status, "accepted")
        # ... and refuses the primary replayed back at it.
        status, reason = self.bridge.anchor_accept(pinned, fields[1], 0, fields[0], True)
        self.assertEqual((status, reason), ("refused", "stale"))
        # A failed Ed25519 check is its own refusal, never an accept.
        status, reason = self.bridge.anchor_accept(pinned, fields[0], 0, fields[1], False)
        self.assertEqual((status, reason), ("refused", "unverified"))
        # No anchor at all stays uncertain.
        status, _ = self.bridge.anchor_accept(pinned, fields[0], 0, None, True)
        self.assertEqual(status, "uncertain")


class StoreAnchorCommands(unittest.TestCase):
    """`run_store.py anchor` and `recover`, over real captured responses."""

    def store_command(self, root, *arguments):
        completed = subprocess.run(
            [sys.executable, str(ROOT / "tools" / "run_store.py"),
             "--store", str(root)] + list(arguments),
            cwd=str(ROOT), capture_output=True, text=True)
        return completed.returncode, completed.stdout + completed.stderr

    def initialized(self):
        import tempfile
        root = Path(tempfile.mkdtemp(prefix="fn-anchor-")) / "store"
        code, output = self.store_command(root, "init")
        self.assertEqual(code, run_store.EXIT_OK, output)
        return root

    @NEEDS_CRYPTO
    def test_anchor_records_then_refuses_a_replay(self):
        root = self.initialized()
        code, output = self.store_command(root, "anchor", "--anchor-vector", str(PRIMARY))
        self.assertEqual(code, run_store.EXIT_OK, output)
        self.assertIn("anchor accepted", output)
        self.assertTrue((root / "anchor.fnan").is_file())
        # The same response again is not strictly newer than itself.
        code, output = self.store_command(root, "anchor", "--anchor-vector", str(PRIMARY))
        self.assertEqual(code, run_store.EXIT_REFUSED, output)
        self.assertIn("stale", output)
        # A genuinely later one advances the durable anchor.
        code, output = self.store_command(root, "anchor", "--anchor-vector", str(LATER1))
        self.assertEqual(code, run_store.EXIT_OK, output)

    @NEEDS_CRYPTO
    def test_restoring_an_older_snapshot_is_refused(self):
        """FLR-003: the image is intact and every checksum matches."""
        root = self.initialized()
        code, output = self.store_command(root, "anchor", "--anchor-vector", str(LATER1))
        self.assertEqual(code, run_store.EXIT_OK, output)
        code, output = self.store_command(
            root, "recover", "--anchor-vector", str(PRIMARY))
        self.assertEqual(code, run_store.EXIT_REFUSED, output)
        self.assertIn("anchor=refused:possibly-stale", output)

    @NEEDS_CRYPTO
    def test_restoring_with_a_fresh_anchor_succeeds(self):
        root = self.initialized()
        code, output = self.store_command(root, "anchor", "--anchor-vector", str(LATER1))
        self.assertEqual(code, run_store.EXIT_OK, output)
        code, output = self.store_command(
            root, "recover", "--anchor-vector", str(LATER2))
        self.assertEqual(code, run_store.EXIT_OK, output)
        self.assertIn("anchor=accepted incarnation=1", output)

    @NEEDS_CRYPTO
    def test_no_anchor_obtainable_is_uncertain_not_refused(self):
        root = self.initialized()
        code, output = self.store_command(root, "anchor", "--anchor-vector", str(LATER1))
        self.assertEqual(code, run_store.EXIT_OK, output)
        missing = str(VECTORS / "does-not-exist.json")
        code, output = self.store_command(root, "recover", "--anchor-vector", missing)
        self.assertEqual(code, run_store.EXIT_UNCERTAIN, output)
        self.assertIn("anchor=uncertain", output)

    def test_a_store_that_never_anchored_recovers_as_before(self):
        root = self.initialized()
        code, output = self.store_command(root, "recover")
        self.assertEqual(code, run_store.EXIT_OK, output)
        self.assertIn("anchor=none", output)


if __name__ == "__main__":
    unittest.main()
