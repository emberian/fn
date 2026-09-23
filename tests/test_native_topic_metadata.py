#!/usr/bin/env python3
"""Source-matched saved-image CLI gate for exact signed FN-Topic projection.

The field vectors below are exact ACL2 `fn-th-field-encode` results for the
root and a zero-parent report. Python does not encode them.
"""
import os
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
TOPIC_FIELD = (
    b"v1 AQBYIAEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBWCAHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHB1gwZm4vc3ViamVjdC92MQABAQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFRG1pbmkBWCAHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHBwcHB1gwZm4vc3ViamVjdC92MQABAQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUF"
)
SHORT_TOPIC_FIELD = (
    b"v1 AQJYMGZuL3N1YmplY3QvdjEAAQEFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBVgwZm4vc3ViamVjdC92MQABAQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFAA=="
)
MAX_FIELD = ROOT / "tests" / "fixtures" / "topic-history" / "max-root-field.bin"
MAX_FIELD_SHA256 = "8b9aeeb3311f313d5b0826f105faaa05e93f398017451442ed7c128d04584851"


@unittest.skipUnless(os.environ.get("FN_RUN_TOPIC_METADATA_E2E") == "1",
                     "set FN_RUN_TOPIC_METADATA_E2E=1 for the source-matched native gate")
@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "a freshly built native image is required")
class NativeTopicMetadataTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-topic-metadata-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.principal = self.root / "principal.bin"
        self.ed_public = self.root / "ed-public.bin"
        self.ed_secret = self.root / "ed-secret.bin"
        self.ml_public = self.root / "ml-public.pem"
        self.ml_private = self.root / "ml-private.pem"
        self.principal.write_bytes(bytes([85]) * 32)
        self.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        made = subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65",
                               "-out", str(self.ml_private)], capture_output=True,
                              timeout=60, check=False)
        self.assertEqual(made.returncode, 0, made.stderr.decode("utf-8", "replace"))
        subprocess.run([OPENSSL, "pkey", "-in", str(self.ml_private), "-pubout",
                        "-out", str(self.ml_public)], timeout=60, check=True)

    def invoke(self, *args):
        return subprocess.run([str(IMAGE), "--fn", *args], cwd=ROOT,
                              capture_output=True, timeout=60, check=False)

    def sign(self, name, source):
        source_path = self.root / (name + ".source")
        carrier_path = self.root / (name + ".carrier")
        source_path.write_bytes(source)
        signed = self.invoke("hybrid-sign-carrier", str(self.principal),
                             str(self.ed_public), str(self.ed_secret),
                             str(self.ml_public), str(self.ml_private),
                             str(source_path), str(carrier_path))
        self.assertEqual(signed.returncode, 0, signed.stderr.decode("utf-8", "replace"))
        return carrier_path

    def source(self, fields):
        return (b"From: author@example.invalid\r\n"
                b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                b"Newsgroups: fn.test\r\nSubject: topic\r\n"
                b"Message-ID: <topic@example.invalid>\r\n" + fields +
                b"\r\nexact signed source\r\n")

    def test_signed_source_candidate_and_relay(self):
        field = b"FN-Topic: " + TOPIC_FIELD + b"\r\n"
        source = self.source(field)
        carried = self.sign("root", source)
        self.assertTrue(carried.read_bytes().endswith(source))
        inspected = self.invoke("topic-inspect-carrier", str(carried), str(self.ml_public))
        self.assertEqual(inspected.returncode, 0, inspected.stderr.decode("utf-8", "replace"))
        self.assertIn(b"topic=candidate carrier=authenticated kind=root", inspected.stdout)
        self.assertIn(b"author-principal=" + b"55" * 32, inspected.stdout)
        self.assertIn(b"binding=controller-mismatch", inspected.stdout)
        self.assertIn(b"admission=unestablished", inspected.stdout)
        relayed = self.root / "relayed.eml"
        relayed.write_bytes(b"Path: relay.example!fn\r\n"
                            b"Xref: relay.example fn.test:7\r\n" + carried.read_bytes())
        again = self.invoke("topic-inspect-carrier", str(relayed), str(self.ml_public))
        self.assertEqual(again.returncode, 0, again.stderr.decode("utf-8", "replace"))
        self.assertEqual(again.stdout, inspected.stdout)
        tampered = self.root / "tampered.eml"
        tampered.write_bytes(carried.read_bytes().replace(b"exact signed source",
                                                        b"alter signed source", 1))
        refused = self.invoke("topic-inspect-carrier", str(tampered), str(self.ml_public))
        self.assertEqual(refused.returncode, 1)
        self.assertIn(b"topic=unverified", refused.stdout)
        # This shorter valid report field is an exact ACL2-emitted vector.
        # This exact ACL2 vector also fits the older frozen image's 8,192-octet
        # header cap; two large root fields could not reach its inspector.
        short_field = b"FN-Topic: " + SHORT_TOPIC_FIELD + b"\r\n"
        duplicate = self.sign("duplicate", self.source(short_field + short_field))
        unsupported = self.invoke("topic-inspect-carrier", str(duplicate),
                                  str(self.ml_public))
        self.assertEqual(unsupported.returncode, 1)
        self.assertIn(b"TOPIC=UNSUPPORTED CARRIER=AUTHENTICATED REASON=DUPLICATE",
                      unsupported.stdout.upper())
        malformed = self.sign("malformed", self.source(b"FN-Topic: v1 AAAA\r\n"))
        unsupported = self.invoke("topic-inspect-carrier", str(malformed),
                                  str(self.ml_public))
        self.assertEqual(unsupported.returncode, 1)
        self.assertIn(b"topic=unsupported", unsupported.stdout)

    def test_max_roster_folded_source_and_relay(self):
        field = MAX_FIELD.read_bytes()
        self.assertEqual(len(field), 2143)
        self.assertEqual(hashlib.sha256(field).hexdigest(), MAX_FIELD_SHA256)
        source = self.source(field)
        carried = self.sign("max-root", source)
        self.assertTrue(carried.read_bytes().endswith(source))
        inspected = self.invoke("topic-inspect-carrier", str(carried), str(self.ml_public))
        self.assertEqual(inspected.returncode, 0, inspected.stderr.decode("utf-8", "replace"))
        self.assertIn(b"topic=candidate carrier=authenticated kind=root", inspected.stdout)
        self.assertIn(b"admission=unestablished", inspected.stdout)
        relayed = self.root / "max-relayed.eml"
        relayed.write_bytes(b"Path: relay.example!fn\r\n"
                            b"Xref: relay.example fn.test:8\r\n" + carried.read_bytes())
        again = self.invoke("topic-inspect-carrier", str(relayed), str(self.ml_public))
        self.assertEqual(again.returncode, 0, again.stderr.decode("utf-8", "replace"))
        self.assertEqual(again.stdout, inspected.stdout)
        tampered = self.root / "max-tampered.eml"
        tampered.write_bytes(carried.read_bytes().replace(b"exact signed source",
                                                        b"alter signed source", 1))
        refused = self.invoke("topic-inspect-carrier", str(tampered), str(self.ml_public))
        self.assertEqual(refused.returncode, 1)
        self.assertIn(b"topic=unverified", refused.stdout)


if __name__ == "__main__":
    unittest.main()
