#!/usr/bin/env python3
"""pub/sub as a declaration (D50): `fn pattern pubsub pub|sub' on one node.

One publisher posts three payloads (empty, five octets, 114 octets: two full
base64 lines) to one group through `fn pattern pubsub pub', each as article
kind `opaque' v1 signed with the hybrid profile and authored over the control
socket; the owner restarts between the second and the third.  A subscriber,
`fn pattern pubsub sub ... --count 3', receives exactly the three payloads,
in order, as files, and acks each after its file.  A rerun of the third
publication over the same SPOOL resends the same signed request (stored
already: exit 0) and the subscriber then finds nothing new.  A spool reused
for another payload is refused by name.

Red before: the image has no `pattern' verb.

The pipeline case (push/pull with a fixed worker set): six pushes, three
pull workers; each message delivered by exactly the worker of its partition.

Opt-in: FN_RUN_HYBRID_E2E=1 (the hybrid-signature saved-image gate this
rides on; hbox_native.sh sets it) and FN_NATIVE_HOST naming a
source-matched image; OpenSSL 3.5 for ML-DSA-65 (FN_TEST_OPENSSL).
"""
import os
from pathlib import Path
import re
import subprocess
import unittest

from tests.native_harness import Node, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST")
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
GROUP = "fn.test"
FROM = "pub <pub@example.invalid>"
PAYLOADS = [b"", b"hello", bytes(range(114))]


@unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                     "set FN_RUN_HYBRID_E2E=1 and a source-matched FN_NATIVE_HOST")
@requires(IMAGE)
class NativePatternPubSubTest(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE)
        self.root, self.control = self.node.root, str(self.node.control)
        initialized = self.node.invoke("store", str(self.node.store_path), "init", GROUP,
                                       timeout=180)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.keys = self.root / "keys"
        self.keys.mkdir()
        (self.keys / "principal").write_bytes(bytes([85]) * 32)
        (self.keys / "ed-public").write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        (self.keys / "ed-secret").write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ml_private, ml_public = self.keys / "ml-private.pem", self.keys / "ml-public.pem"
        generated = subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65",
                                    "-out", str(ml_private)],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   timeout=60, check=False)
        self.assertEqual(generated.returncode, 0, generated.stderr.decode("utf-8", "replace"))
        subprocess.run([OPENSSL, "pkey", "-in", str(ml_private), "-pubout",
                        "-out", str(ml_public)], timeout=60, check=True)
        self.out = self.root / "delivered"
        self.out.mkdir()

    def fn(self, *words, timeout=300):
        return self.node.invoke(*[str(w) for w in words], timeout=timeout)

    def publish(self, index, payload_file=None):
        payload = payload_file or (self.root / ("payload-%d" % index))
        if payload_file is None:
            payload.write_bytes(PAYLOADS[index])
        return self.fn("pattern", "pubsub", "pub", self.control, "1", self.keys, GROUP,
                       FROM, "<p%d.pattern@example.invalid>" % index, payload,
                       self.root / ("spool-%d" % index))

    def subscribe(self, *options):
        return self.fn("pattern", "pubsub", "sub", self.control, "subscriber", GROUP,
                       self.out, *options)

    def test_three_payloads_in_order_across_an_owner_restart(self):
        owner = self.node.start()
        enrolled = self.fn("hybrid-enroll", self.control, "1", self.keys / "principal",
                           self.keys / "ed-public", self.keys / "ml-public.pem")
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        # The subscriber registers before anything is posted; registration
        # starts at position 0, so it would read the group from the start
        # either way.
        empty = self.subscribe("--timeout", "1")
        self.assertEqual(empty.returncode, 0, (empty.stdout + empty.stderr).decode())
        self.assertIn(b"pattern sub end delivered=0 timeout", empty.stdout)
        for index in (0, 1):
            posted = self.publish(index)
            self.assertEqual(posted.returncode, 0, (posted.stdout + posted.stderr).decode())
            self.assertRegex(posted.stdout, rb"pattern pub \S+ accepted")
        self.node.stop(process=owner)
        owner = self.node.start()
        posted = self.publish(2)
        self.assertEqual(posted.returncode, 0, (posted.stdout + posted.stderr).decode())

        got = self.subscribe("--count", "3", "--timeout", "30")
        self.assertEqual(got.returncode, 0, (got.stdout + got.stderr).decode())
        lines = re.findall(rb"pattern sub message (\d+) ([0-9a-f]+) (\d+) (\S+)", got.stdout)
        self.assertEqual(len(lines), 3, got.stdout)
        sequences = [int(line[0]) for line in lines]
        self.assertEqual(sequences, sorted(sequences))
        for index, (sequence, msgid, octets, path) in enumerate(lines):
            self.assertEqual(bytes.fromhex(msgid.decode()),
                             b"<p%d.pattern@example.invalid>" % index)
            self.assertEqual(int(octets), len(PAYLOADS[index]))
            self.assertEqual(Path(path.decode()).read_bytes(), PAYLOADS[index])
        self.assertEqual(sorted(p.name for p in self.out.iterdir()),
                         sorted(Path(line[3].decode()).name for line in lines))

        # The same SPOOL resends the same signed request: stored already.
        again = self.publish(2, payload_file=self.root / "payload-2")
        self.assertEqual(again.returncode, 0, (again.stdout + again.stderr).decode())
        nothing = self.subscribe("--timeout", "2")
        self.assertEqual(nothing.returncode, 0, (nothing.stdout + nothing.stderr).decode())
        self.assertIn(b"pattern sub end delivered=0 timeout", nothing.stdout)

        # A spool is one message: another payload over it is refused by name.
        other = self.root / "other"
        other.write_bytes(b"other")
        refused = self.fn("pattern", "pubsub", "pub", self.control, "1", self.keys, GROUP,
                          FROM, "<p2.pattern@example.invalid>", other, self.root / "spool-2")
        self.assertEqual(refused.returncode, 1, (refused.stdout + refused.stderr).decode())
        self.assertIn(b"pattern pub sign refused spool-conflict", refused.stdout)
        self.node.stop(process=owner)


    def test_pipeline_three_workers_partition_six_messages(self):
        """push/pull with a fixed worker set: six pushes, three pull workers;
        each message is delivered by exactly one worker, the one whose index
        is the FNV-1a of its Message-ID mod 3 (computed here independently),
        and every worker reads the whole queue (the others' messages as
        skips) to its end."""
        owner = self.node.start()
        enrolled = self.fn("hybrid-enroll", self.control, "1", self.keys / "principal",
                           self.keys / "ed-public", self.keys / "ml-public.pem")
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        msgids = [b"<j%d.pipeline@example.invalid>" % i for i in range(6)]
        for i, msgid in enumerate(msgids):
            payload = self.root / ("job-%d" % i)
            payload.write_bytes(b"job %d" % i)
            pushed = self.fn("pattern", "pipeline", "push", self.control, "1", self.keys,
                             GROUP, FROM, msgid.decode(), payload,
                             self.root / ("job-spool-%d" % i))
            self.assertEqual(pushed.returncode, 0, (pushed.stdout + pushed.stderr).decode())

        def fnv1a(octets):
            h = 2166136261
            for o in octets:
                h = ((h ^ o) * 16777619) % 4294967296
            return h

        seen = {}
        for index in range(3):
            out = self.root / ("worker-%d" % index)
            out.mkdir()
            got = self.fn("pattern", "pipeline", "pull", self.control, "worker-%d" % index,
                          str(index), "3", GROUP, out, "--timeout", "2")
            self.assertEqual(got.returncode, 0, (got.stdout + got.stderr).decode())
            delivered = re.findall(rb"pattern pull message \d+ ([0-9a-f]+) \d+ (\S+)", got.stdout)
            skipped = re.findall(rb"pattern pull skip ([0-9a-f]+)", got.stdout)
            self.assertEqual(len(delivered) + len(skipped), 6, got.stdout)
            for msgid_hex, path in delivered:
                msgid = bytes.fromhex(msgid_hex.decode())
                self.assertEqual(fnv1a(msgid) % 3, index)
                self.assertNotIn(msgid, seen)
                seen[msgid] = index
                self.assertEqual(Path(path.decode()).read_bytes(),
                                 b"job %d" % msgids.index(msgid))
        self.assertEqual(sorted(seen), sorted(msgids))
        # A worker index outside its set is refused by the argv grammar.
        bad = self.fn("pattern", "pipeline", "pull", self.control, "worker-x", "3", "3",
                      GROUP, self.root)
        self.assertEqual(bad.returncode, 5, (bad.stdout + bad.stderr).decode())
        self.assertIn(b"partition", bad.stderr)
        self.node.stop(process=owner)


if __name__ == "__main__":
    unittest.main()
