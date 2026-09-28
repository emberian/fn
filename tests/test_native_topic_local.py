"""Source-matched native gate for experimental local root/report admission.

The fixed signed sources and FN-Topic fields were emitted by ACL2; Python
only transports them and the test cryptographic keys through native commands.
"""
import os
import hashlib
from pathlib import Path
import subprocess
import unittest

from tests.native_harness import ROOT, Node, environment, executable, native_image
from tests import native_log_observation

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
LEGACY_IMAGE = Path(os.environ.get("FN_NATIVE_TOPIC_V1_HOST", ""))
FIXTURES = ROOT / "tests" / "fixtures" / "topic-history"
PRINCIPAL = bytes([85]) * 32
ED_PUBLIC = bytes.fromhex(
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
ED_SECRET = bytes.fromhex(
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")


@unittest.skipUnless(os.environ.get("FN_RUN_TOPIC_LOCAL_E2E") == "1"
                     and executable(IMAGE),
                     "requires a source-matched topic saved image")
class NativeTopicLocalTest(unittest.TestCase):
    def setUp(self):
        self.image = (LEGACY_IMAGE
                      if self._testMethodName == "test_v1_history_reopens_under_v2"
                      and LEGACY_IMAGE.is_file() else IMAGE)
        self.node = Node(self, self.image)
        self.root, self.store = self.node.root, self.node.store_path
        self.control, self.config = self.node.control, self.node.config
        self.assertEqual(self.invoke("store", self.store, "init", "fn.test").returncode,
                         0)
        self.principal = self.root / "principal.bin"
        self.ed_public = self.root / "ed-public.bin"
        self.ed_secret = self.root / "ed-secret.bin"
        self.principal.write_bytes(PRINCIPAL)
        self.ed_public.write_bytes(ED_PUBLIC)
        self.ed_secret.write_bytes(ED_SECRET)
        self.ml_public = FIXTURES / "ml-dsa-65-test-public.pem"
        self.ml_private = FIXTURES / "ml-dsa-65-test-private.pem"

    def invoke(self, *words):
        return self.node.invoke(*words, image=self.image, timeout=120)

    def start_owner(self):
        return self.node.start(image=self.image, timeout=120)

    def stop_owner(self, proc):
        self.node.stop(process=proc)

    def topic(self, operation, *args, expected):
        result = self.invoke("topic", operation, self.control, *args)
        self.assertEqual(result.returncode, expected,
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
        return result

    def transactions(self):
        # The committed history (format 9: the record log), read by the image.
        return native_log_observation.committed_history(self.image, self.store,
                                                        env=environment(), cwd=ROOT)

    def author(self, source, name):
        signed = self.invoke("hybrid-sign", self.principal, self.ed_public,
                             self.ed_secret, self.ml_public, self.ml_private,
                             source)
        self.assertEqual(signed.returncode, 0,
                         signed.stderr.decode("utf-8", "replace"))
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_sig = self.root / (name + ".ed.sig")
        ml_sig = self.root / (name + ".ml.sig")
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        authored = self.invoke("hybrid-author", self.control, "1", source,
                               ed_sig, ml_sig, self.ml_public)
        self.assertEqual(authored.returncode, 0,
                         (authored.stdout + authored.stderr).decode("utf-8", "replace"))
        return authored

    def test_install_is_durable_and_absent_source_refuses(self):
        owner = self.start_owner()
        self.assertIn(b"topic accepted", self.topic("install", expected=0).stdout)
        self.topic("install", expected=1)
        self.topic("anchor", "99", "2", expected=1)
        self.topic("report", "99", expected=1)
        self.stop_owner(owner)
        reopened = self.start_owner()
        self.topic("install", expected=1)
        self.topic("anchor", "99", "2", expected=1)
        self.stop_owner(reopened)

    def test_root_and_report_admit_from_historical_signed_sources(self):
        self.assertEqual(
            hashlib.sha256((FIXTURES / "matched-root.source").read_bytes()).hexdigest(),
            "d2c9852f474ac62fcaeb94c65a671d09ed9e8230d3db57ec3329392ffd887a87")
        self.assertEqual(
            hashlib.sha256((FIXTURES / "matched-report.source").read_bytes()).hexdigest(),
            "8601816a81ed55e48b790894a2c7b2d1274a7884ff96f28f242e8c6f232dd3be")
        owner = self.start_owner()
        enrolled = self.invoke("hybrid-enroll", self.control, "1",
                               self.principal, self.ed_public, self.ml_public)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        self.author(FIXTURES / "matched-root.source", "root")
        self.topic("install", expected=0)
        self.assertIn(b"topic accepted", self.topic("anchor", "1", "1",
                                                    expected=0).stdout)
        self.author(FIXTURES / "matched-report.source", "report")
        self.assertIn(b"topic accepted", self.topic("report", "4",
                                                    expected=0).stdout)
        admitted_files = self.transactions()
        self.assertGreater(len(admitted_files), 0)
        self.assertIn(b"topic accepted, replayed-historical",
                      self.topic("report", "4", expected=0).stdout)
        self.assertEqual(self.transactions(), admitted_files)
        self.stop_owner(owner)
        reopened = self.start_owner()
        self.topic("install", expected=1)
        self.topic("anchor", "1", "1", expected=1)
        self.assertIn(b"topic accepted, replayed-historical",
                      self.topic("report", "4", expected=0).stdout)
        self.assertEqual(self.transactions(), admitted_files)
        self.topic("report", "99", expected=1)
        self.assertEqual(self.transactions(), admitted_files)
        self.stop_owner(reopened)

    def test_v1_history_reopens_under_v2(self):
        if not LEGACY_IMAGE.is_file() or not os.access(LEGACY_IMAGE, os.X_OK):
            self.skipTest("requires exact pre-v2 topic image")
        owner = self.start_owner()
        enrolled = self.invoke("hybrid-enroll", self.control, "1",
                               self.principal, self.ed_public, self.ml_public)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        self.author(FIXTURES / "matched-root.source", "legacy-root")
        self.topic("install", expected=0)
        self.topic("anchor", "1", "1", expected=0)
        self.author(FIXTURES / "matched-report.source", "legacy-report")
        self.topic("report", "4", expected=0)
        historical = self.transactions()
        self.stop_owner(owner)

        self.image = IMAGE
        reopened = self.start_owner()
        self.assertIn(b"replayed-historical",
                      self.topic("report", "4", expected=0).stdout)
        self.assertEqual(self.transactions(), historical)
        self.topic("anchor", "1", "1", expected=1)
        self.assertEqual(self.transactions(), historical)
        self.assertEqual(
            hashlib.sha256((FIXTURES / "matched-second-root.source").read_bytes()).hexdigest(),
            "6216689ae3e67837d3b5187617ca6a1adff6179e59249e65e98c5e0024bdcf8f")
        self.author(FIXTURES / "matched-second-root.source", "v2-second-root")
        self.topic("anchor", "6", "1", expected=0)
        mixed = self.transactions()
        self.assertGreater(len(mixed), len(historical))
        self.assertIn(b"replayed-historical",
                      self.topic("report", "4", expected=0).stdout)
        self.assertEqual(self.transactions(), mixed)
        revoked = self.invoke("hybrid-revoke", self.control, "2", self.principal)
        self.assertEqual(revoked.returncode, 0,
                         (revoked.stdout + revoked.stderr).decode("utf-8", "replace"))
        after_revoke = self.transactions()
        self.assertGreater(len(after_revoke), len(mixed))
        self.assertIn(b"replayed-historical",
                      self.topic("report", "4", expected=0).stdout)
        self.assertEqual(self.transactions(), after_revoke)
        self.stop_owner(reopened)

        before_status = self.invoke("store", self.store, "status")
        before_retention = self.invoke("store", self.store, "retention")
        self.assertEqual(before_status.returncode, 0, before_status.stderr.decode())
        self.assertEqual(before_retention.returncode, 0,
                         before_retention.stderr.decode())
        # Two compactions over the record log (the checkpoint's rotation and
        # the covered segments' drop; lane log-recovery-2 re-targeted this
        # from the pack chain).  The generation checkpoint that followed is
        # retired (lane matrix-reds): the reopen below reads the state
        # checkpoint the compaction wrote, and the topic report after it is
        # the projection's check.
        for words in (("operator", self.config, "store", "compact"),
                      ("operator", self.config, "store", "compact")):
            result = self.invoke(*words)
            self.assertEqual(result.returncode, 0,
                             (result.stdout + result.stderr).decode("utf-8", "replace"))

        def state(result):
            # The open's route (open=checkpoint:S after a compaction) is not
            # the state; every other line is.
            return [line for line in result.stdout.splitlines()
                    if not line.startswith(b"open=")]
        self.assertEqual(state(self.invoke("store", self.store, "status")),
                         state(before_status))
        self.assertEqual(self.invoke("store", self.store, "retention").stdout,
                         before_retention.stdout)
        compacted = self.transactions()

        final = self.start_owner()
        self.topic("anchor", "6", "1", expected=1)
        self.assertIn(b"replayed-historical",
                      self.topic("report", "4", expected=0).stdout)
        self.assertEqual(self.transactions(), compacted)
        self.stop_owner(final)

    def test_fresh_v2_anchor_refuses_legacy_reopen(self):
        if not LEGACY_IMAGE.is_file() or not os.access(LEGACY_IMAGE, os.X_OK):
            self.skipTest("requires exact pre-v2 topic image")
        owner = self.start_owner()
        enrolled = self.invoke("hybrid-enroll", self.control, "1",
                               self.principal, self.ed_public, self.ml_public)
        self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
        self.author(FIXTURES / "matched-root.source", "v2-root")
        self.topic("install", expected=0)
        self.topic("anchor", "1", "1", expected=0)
        self.stop_owner(owner)

        try:
            legacy = self.node.operator("run", image=LEGACY_IMAGE, timeout=40)
        except subprocess.TimeoutExpired:
            self.fail("pre-v2 image unexpectedly opened a v2 topic anchor")
        self.assertNotEqual(legacy.returncode, 0, legacy.stdout + legacy.stderr)

        reopened = self.start_owner()
        self.topic("anchor", "1", "1", expected=1)
        self.stop_owner(reopened)


if __name__ == "__main__":
    unittest.main()
