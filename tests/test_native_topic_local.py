"""Source-matched native gate for experimental local root/report admission.

The fixed signed sources and FN-Topic fields were emitted by ACL2; Python
only transports them and the test cryptographic keys through native commands.
"""
import os
import hashlib
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
FIXTURES = ROOT / "tests" / "fixtures" / "topic-history"
PRINCIPAL = bytes([85]) * 32
ED_PUBLIC = bytes.fromhex(
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
ED_SECRET = bytes.fromhex(
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(os.environ.get("FN_RUN_TOPIC_LOCAL_E2E") == "1"
                     and IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "requires a source-matched topic saved image")
class NativeTopicLocalTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-topic-local-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.config = self.root / "fn.toml"
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.env.pop("FN_NATIVE_CONTROL_FAULT", None)
        self.env.pop("FN_NATIVE_CONTROL_TEST_STOP", None)
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                self.store, free_port(), self.control), encoding="ascii")
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
        return subprocess.run([str(IMAGE), "--fn", *map(str, words)],
                              cwd=ROOT, env=self.env, capture_output=True,
                              timeout=120, check=False)

    def start_owner(self):
        proc = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        self.addCleanup(self.reap, proc)
        wait_for_announcement(proc, b"LISTENING ", timeout=120)
        return proc

    @staticmethod
    def reap(proc):
        if proc.poll() is None:
            proc.kill()
            proc.wait(timeout=10)
        for stream in (proc.stdout, proc.stderr):
            if stream and not stream.closed:
                stream.close()

    def stop_owner(self, proc):
        diagnostic = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostic)

    def topic(self, operation, *args, expected):
        result = self.invoke("topic", operation, self.control, *args)
        self.assertEqual(result.returncode, expected,
                         (result.stdout + result.stderr).decode("utf-8", "replace"))
        return result

    def transactions(self):
        return tuple(sorted((path.name, hashlib.sha256(path.read_bytes()).hexdigest())
                            for path in (self.store / "transactions").glob("*.txn")))

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
            "59411dc69536c4bfb9f39ddd243df9625627d98f91ed2f6c0d5a942672f366dc")
        self.assertEqual(
            hashlib.sha256((FIXTURES / "matched-report.source").read_bytes()).hexdigest(),
            "aa269729afb6ba7df35f0fcbdb350752dfb921599b0f40b198b8d2aa9d6ef321")
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


if __name__ == "__main__":
    unittest.main()
