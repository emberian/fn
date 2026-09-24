"""Source-matched saved-image gate for the experimental local topic install.

This exercises the connected peer gate, canonical control request, durable
Store publication and replay. It does not claim a native root/report witness.
"""
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))


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


if __name__ == "__main__":
    unittest.main()
