"""A known abort of a staged identity, consumer or topic record, natively.

Lane host-decisions (PRF-299) made the Store's known abort resolve every
staged deferred record (fn-sn-known-abort; fn-owner-known-abort answers
:aborted, lane host-decisions-2's fn-pout-known-abort), where before a staged
identity, consumer or topic record answered :fault and the owner fenced for
recovery although nothing had been written.  This module injects the known
refusal on the served owner's publication of each kind
(FN_NATIVE_POST_FAULT=record-prepublish:refuse, host/native/io.lisp
fnn-publish: a refusal before the record's first write, developer image
only) and checks, per kind:

* the verb is REFUSED (exit 1), never uncertain (3) or a fault (4);
* the owner is not fenced: it keeps serving (a second refused verb is again
  a refusal, not "fenced pending recovery") and stops cleanly (exit 0);
* nothing was committed: the record log's committed history is unchanged;
* after a restart without the fault, the same verb commits (exit 0) and the
  history grows by exactly that record.
"""
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement
from tests import native_log_observation

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                            ROOT / "build" / "fn-host-developer"))
FIXTURES = ROOT / "tests" / "fixtures" / "topic-history"
EXIT_OK, EXIT_REFUSED = 0, 1
FAULT = "record-prepublish:refuse"


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "requires the developer image (FN_NATIVE_DEVELOPER_HOST)")
class NativeKnownAbortTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-known-abort-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.config = self.root / "fn.toml"
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        for name in ("ACL2_SYSTEM_BOOKS", "FN_HOST", "FN_NATIVE_POST_FAULT",
                     "FN_NATIVE_RECOVERY_FAULT", "FN_NATIVE_CONTROL_FAULT",
                     "FN_NATIVE_CONTROL_TEST_STOP"):
            self.env.pop(name, None)
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
            'port = {}\n[control]\npath = "{}"\n'.format(
                self.store, free_port(), self.control), encoding="ascii")
        init = self.invoke("store", self.store, "init", "fn.test")
        self.assertEqual(init.returncode, 0, self.text(init))
        self.principal = self.root / "principal.bin"
        self.ed_public = self.root / "ed-public.bin"
        self.principal.write_bytes(bytes([85]) * 32)
        self.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ml_public = FIXTURES / "ml-dsa-65-test-public.pem"

    @staticmethod
    def text(result):
        return (result.stdout + result.stderr).decode("utf-8", "replace")

    def invoke(self, *words, env=None):
        return subprocess.run([str(IMAGE), "--fn", *map(str, words)],
                              cwd=ROOT, env=env or self.env, capture_output=True,
                              timeout=120, check=False)

    def start_owner(self, fault=None):
        env = dict(self.env)
        if fault:
            env["FN_NATIVE_POST_FAULT"] = fault
        proc = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(self.config), "run"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
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
        return diagnostic

    def history(self):
        return native_log_observation.committed_history(IMAGE, self.store,
                                                        env=self.env, cwd=ROOT)

    def verb(self, kind):
        if kind == "topic":
            return ("topic", "install", self.control)
        if kind == "consumer":
            return ("consumer", "bootstrap", self.control)
        return ("hybrid-enroll", self.control, "1", self.principal,
                self.ed_public, self.ml_public)

    def check_known_abort(self, kind):
        before = self.history()
        owner = self.start_owner(FAULT)
        refused = self.invoke(*self.verb(kind))
        self.assertEqual(refused.returncode, EXIT_REFUSED, self.text(refused))
        self.assertIsNone(owner.poll(), "the owner stopped after a known abort")
        # Not fenced: the next publication is refused the same way, by the
        # injected refusal, not by a fence pending recovery.
        again = self.invoke(*self.verb(kind))
        self.assertEqual(again.returncode, EXIT_REFUSED, self.text(again))
        self.assertNotIn("fenced", self.text(again))
        diagnostic = self.stop_owner(owner)
        self.assertNotIn("indeterminate", diagnostic)
        self.assertEqual(self.history(), before, "a known abort committed a record")
        # Without the fault the same verb commits exactly one record.
        owner = self.start_owner()
        committed = self.invoke(*self.verb(kind))
        self.assertEqual(committed.returncode, EXIT_OK, self.text(committed))
        self.stop_owner(owner)
        after = self.history()
        self.assertEqual(len(after), len(before) + 1)

    def test_topic_known_abort(self):
        self.check_known_abort("topic")

    def test_consumer_known_abort(self):
        self.check_known_abort("consumer")

    def test_identity_known_abort(self):
        self.check_known_abort("identity")


if __name__ == "__main__":
    unittest.main()
