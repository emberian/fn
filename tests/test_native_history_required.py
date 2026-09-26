"""D31, natively: the committed-history requirement and the retry resolution.

books/store-history-required.lisp decides; host/native/io.lisp performs:

* the retry-resolution sequence of the review of 2026-09-25 §3, case 2, on
  both posting entries (developer `store ROOT post`, and the served owner:
  `operator CONFIG run` with `operator CONFIG post`), under SIGKILL and EIO
  at each of the five marker cuts: the record is durable, the process dies
  before (or inside) its marker program, the next writable open catches the
  marker up, the client's retry resolves as already stored and nothing
  commits, the newest transaction file then disappears, and recovery refuses
  the store, twice;
* the catch-up's own marker cuts (FN_NATIVE_RECOVERY_FAULT on `recover`):
  after each, the next open completes it and the same sequence is refused;
* D34: no verb marks a store later; `init` refuses `required` by name (a
  store is born `unmarked`; how one is born `required` is PKT-587).
"""
import os
from pathlib import Path
import re
import signal
import subprocess
import unittest

from tests.campaign import native_cuts
from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
DEVELOPER = verbs.DEVELOPER
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_FAULT = 0, 1, 3, 4
MARKER_CUTS = ("marker-created", "marker-written", "marker-staged-durable",
               "marker-replaced", "marker-durable")
ACTIONS = (("kill", None), ("eio", EXIT_UNCERTAIN))
SELECTORS = ("FN_NATIVE_POST_FAULT", "FN_NATIVE_RECOVERY_FAULT", "FN_NATIVE_PROFILE_FAULT",
             "FN_NATIVE_CONTROL_FAULT")


class HistoryRequiredSourceTests(unittest.TestCase):
    def test_the_host_calls_acl2s_decisions(self):
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        check = native_cuts.host_function(io, "fnn-check-history-marker")
        self.assertIn("'fn-hmr-open-verdict", check)
        self.assertIn("'fn-hmr-catch-up", check)
        native_cuts.verify_recovery_order()


class Fixture(verbs.NativeOperatorVerbFixture):
    def setUp(self):
        if not verbs.executable(DEVELOPER):
            self.skipTest("{} is required".format(DEVELOPER))
        super().setUp()
        self.control = self.root / "control.sock"
        self.port = verbs.free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")
        self.env = verbs.environment()
        for name in SELECTORS:
            self.env.pop(name, None)

    start_owner = verbs.NativeOperatorUncertainOutcomeTests.start_owner
    reap = verbs.NativeOperatorUncertainOutcomeTests.reap
    article = staticmethod(verbs.NativeOperatorUncertainOutcomeTests.article)

    def with_fault(self, name, value):
        return dict(self.env, **{name: value})

    def op(self, *words, env=None, expected=EXIT_OK):
        result = self.operator(*words, image=DEVELOPER, env=env or self.env)
        if expected is not None:
            self.assertEqual(result.returncode, expected, "operator {}: {} {}".format(
                words, result.stdout.decode(), result.stderr.decode()))
        return result

    def cli(self, *words, env=None, expected=EXIT_OK):
        result = subprocess.run(
            [str(DEVELOPER), "--fn", "store", str(self.store), *map(str, words)],
            cwd=ROOT, env=env or self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)
        if expected is not None:
            self.assertEqual(result.returncode, expected, "store {}: {} {}".format(
                words, result.stdout.decode(), result.stderr.decode()))
        return result

    def payload(self, message_id):
        path = self.root / (message_id.strip("<>").replace("@", "-") + ".eml")
        path.write_bytes(self.article(message_id))
        return path

    def cli_post(self, message_id, env=None, expected=EXIT_OK):
        return self.cli("post", message_id, self.payload(message_id), "-", "-", "fn.test",
                        env=env, expected=expected)

    def served_post(self, message_id):
        return self.op("post", "--message-id", message_id, "--payload",
                       str(self.payload(message_id)), "--group", "fn.test", expected=None)

    def files(self):
        return sorted((self.store / "transactions").iterdir())

    def marker(self):
        path = self.store / "committed-history.json"
        return path.read_bytes() if path.exists() else None

    def profile(self):
        status = self.op("status").stdout.decode()
        found = re.search(r"history-marker=(\w+)", status)
        self.assertIsNotNone(found, status)
        return found.group(1)

    def reference_marker(self, count):
        """The marker bytes of a store with COUNT commits, from ACL2's frame."""
        other = self.root / "reference-{}".format(count)
        if (other / "committed-history.json").exists():
            return (other / "committed-history.json").read_bytes()
        subprocess.run([str(DEVELOPER), "--fn", "store", str(other), "init", "fn.test"],
                       cwd=ROOT, env=self.env, check=True, capture_output=True)
        for n in range(count):
            msgid = "<reference-{}-{}@example.invalid>".format(count, n)
            subprocess.run([str(DEVELOPER), "--fn", "store", str(other), "post", msgid,
                            str(self.payload(msgid)), "-", "-", "fn.test"],
                           cwd=ROOT, env=self.env, check=True, capture_output=True)
        return (other / "committed-history.json").read_bytes()

    def assert_newest_loss_refused(self, marker, records):
        self.files()[-1].unlink()
        for _ in range(2):
            refused = self.op("recover", expected=EXIT_FAULT)
            self.assertIn("history-short-of-marker marker={} records={}".format(marker, records),
                          refused.stderr.decode())

    def assert_killed_or(self, result, expected):
        if expected is None:
            self.assertLess(result.returncode, 0, result.stderr.decode())
        else:
            self.assertEqual(result.returncode, expected, result.stderr.decode())


class RetryResolutionTests(Fixture):
    """D31 case 2: a success answered after recovery, with no later commit."""

    def test_the_developer_entry_at_every_marker_cut(self):
        covering = self.reference_marker(2)
        for cut in MARKER_CUTS:
            for action, expected in ACTIONS:
                with self.subTest(cut=cut, action=action):
                    self.store = self.root / "cli-{}-{}".format(cut, action)
                    self.config.write_text('[store]\npath = "{}"\n'.format(self.store),
                                           encoding="ascii")
                    self.cli("init", "fn.test")
                    self.cli_post("<first@example.invalid>")
                    retried = "<retried-{}-{}@example.invalid>".format(cut, action)
                    faulted = self.cli_post(
                        retried, env=self.with_fault("FN_NATIVE_POST_FAULT",
                                                     "{}:{}".format(cut, action)),
                        expected=None)
                    self.assert_killed_or(faulted, expected)
                    self.assertEqual(len(self.files()), 2)   # the record is durable
                    # The retry: the open catches the marker up, the answer
                    # is `duplicate' (already stored), nothing commits.
                    again = self.cli_post(retried)
                    self.assertEqual(again.stdout.decode().strip(), "duplicate")
                    self.assertEqual(len(self.files()), 2)
                    self.assertEqual(self.marker(), covering)
                    self.assert_newest_loss_refused(2, 1)

    def test_the_served_owner_at_every_marker_cut(self):
        for cut in MARKER_CUTS:
            for action, expected in ACTIONS:
                with self.subTest(cut=cut, action=action):
                    self.store = self.root / "owner-{}-{}".format(cut, action)
                    self.control = self.root / "c-{}-{}.sock".format(cut[:9], action)
                    self.port = verbs.free_port()
                    self.config.write_text(
                        '[store]\npath = "{}"\n'
                        '[listener]\nhost = "127.0.0.1"\nport = {}\n'
                        '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
                        encoding="ascii")
                    self.op("init", "fn.test")
                    owner = self.start_owner(DEVELOPER)
                    first = self.served_post("<first@example.invalid>")
                    self.assertEqual(first.returncode, EXIT_OK, first.stderr.decode())
                    owner.send_signal(signal.SIGTERM)
                    self.assertEqual(owner.wait(timeout=60), EXIT_OK)
                    retried = "<served-{}-{}@example.invalid>".format(cut, action)
                    owner = self.start_owner(DEVELOPER, {"FN_NATIVE_POST_FAULT":
                                                         "{}:{}".format(cut, action)})
                    unsure = self.served_post(retried)
                    self.assertNotEqual(unsure.returncode, EXIT_OK, unsure.stdout.decode())
                    code = owner.wait(timeout=60)
                    if expected is None:
                        self.assertEqual(code, -signal.SIGKILL)
                    else:
                        self.assertEqual(unsure.returncode, EXIT_UNCERTAIN, unsure.stderr.decode())
                    count = len(self.files())   # the retried record is durable
                    owner = self.start_owner(DEVELOPER)
                    again = self.served_post(retried)
                    print("served retry", cut, action, again.returncode,
                          again.stdout.decode().strip(), again.stderr.decode().strip())
                    # The owner answers the retry as a success: already stored.
                    self.assertEqual(again.returncode, EXIT_OK, again.stderr.decode())
                    self.assertIn(b"accepted operator post DUPLICATE", again.stdout + again.stderr)
                    owner.send_signal(signal.SIGTERM)
                    self.assertEqual(owner.wait(timeout=60), EXIT_OK)
                    self.assertEqual(len(self.files()), count)   # nothing committed
                    self.assertEqual(self.marker(), self.reference_marker(count))
                    self.assert_newest_loss_refused(count, count - 1)

    def test_the_catch_up_cuts(self):
        covering = self.reference_marker(2)
        for cut in MARKER_CUTS:
            for action, expected in ACTIONS:
                with self.subTest(cut=cut, action=action):
                    self.store = self.root / "catch-{}-{}".format(cut, action)
                    self.config.write_text('[store]\npath = "{}"\n'.format(self.store),
                                           encoding="ascii")
                    self.cli("init", "fn.test")
                    self.cli_post("<first@example.invalid>")
                    retried = "<caught-{}-{}@example.invalid>".format(cut, action)
                    self.cli_post(retried, env=self.with_fault("FN_NATIVE_POST_FAULT",
                                                               "marker-created:kill"),
                                  expected=None)
                    before = self.marker()
                    self.assertNotEqual(before, covering)
                    crashed = self.cli("recover", env=self.with_fault(
                        "FN_NATIVE_RECOVERY_FAULT", "{}:{}".format(cut, action)), expected=None)
                    self.assert_killed_or(crashed, expected)
                    self.assertIn(self.marker(), (before, covering))
                    self.cli("recover")
                    self.assertEqual(self.marker(), covering)
                    again = self.cli_post(retried)
                    self.assertEqual(again.stdout.decode().strip(), "duplicate")
                    self.assert_newest_loss_refused(2, 1)


if __name__ == "__main__":
    unittest.main()
