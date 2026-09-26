"""D27, PRF-167, SCN-097: the consumer count is the operator's (profile field 9).

On the developer image: a store made with the pre-D27 figure
(`--max-consumers 256`) registers 256 consumers over the owner's local
control socket and refuses the 257th; `store upgrade-profile
--max-consumers 300` raises the field with no migration; at the next open
the replay of the 256 committed registrations is accepted, consumers 257 to
300 register, the first one still answers POSITION, and the 301st is
refused.  A final reopen replays all 300 (above the old constant).  The
decision is books/consumer-position.lisp `fn-cp-register-within', called by
books/consumer-owner-local.lisp `fn-col-register' from host/owner-host.lisp
`fn-owner-consumer-local-register' with the opened profile's field 9.
"""
import select
import signal
import subprocess
import unittest

from tests import native_profile_fixture as upgrade
from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
EXIT_OK, EXIT_REFUSED = verbs.EXIT_OK, verbs.EXIT_REFUSED


class NativeConsumerProfileTests(upgrade.ProfileFixture):
    image = verbs.DEVELOPER
    profile_line = upgrade.ProfileLineMixin.profile_line

    def start_owner(self, image):
        # The owner's stderr goes to a file: three hundred requests must not
        # fill a pipe nobody drains.
        self.opens = getattr(self, "opens", 0) + 1
        self.owner_log = self.root / "owner-{}.err".format(self.opens)
        with open(self.owner_log, "wb") as log:
            process = subprocess.Popen(
                [str(image), "--fn", "operator", str(self.config), "run"],
                cwd=ROOT, env=verbs.environment(), stdout=subprocess.PIPE,
                stderr=log, bufsize=0)
        self.addCleanup(self.reap, process)
        for _ in range(4):
            self.assertTrue(select.select([process.stdout], [], [], 180)[0],
                            "the owner did not become ready")
            if process.stdout.readline().startswith(b"LISTENING "):
                return process
            if process.poll() is not None:
                self.fail("owner failed: {}".format(self.owner_log.read_text()))
        self.fail("the owner's readiness output was malformed")

    def stop(self, owner):
        owner.send_signal(signal.SIGTERM)
        self.assertEqual(owner.wait(timeout=60), EXIT_OK,
                         self.owner_log.read_text(errors="replace"))

    def consumer(self, verb, *args):
        return subprocess.run(
            [str(self.image), "--fn", "consumer", verb, str(self.control),
             *map(str, args)], cwd=ROOT, env=verbs.environment(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180,
            check=False)

    def register(self, k):
        target = self.root / "c{}.fncu".format(k)
        return self.consumer("register", "c{}".format(k), "fn.test", target), target

    def register_range(self, first, last):
        for k in range(first, last + 1):
            result, target = self.register(k)
            self.assertEqual(result.returncode, EXIT_OK,
                             "c{}: {}".format(k, result.stderr.decode()))
            self.assertIn(b"consumer accepted", result.stdout)
            self.assertTrue(target.read_bytes().startswith(b"fncu\x01"))

    def refused(self, k):
        result, target = self.register(k)
        self.assertEqual(result.returncode, EXIT_REFUSED,
                         "c{}: {}".format(k, result.stdout.decode()))
        self.assertIn(b"refused", result.stdout + result.stderr)
        self.assertFalse(target.exists())

if __name__ == "__main__":
    unittest.main()
