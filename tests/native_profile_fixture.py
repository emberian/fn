"""The native operator fixture for the store profile (kept from the removed
tests/test_native_profile_upgrade.py when D34 removed the offline upgrade):
one scratch node with a configured store, listener and control socket, the
two preset frames `init --profile development|scale` writes (format 9, the
record log: the one format init writes), and the operator's `status` profile
line.  No test lives here.
"""
import fcntl
import hashlib
import os
from pathlib import Path
import signal
import subprocess
import unittest

from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
IMAGE = verbs.IMAGE
DEVELOPER = verbs.DEVELOPER
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN = verbs.EXIT_OK, verbs.EXIT_REFUSED, verbs.EXIT_UNCERTAIN

# The two preset frames `init --profile development|scale` writes in format 10
# (lane format-bump-10: the word fn-store-10 and fifteen u64 fields; measured on
# hbox native-n2's developer image; format 9's were 226969fe... and d11edbf6...)
# Before: format 9
# (lane log-recovery: re-measured on 878a8dbde's images, hbox native-s1b; the
# format-8 frames were 61802dbb... and 0d1757e3...)
# (planning/evidence/bounds-join-2026-09-25.md: the presets carry the
# codec-ceiling G and R = the article record; since header-limits-profile,
# PRF-230, fields 15 to 17 the header limits: re-measured on batch AS's
# image, `operator init --profile development|scale`).
DEVELOPMENT_FRAME = "2e0a82e360b3f8e221140824bd88c57a4b629e7b06204f5cdefefda68fe586b5"
SCALE_FRAME = "b6dbf9da0023ce82168c989fb4754cf83e3dffa583e1a8d0947e76e44529ee40"
BUDGET = {"old": {128}, "new": {4096}, "either": {128, 4096}}
FRAME = {128: DEVELOPMENT_FRAME, 4096: SCALE_FRAME}

class ProfileFixture(verbs.NativeOperatorVerbFixture):
    image = IMAGE

    def setUp(self):
        if not verbs.executable(self.image):
            self.skipTest("{} is required".format(self.image))
        super().setUp()
        self.control = self.root / "control.sock"
        self.port = verbs.free_port()
        self.config.write_text(
            '[store]\npath = "{}"\n'
            '[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(self.store, self.port, self.control),
            encoding="ascii")

    start_owner = verbs.NativeOperatorUncertainOutcomeTests.start_owner
    reap = verbs.NativeOperatorUncertainOutcomeTests.reap
    headroom = verbs.NativeOperatorCapacityTests.headroom
    post_many = verbs.NativeOperatorCapacityTests.post_many
    stop = verbs.NativeOperatorCapacityTests.stop

    def op(self, *words, env=None):
        return self.operator(*words, image=self.image, env=env)

    def store_cli(self, *words, env=None):
        return subprocess.run(
            [str(self.image), "--fn", "store", str(self.store), *words],
            cwd=ROOT, env=env or verbs.environment(), stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=180, check=False)

    def frame(self):
        return hashlib.sha256((self.store / "config.json").read_bytes()).hexdigest()

    def init(self):
        created = self.op("init", "--profile", "development", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.assertEqual(self.frame(), DEVELOPMENT_FRAME)


class ProfileLineMixin:
    """D27: the operator's fields as `status' prints them."""

    def profile_line(self):
        status = self.op("status")
        self.assertEqual(status.returncode, EXIT_OK, status.stderr.decode())
        for line in status.stdout.decode("ascii").splitlines():
            if line.startswith("profile "):
                return {k: int(v) if v.isdigit() else v
                        for k, v in (w.split("=", 1) for w in line.split()[1:])}
        self.fail(status.stdout.decode())

    def article(self, message_id, total):
        """An authored article of exactly TOTAL octets."""
        head = ("From: p1@example.invalid\r\nNewsgroups: fn.test\r\n"
                "Subject: p1 bound\r\nMessage-ID: {}\r\n\r\n").format(message_id).encode("ascii")
        body = b"x" * (total - len(head) - 2) + b"\r\n"
        data = head + body
        self.assertEqual(len(data), total)
        return data
