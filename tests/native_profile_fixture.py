"""The native operator fixture for the store profile (kept from the removed
tests/test_native_profile_upgrade.py when D34 removed the offline upgrade):
one scratch node with a configured store, listener and control socket, the
two preset frames `init --profile development|scale` writes (format 9, the
record log: the one format init writes), and the operator's `status` profile
line.  No test lives here.
"""
import hashlib

from tests import test_native_operator_verbs as verbs
from tests.native_harness import EXIT_OK, executable, native_image

IMAGE = native_image("FN_NATIVE_HOST")

# The two preset frames `init --profile development|scale` writes in format 10
# (lane format-bump-10: the word fn-store-10, fifteen u64 fields, the BLAKE3
# trailer of lane blake3-digest; measured on hbox native-n3's developer image;
# before the digest merge, on
# hbox native-n2's developer image; format 9's were 226969fe... and d11edbf6...)
# Before: format 9
# (lane log-recovery: re-measured on 878a8dbde's images, hbox native-s1b; the
# format-8 frames were 61802dbb... and 0d1757e3...)
# (planning/evidence/bounds-join-2026-09-25.md: the presets carry the
# codec-ceiling G and R = the article record; since header-limits-profile,
# PRF-230, fields 15 to 17 the header limits: re-measured on batch AS's
# image, `operator init --profile development|scale`).
DEVELOPMENT_FRAME = "1de8f91f4b616ff6004c7342de57d9bbf550e469cb230cf92d670234bbc07de8"
SCALE_FRAME = "18e505d3a0c2e3acb5b0ba45405b8842936d558199c1bb951349fc46af135696"
BUDGET = {"old": {128}, "new": {4096}, "either": {128, 4096}}
FRAME = {128: DEVELOPMENT_FRAME, 4096: SCALE_FRAME}

class ProfileFixture(verbs.NativeOperatorVerbFixture):
    """A node with a listener and control socket (tests/native_harness.py
    Node) whose verbs run on `self.image`."""
    image = IMAGE
    listener = True

    def setUp(self):
        if not executable(self.image):
            self.skipTest("{} is required".format(self.image))
        super().setUp()

    headroom = verbs.NativeOperatorCapacityTests.headroom
    post_many = verbs.NativeOperatorCapacityTests.post_many

    def op(self, *words, env=None):
        return self.operator(*words, image=self.image, env=env)

    def store_cli(self, *words, env=None):
        return self.node.store(*words, image=self.image, env=env)

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
