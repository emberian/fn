"""Production/developer native saved-image entry separation.

The source checks are always active.  The executable witness joins them when
both saved images have been built; absence skips that witness rather than
turning a source inspection into runtime evidence.
"""
import os
from pathlib import Path
import subprocess
import unittest


ROOT = Path(__file__).resolve().parent.parent
PRODUCTION = Path(os.environ.get(
    "FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


def invoke(image, *words):
    environment = dict(os.environ)
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    # The profile is serialized at build time.  A restart-time variable must
    # not change which entries the image exposes.
    environment["FN_NATIVE_PROFILE"] = "developer"
    return subprocess.run(
        [str(image), "--fn", *words], cwd=ROOT, env=environment,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, check=False)


class NativeImageProfileSourceTests(unittest.TestCase):
    def test_default_build_is_production_and_developer_output_is_distinct(self):
        script = (ROOT / "tools/build_native_host.sh").read_text()
        self.assertIn('PROFILE="${FN_NATIVE_PROFILE:-production}"', script)
        self.assertIn("production) DEFAULT_IMAGE=build/fn-host", script)
        self.assertIn("developer) DEFAULT_IMAGE=build/fn-host-developer", script)
        self.assertIn('FN_NATIVE_PROFILE="$PROFILE" FN_NATIVE_IMAGE="$IMAGE"', script)

        refused = subprocess.run(
            ["sh", "tools/build_native_host.sh"], cwd=ROOT,
            env={**os.environ, "FN_NATIVE_PROFILE": "invalid"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(refused.returncode, 2, refused.stderr.decode())
        self.assertIn(b"must be production or developer", refused.stderr)

    def test_profile_is_selected_before_owner_and_operator_are_loaded(self):
        build = (ROOT / "host/native/build.lisp").read_text()
        io = build.index('(load "host/native/io.lisp")')
        profile = build.index("(fnn-select-image-profile", io)
        owner = build.index('(load "host/native/owner.lisp")', profile)
        operator = build.index('(load "host/native/operator.lisp")', owner)
        self.assertLess(io, profile)
        self.assertLess(profile, owner)
        self.assertLess(owner, operator)
        # Public BP operations stay in the same production image.
        self.assertGreater(build.index('(load "host/native/bp.lisp")'), operator)
        self.assertGreater(build.index('(load "host/native/bp-service.lisp")'), operator)
        self.assertIn('(sb-ext:posix-getenv "FN_NATIVE_IMAGE")', build)

    def test_only_developer_image_registers_raw_owner_and_admits_raw_reader(self):
        owner = (ROOT / "host/native/owner.lisp").read_text()
        dispatch = (ROOT / "host/native/io.lisp").read_text()
        self.assertIn('(fnn-register-developer-verb "owner"', owner)
        reader = dispatch.index('((string= verb "reader")')
        gate = dispatch.index("(unless (fnn-developer-image-p)", reader)
        call = dispatch.index("(fnn-command-reader", gate)
        self.assertLess(reader, gate)
        self.assertLess(gate, call)

    def test_packaged_launcher_defaults_to_the_production_image(self):
        launcher = (ROOT / "packaging/fn-native").read_text()
        self.assertIn('image=${FN_NATIVE_HOST:-"$root/build/fn-host"}', launcher)
        self.assertIn("production saved native host image", launcher)


@unittest.skipUnless(
    os.access(PRODUCTION, os.X_OK) and os.access(DEVELOPER, os.X_OK),
    "build production and developer native images for the executable profile witness")
class NativeImageProfileSavedImageTests(unittest.TestCase):
    def test_production_rejects_raw_services_but_keeps_operator_and_bp(self):
        operator = invoke(PRODUCTION, "operator", "/not-opened", "help", "run")
        self.assertEqual(operator.returncode, 0, operator.stderr.decode())
        self.assertIn(b"usage: fn operator", operator.stdout)

        owner = invoke(PRODUCTION, "owner", "run", "/not-opened", "0", "1", "8")
        self.assertEqual(owner.returncode, 5, owner.stderr.decode())
        self.assertIn(b"unknown verb owner", owner.stderr)

        reader = invoke(PRODUCTION, "reader", "not-a-port", "1", "-")
        self.assertEqual(reader.returncode, 5, reader.stderr.decode())
        self.assertIn(b"reader is available only in the developer image", reader.stderr)

        bp = invoke(PRODUCTION, "bp", "not-a-command")
        self.assertEqual(bp.returncode, 5, bp.stderr.decode())
        self.assertIn(b"unknown bp command", bp.stderr)

    def test_restart_environment_cannot_hide_developer_entries_or_enable_production(self):
        owner = invoke(DEVELOPER, "owner", "run", "/not-opened", "0", "1", "8")
        self.assertNotIn(b"unknown verb owner", owner.stderr)
        reader = invoke(DEVELOPER, "reader", "not-a-port", "1", "-")
        self.assertNotIn(b"available only in the developer image", reader.stderr)


if __name__ == "__main__":
    unittest.main()
