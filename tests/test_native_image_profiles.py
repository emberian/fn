"""Production/developer native saved-image entry separation.

The source checks are always active.  The executable witness joins them when
both saved images have been built; absence skips that witness rather than
turning a source inspection into runtime evidence.
"""
import os
import re
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
PRODUCTION = Path(os.environ.get(
    "FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
DTN = Path(os.environ.get("FN_NATIVE_DTN_HOST", ROOT / "build" / "fn-host-dtn"))
DTN_DEVELOPER = Path(os.environ.get(
    "FN_NATIVE_DTN_DEVELOPER_HOST", ROOT / "build" / "fn-host-dtn-developer"))


def invoke(image, *words, environment_override=None):
    environment = dict(os.environ)
    environment["ACL2_CUSTOMIZATION"] = "NONE"
    environment.pop("ACL2_SYSTEM_BOOKS", None)
    # The profile is serialized at build time.  A restart-time variable must
    # not change which entries the image exposes.
    environment["FN_NATIVE_PROFILE"] = "developer"
    environment.update(environment_override or {})
    return subprocess.run(
        [str(image), "--fn", *words], cwd=ROOT, env=environment,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, check=False)


class NativeImageProfileSourceTests(unittest.TestCase):
    def test_dtn_build_selects_serialized_profile_and_separate_output(self):
        build = (ROOT / "host/native/build-dtn.lisp").read_text()
        io = build.index('(load "host/native/io.lisp")')
        profile = build.index("(fnn-select-image-profile)", io)
        modules = build.index('(load "host/native/immutable-publish.lisp")', profile)
        self.assertLess(io, profile)
        self.assertLess(profile, modules)
        self.assertIn('(sb-ext:posix-getenv "FN_NATIVE_IMAGE")', build)
        script = (ROOT / "tools/build_native_host.sh").read_text()
        self.assertIn("production) DEFAULT_IMAGE=build/fn-host-dtn", script)
        self.assertIn("developer) DEFAULT_IMAGE=build/fn-host-dtn-developer", script)

    def test_dtn_fault_readers_use_the_same_startup_gate(self):
        source = (ROOT / "host/native/io.lisp").read_text()
        selectors = set(re.findall(r'"(FN_[A-Z_]+)"', source[
            source.index('(defparameter +fnn-developer-selectors+'):
            source.index('(defun fnn-developer-selector (')]))
        prefixes = ("FN_BP_", "FN_TCPCL_TEST_", "FN_CHECKPOINT_TEST_",
                    "FN_APP_JOURNAL_TEST_")
        for path in (ROOT / "host/native").glob("*.lisp"):
            if path.name == "io.lisp":
                continue
            text = path.read_text()
            for name in re.findall(r'"(FN_[A-Z_]+)"', text):
                if name.startswith(prefixes) or name == "FN_IMMUTABLE_PUBLISH_TEST_FAIL":
                    with self.subTest(path=path.name, name=name):
                        self.assertIn(name, selectors)
                        self.assertNotRegex(
                            text, r'posix-getenv\s+"' + name + r'"')

    def test_literal_build_inputs_exist(self):
        # Check the actual saved-image driver, not only Makefile proof roots.
        # A removed join book previously survived here and blocked every image.
        build = (ROOT / "host/native/build.lisp").read_text()
        inputs = re.findall(r'\((include-book|ld|load)\s+"([^"]+)"', build)
        self.assertTrue(inputs)
        for operation, name in inputs:
            with self.subTest(operation=operation, name=name):
                source = ROOT / (name + ".lisp" if operation == "include-book" else name)
                self.assertTrue(source.is_file(), f"missing native build input: {source}")

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
        self.assertIn('../libexec/fn/fn-host', launcher)
        self.assertIn('image=$root/build/fn-host', launcher)
        self.assertIn('native host core missing', launcher)
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


class RawPostEntryWitnesses(unittest.TestCase):
    def test_dtn_selector_gate_is_serialized(self):
        selector = {"FN_BP_TEST_DELIVER_FAULT": "1"}
        for image in (PRODUCTION, DTN):
            if not (image.is_file() and os.access(image, os.X_OK)):
                self.skipTest(f"build {image} for the saved-image witness")
            with self.subTest(image=image):
                refused = invoke(image, "bp", "unknown", environment_override=selector)
                self.assertEqual(refused.returncode, 5, refused.stderr.decode())
                self.assertIn(b"FN_BP_TEST_DELIVER_FAULT", refused.stderr)
        for image in (DEVELOPER, DTN_DEVELOPER):
            if not (image.is_file() and os.access(image, os.X_OK)):
                self.skipTest(f"build {image} for the saved-image witness")
            with self.subTest(image=image):
                dispatched = invoke(image, "bp", "unknown", environment_override=selector)
                self.assertEqual(dispatched.returncode, 5, dispatched.stderr.decode())
                self.assertIn(b"unknown bp command", dispatched.stderr)

    def test_production_images_refuse_raw_post_before_store_or_payload_io(self):
        for image in (PRODUCTION, DTN):
            if not (image.is_file() and os.access(image, os.X_OK)):
                self.skipTest(f"build {image} for the saved-image witness")
            with self.subTest(image=image), tempfile.TemporaryDirectory() as tmp:
                fresh = Path(tmp) / "fresh"
                payload = Path(tmp) / "absent-payload"
                args = ("store", str(fresh), "post", "<entry@test>",
                        str(payload), "-", "-", "fn.test")
                rejected = invoke(image, *args)
                self.assertEqual(rejected.returncode, 5, rejected.stderr.decode())
                self.assertIn(b"store post", rejected.stderr)
                self.assertFalse(fresh.exists())
                store = Path(tmp) / "existing"
                initialized = invoke(image, "store", str(store), "init", "fn.test")
                self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
                before = {p.relative_to(store): (p.stat().st_size, p.stat().st_mtime_ns)
                          for p in store.rglob("*")}
                rejected = invoke(image, "store", str(store), "post", "<entry@test>",
                                  str(payload), "-", "-", "fn.test")
                self.assertEqual(rejected.returncode, 5, rejected.stderr.decode())
                self.assertIn(b"store post", rejected.stderr)
                after = {p.relative_to(store): (p.stat().st_size, p.stat().st_mtime_ns)
                         for p in store.rglob("*")}
                self.assertEqual(after, before)
                self.assertFalse(payload.exists())
                recovered = invoke(image, "store", str(store), "recover")
                self.assertEqual(recovered.returncode, 0, recovered.stderr.decode())

    def test_developer_images_keep_raw_post(self):
        for image in (DEVELOPER, DTN_DEVELOPER):
            if not (image.is_file() and os.access(image, os.X_OK)):
                self.skipTest(f"build {image} for the saved-image witness")
            with self.subTest(image=image), tempfile.TemporaryDirectory() as tmp:
                store = Path(tmp) / "store"
                payload = Path(tmp) / "payload"
                payload.write_bytes(b"entry-profile developer diagnostic\r\n")
                initialized = invoke(image, "store", str(store), "init", "fn.test")
                self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
                posted = invoke(image, "store", str(store), "post", "<entry@test>",
                                str(payload), "-", "-", "fn.test")
                self.assertEqual(posted.returncode, 0, posted.stderr.decode())
                self.assertIn(b"committed sequence=", posted.stdout)


if __name__ == "__main__":
    unittest.main()
