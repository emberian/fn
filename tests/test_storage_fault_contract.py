"""The CLI forwards fault contracts without granting or normalizing assumptions."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("fn_admin", ROOT / "tools/fn_admin.py")
admin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(admin)


class Launched(Exception):
    pass


class StorageFaultContractTests(unittest.TestCase):
    def test_init_defers_default_and_validation_to_acl2(self):
        with tempfile.TemporaryDirectory() as directory:
            image = Path(directory) / "node.img"
            for supplied in (None, "crash-only", "invalid #.(not-a-reader)"):
                with self.subTest(supplied=supplied), \
                     patch.dict(admin.os.environ, {}, clear=True), \
                     patch.object(admin, "prepare_native_crypto"), \
                     patch.object(admin.subprocess, "call", return_value=2) as launch:
                    options = [] if supplied is None else ["--storage-fault-model", supplied]
                    self.assertEqual(admin.main(["init", str(image), *options], root=ROOT), 2)
                    env = launch.call_args.kwargs["env"]
                    if supplied is None:
                        self.assertNotIn("FN2_STORAGE_FAULT_MODEL", env)
                    else:
                        self.assertEqual(env["FN2_STORAGE_FAULT_MODEL"], supplied)

    def test_serve_inherits_or_forwards_explicit_text_exactly(self):
        with tempfile.TemporaryDirectory() as directory:
            image = Path(directory) / "node.img"
            image.write_bytes(b"preserved fixture")
            for supplied in (None, "broad", "CRASH-ONLY-invalid"):
                with self.subTest(supplied=supplied), \
                     patch.dict(admin.os.environ, {"FN2_STORAGE_FAULT_MODEL": "crash-only"}), \
                     patch.object(admin, "prepare_native_crypto"), \
                     patch.object(admin.os, "chdir"), patch.object(admin.os, "dup2"), \
                     patch.object(admin.os, "execve", side_effect=Launched) as launch:
                    options = [] if supplied is None else ["--storage-fault-model", supplied]
                    with self.assertRaises(Launched):
                        admin.main(["serve", str(image), *options], root=ROOT)
                    self.assertEqual(launch.call_args.args[2]["FN2_STORAGE_FAULT_MODEL"],
                                     "crash-only" if supplied is None else supplied)
            self.assertEqual(image.read_bytes(), b"preserved fixture")


if __name__ == "__main__":
    unittest.main()
