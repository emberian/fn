"""Actual native process death checked through the byte scan/reopen subject."""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

from tests.campaign import model_images


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_CRASH_HOST", ""))
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402


class NativeCrashFaultSurfaceTests(unittest.TestCase):
    def test_post_fault_environment_is_developer_image_only(self):
        source = (ROOT / "host/native/io.lisp").read_text()
        start = source.index("(defun fnn-post-test-fault")
        end = source.index("\n(defun fnn-command-post", start)
        body = source[start:end]
        self.assertIn("(fnn-developer-image-p)", body)
        self.assertIn("FN_NATIVE_POST_FAULT requires a developer image", body)


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "FN_NATIVE_CRASH_HOST must name a freshly built developer image")
class NativeCrashModelTests(unittest.TestCase):
    def invoke(self, store, command, *arguments, expected=0, env=None):
        host_env = dict(os.environ)
        host_env.update(env or {})
        host_env["FN_HOST"] = "native"
        host_env["FN_NATIVE_HOST"] = str(IMAGE)
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(store),
             command, *map(str, arguments)], cwd=ROOT, env=host_env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(result.returncode, expected,
                         "stdout={}\nstderr={}".format(result.stdout, result.stderr))
        return result

    def test_record_link_sigkill_scans_and_reopens_as_exact_commit(self):
        with tempfile.TemporaryDirectory(prefix="fn-native-crash-model-") as tmp:
            root = Path(tmp)
            store = root / "store"
            payload = root / "payload"
            payload.write_bytes(b"native crash model protected content")
            self.invoke(store, "init")

            killed_env = dict(os.environ)
            killed_env["FN_NATIVE_POST_FAULT"] = "record-linked:kill"
            killed = subprocess.run(
                [str(IMAGE), "--fn", "store", str(store), "post",
                 "<native-crash-model@example.invalid>", str(payload), "-", "-",
                 "fn.letters"], cwd=ROOT, env=killed_env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
            self.assertEqual(killed.returncode, -9, killed.stderr)

            frontier_before = (store / "allocation-frontier.json").read_bytes()
            names_before = sorted(path.name for path in (store / "transactions").iterdir())
            self.assertEqual(names_before, ["00000000000000000000.txn"])
            record_before = (store / "transactions" / names_before[0]).read_bytes()

            bridge = model_images.ModelBridge()
            try:
                bridge.call('(include-book "books/byte-store-keystones")')
                bridge.call("(defconst *fn-native-killed-image* {})".format(
                    model_images.import_image(store)))
                bridge.call("(defconst *fn-native-killed-scan* "
                            "(fn-bs-scan-store *fn-native-killed-image*))")
                observed = bridge.value(
                    "(let* ((scan *fn-native-killed-scan*)"
                    " (records (fn-bs-scan-records scan))"
                    " (opened (fn-sn-open-observed '(\"fn.letters\") 10000000"
                    "            (fn-bs-scan-frontier scan) records)))"
                    " (list (fn-bs-scan-okp scan) (fn-bs-scan-frontier scan)"
                    "       (len records) (fn-record-sequence (car records))"
                    "       (fn-record-txid (car records)) (fn-sn-open-okp opened)))")
                match = re.search(r"\(T\s+1\s+1\s+0\s+0\s+T\)\s*$", observed)
                self.assertIsNotNone(match, observed)
            finally:
                bridge.close()

            recovered = self.invoke(store, "recover")
            self.assertIn(b"transactions=1 articles=1", recovered.stdout)
            self.assertEqual((store / "allocation-frontier.json").read_bytes(),
                             frontier_before)
            self.assertEqual((store / "transactions" / names_before[0]).read_bytes(),
                             record_before)
            inspected = self.invoke(
                store, "inspect", "--message-id",
                "<native-crash-model@example.invalid>")
            self.assertEqual(inspected.stdout, payload.read_bytes())


if __name__ == "__main__":
    unittest.main()
