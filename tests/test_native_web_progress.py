"""The deployed web consumers distinguish request, render and send time."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class WebProgressTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_request_render_and_send_have_separate_deadlines(self):
        run = subprocess.run(
            ["sbcl", "--noinform", "--script", "tests/native_web_progress_raw-mock.lisp"],
            capture_output=True, text=True, timeout=20)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("quantum reset passed", run.stdout)

    @unittest.skipUnless(shutil.which("sbcl"), "SBCL required")
    def test_old_deadline_and_quantum_age_are_refuted(self):
        source = Path("host/native/web-host.lisp").read_text()
        mutations = {
            "total-request-time": source.replace(
                "          ;; ACL2's read-size reached zero: the complete request arrived.\n"
                "          (fnn-web-conn-deadline conn) nil\n", ""),
            "accumulated-cold-age": source.replace(
                "                (t (setf (fnn-web-conn-line-since conn) nil)\n"
                "                   (if (fnn-web-conn-reply-scan conn)",
                "                (t (if (fnn-web-conn-reply-scan conn)"),
        }
        for name, mutant in mutations.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                self.assertNotEqual(source, mutant)
                path = Path(directory) / "web-host.lisp"
                path.write_text(mutant)
                run = subprocess.run(
                    ["sbcl", "--noinform", "--script", "tests/native_web_progress_raw-mock.lisp"],
                    env={**os.environ, "FN_WEB_PROGRESS_SOURCE": str(path)},
                    capture_output=True, text=True, timeout=20)
                self.assertNotEqual(run.returncode, 0, run.stdout + run.stderr)
                self.assertIn("assertion", run.stderr.lower())
