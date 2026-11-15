"""Local fake transports exercise bounded collection; no remote or cache use."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import farm


class FarmEvidenceFetch(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.local = self.root / "evidence"
        self.local.mkdir()
        self.manifest = self.local / "manifest.json"
        self.old = '{"fixture": "previous valid manifest"}\n'
        self.manifest.write_text(self.old)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.fake("ssh", '''import os, subprocess, sys, time
if os.environ.get("FIXTURE_SSH_MODE") == "hang":
    subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    time.sleep(60)
sys.stdout.write(os.environ.get("FIXTURE_SSH_OUTPUT", "{}"))
sys.stderr.write("fixture transport stderr\\n")
sys.exit(int(os.environ.get("FIXTURE_SSH_EXIT", "0")))
''')
        self.fake("rsync", '''import os, subprocess, sys, time
with open(os.environ["FIXTURE_RSYNC_CALLS"], "a") as stream:
    stream.write(" ".join(sys.argv[1:]) + "\\n")
subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
time.sleep(60)
''')
        patch = mock.patch.dict(os.environ, {
            "PATH": str(self.bin) + os.pathsep + os.environ.get("PATH", ""),
            "FIXTURE_SSH_OUTPUT": '{"fixture": "new manifest"}\n',
            "FIXTURE_SSH_MODE": "normal", "FIXTURE_SSH_EXIT": "0",
            "FIXTURE_RSYNC_CALLS": str(self.root / "rsync-calls"),
        })
        patch.start()
        self.addCleanup(patch.stop)
        patch = mock.patch.object(farm, "EVIDENCE_TIMEOUT_SECONDS", 0.2)
        patch.start()
        self.addCleanup(patch.stop)

    def fake(self, name, body):
        path = self.bin / name
        path.write_text(f"#!{sys.executable}\n" + body)
        path.chmod(0o755)

    def test_manifest_json_validates_before_atomic_replace_and_separates_stderr(self):
        original = Path.replace
        replacements = []

        def replace(path, target):
            self.assertEqual(self.manifest.read_text(), self.old)
            self.assertEqual(json.loads(path.read_text()), {"fixture": "new manifest"})
            replacements.append(target)
            return original(path, target)

        with mock.patch.object(Path, "replace", replace):
            self.assertTrue(farm.fetch_manifest("fixture", Path("/remote"), "run", self.local))
        self.assertEqual(replacements, [self.manifest])
        self.assertEqual(json.loads(self.manifest.read_text()), {"fixture": "new manifest"})

    def test_failed_invalid_and_timed_out_manifest_preserve_valid_local_bytes(self):
        for settings in ({"FIXTURE_SSH_EXIT": "1"},
                         {"FIXTURE_SSH_OUTPUT": "invalid JSON"},
                         {"FIXTURE_SSH_OUTPUT": "[]"},
                         {"FIXTURE_SSH_MODE": "hang"}):
            with self.subTest(settings=settings), mock.patch.dict(os.environ, settings), \
                 contextlib.redirect_stderr(io.StringIO()) as errors:
                started = time.monotonic()
                self.assertFalse(farm.fetch_manifest("fixture", Path("/remote"), "run", self.local))
                self.assertLess(time.monotonic() - started, 3)
                self.assertEqual(self.manifest.read_text(), self.old)
                self.assertEqual(list(self.local.glob(".manifest-*")), [])
                self.assertIn("manifest collection failed", errors.getvalue())

    def test_hung_bulk_transport_is_bounded_without_retry_or_manifest_refetch(self):
        with contextlib.redirect_stderr(io.StringIO()) as errors:
            started = time.monotonic()
            self.assertFalse(farm.fetch_evidence_dir("fixture", Path("/remote"), "run", self.local))
            self.assertLess(time.monotonic() - started, 3)
        calls = (self.root / "rsync-calls").read_text().splitlines()
        self.assertEqual(len(calls), 1)
        self.assertIn("--exclude=manifest.json", calls[0])
        self.assertNotIn("--include=manifest.json", calls[0])
        self.assertEqual(json.loads(self.manifest.read_text()), {"fixture": "new manifest"})
        self.assertIn("artifact collection incomplete", errors.getvalue())

    def test_missing_requested_manifest_never_publishes_pairs(self):
        with mock.patch.dict(os.environ, {"FIXTURE_SSH_OUTPUT": "no evidence directory\n"}), \
             mock.patch.object(farm.certs, "publish") as publish, \
             mock.patch.object(farm, "MIRROR") as mirror, \
             contextlib.redirect_stderr(io.StringIO()) as errors:
            self.assertFalse(farm.fetch("fixture", "run-fixture", self.root, Path("/remote")))
        publish.assert_not_called()
        mirror.assert_not_called()
        self.assertIn("collection incomplete: no certification manifest", errors.getvalue())
        self.assertFalse((self.root / "rsync-calls").exists())

    def test_incomplete_collection_keeps_remote_pass_and_failure_results(self):
        for code, verdict in ((0, "passed"), (1, "failed")):
            with self.subTest(code=code), \
                 mock.patch.object(farm, "ssh", return_value=subprocess.CompletedProcess(
                     [], 0, f"STATUS {code}\nMANIFEST {verdict} certify-fixture\nKNOWN yes\n")), \
                 mock.patch.object(farm, "note_certify_id") as note_id, \
                 mock.patch.object(farm, "note_box_manifest") as note_verdict, \
                 contextlib.redirect_stdout(io.StringIO()) as output:
                def collect(*args):
                    note_id.assert_called_once()
                    note_verdict.assert_called_once()
                    return False
                self.assertEqual(farm.wait("fixture", "run-fixture", self.root,
                                           remote="/remote", collect=collect), code)
                self.assertIn("collection incomplete; remote verdict unchanged", output.getvalue())

    def test_publish_timeout_keeps_manifest_and_still_verifies_local_publication(self):
        evidence = "build/acl2/fixture"
        original = farm.ssh
        report = mock.Mock(cache_entries=[])
        report.lines.return_value = []

        def ssh(host, script, **options):
            if script == "publish-fixture":
                self.assertEqual(options["timeout"], farm.EVIDENCE_TIMEOUT_SECONDS)
                raise subprocess.TimeoutExpired(["fixture-publish"], options["timeout"])
            return original(host, script, **options)

        with mock.patch.object(farm, "fetch_run_log", return_value=f"Certification evidence: {evidence}\n"), \
             mock.patch.object(farm, "ssh", side_effect=ssh), \
             mock.patch.object(farm, "fetch_transfer", return_value=True), \
             mock.patch.object(farm, "certs_script", return_value="publish-fixture"), \
             mock.patch.object(farm.certs, "load_manifests", return_value=[{"fixture": "new manifest"}]), \
             mock.patch.object(farm.certs, "certified_books", return_value=[]), \
             mock.patch.object(farm.certs, "publish", return_value=report) as publish, \
             mock.patch.object(farm, "MIRROR") as mirror, \
             contextlib.redirect_stderr(io.StringIO()) as errors:
            self.assertFalse(farm.fetch("fixture", "run-fixture", self.root,
                                        Path("/remote"), cache="fixture-cache"))
        publish.assert_called_once()
        mirror.assert_not_called()
        self.assertEqual(json.loads((self.root / evidence / "manifest.json").read_text()),
                         {"fixture": "new manifest"})
        self.assertIn("cache sweep incomplete", errors.getvalue())
        self.assertIn("existing remote cache state is unknown", errors.getvalue())
        self.assertNotIn("NOT in", errors.getvalue())

    def test_mirror_existing_runner_seam_has_deadline_and_separate_streams(self):
        import cert_cache_sync

        def sync(source, target, hours, *, since, entries, run):
            self.assertEqual((source, target, since, entries),
                             ("fixture", "other-fixture", 123, ["fixture-entry"]))
            response = run(["ssh", "fixture", "read"], input="fixture input",
                           capture_output=True, text=True)
            self.assertEqual(json.loads(response.stdout), {"fixture": "new manifest"})
            self.assertEqual(response.stderr, "fixture transport stderr\n")
            with mock.patch.dict(os.environ, {"FIXTURE_SSH_MODE": "hang"}):
                run(["ssh", "fixture", "hang"], capture_output=True, text=True)

        with mock.patch.dict(farm.HOSTS, {"fixture": {}, "other-fixture": {}}, clear=True), \
             mock.patch.object(cert_cache_sync, "sync", side_effect=sync):
            started = time.monotonic()
            with self.assertRaises(subprocess.TimeoutExpired):
                farm.mirror_cache("fixture", 123, ["fixture-entry"])
            self.assertLess(time.monotonic() - started, 3)


if __name__ == "__main__":
    unittest.main()
