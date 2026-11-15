"""Farm stages share the selected SSH identity; no remote commands execute."""
import contextlib
import io
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import farm


COUNTS = ("artifact-set fixture origin /fixture source source toolchain toolchain; "
          "installed 2, kept 0, missing 1, removed 0\n")


class FarmSSHTransport(unittest.TestCase):
    def selected_transport(self, commands, output):
        original = farm.ssh

        def selected(host, script, check=True):
            return original("fn@" + host, script, check=check)

        def run(command, **kwargs):
            commands.append((command, kwargs))
            self.assertEqual(command[-2], "fn@fixture-box")
            self.assertEqual(command[:4], ["ssh", "-n", "-o", "ConnectTimeout=10"])
            self.assertFalse(kwargs["check"])
            return subprocess.CompletedProcess(command, *output(command[-1]))

        return selected, run

    @unittest.skipUnless(shutil.which("rsync"), "rsync required for push controls")
    def test_push_preserves_remote_git_file_and_directory(self):
        # Exercise the actual rsync flags against temporary local directories.
        with tempfile.TemporaryDirectory() as directory:
            for kind in ("file", "directory"):
                with self.subTest(kind=kind):
                    source = Path(directory) / ("source-" + kind)
                    remote = Path(directory) / ("remote-" + kind)
                    source.mkdir()
                    remote.mkdir()
                    source_git, remote_git = source / ".git", remote / ".git"
                    if kind == "directory":
                        source_git.mkdir()
                        remote_git.mkdir()
                        source_git, remote_git = source_git / "HEAD", remote_git / "HEAD"
                    source_git.write_text("laptop Git metadata\n")
                    remote_git.write_text("forge Git metadata\n")
                    (source / "book.lisp").write_text('(in-package "ACL2")\n')

                    def local_rsync(command, **kwargs):
                        command = list(command)
                        self.assertEqual(command[0], "rsync")
                        self.assertEqual(command[-1], f"fixture-box:{remote}/")
                        self.assertFalse(kwargs["check"])
                        command[-1] = str(remote) + "/"
                        return subprocess.run(command, text=True, capture_output=True,
                                              check=False, timeout=10)

                    with mock.patch.object(farm, "ssh", return_value=subprocess.CompletedProcess([], 0, "")), \
                         mock.patch.object(farm, "run", side_effect=local_rsync):
                        farm.push("fixture-box", source, remote)
                    self.assertEqual(remote_git.read_text(), "forge Git metadata\n")
                    self.assertEqual((remote / "book.lisp").read_text(),
                                     (source / "book.lisp").read_text())

    def test_preflight_and_main_submit_share_selected_identity(self):
        commands = []
        selected, run = self.selected_transport(
            commands, lambda script: (0, COUNTS if script == "cache-preflight"
                                      else "FN_FARM_STARTED fixture-run 123\n", None))
        with tempfile.TemporaryDirectory() as directory, \
             mock.patch.object(farm, "ssh", side_effect=selected), \
             mock.patch.object(farm, "RUN", side_effect=run), \
             mock.patch.object(farm, "refuse_a_running_run_in_the_same_tree"), \
             mock.patch.object(farm, "push"), \
             mock.patch.object(farm, "cache_preflight_script", return_value="cache-preflight"), \
             mock.patch.object(farm, "remote_script", return_value="main-submit"), \
             mock.patch.object(farm, "remote_certify_id", return_value="certify-fixture"), \
             contextlib.redirect_stderr(io.StringIO()):
            root = Path(directory)
            identifier = farm._submit_locked(
                "fixture-box", root, ["books/example"], 1, 180, [],
                Path("/fixture"), False, None, None, False, None, False,
                None, None, (), "off", True, None, "fixture-run")
            self.assertEqual(identifier, "fixture-run")
            self.assertTrue(farm.record_path(root, identifier).is_file())
        self.assertEqual([command[-1] for command, _ in commands],
                         ["cache-preflight", "main-submit"])

    def test_cache_counts_share_selected_transport_and_keep_status_filter(self):
        for status, output, expected in ((0, "2\n", {"fixture-box": 2}),
                                         (255, "error: denied\n", {}),
                                         (0, "not-a-count\n", {})):
            with self.subTest(status=status, output=output):
                commands = []
                selected, run = self.selected_transport(
                    commands, lambda script: (status, output, None))
                with mock.patch.dict(farm.HOSTS, {"fixture-box": {"cache": "/cache"}}, clear=True), \
                     mock.patch.object(farm, "ssh", side_effect=selected), \
                     mock.patch.object(farm, "RUN", side_effect=run):
                    self.assertEqual(farm.matching_certificates(["key-a", "key-b"]), expected)
                self.assertEqual(len(commands), 1)
                self.assertIn("key-a\nkey-b\n", commands[0][0][-1])

    def test_preflight_refusal_keeps_merged_diagnostic_and_exit_status(self):
        commands = []
        selected, run = self.selected_transport(
            commands, lambda script: (14, "error: toolchain identity refused\n", None))
        with mock.patch.object(farm, "ssh", side_effect=selected), \
             mock.patch.object(farm, "RUN", side_effect=run):
            with self.assertRaises(farm.FarmError) as refused:
                farm.install_from_cache("fixture-box", Path("/fixture"),
                                        ["books/example"], [], False)
        message = str(refused.exception)
        self.assertIn("ACL2 was not started", message)
        self.assertIn("exit 14", message)
        self.assertIn("first error: error: toolchain identity refused", message)
        self.assertEqual(len(commands), 1)

    def test_explicit_closure_recertification_retains_status_one_counts(self):
        commands = []
        selected, run = self.selected_transport(commands, lambda script: (1, COUNTS, None))
        with mock.patch.object(farm, "ssh", side_effect=selected), \
             mock.patch.object(farm, "RUN", side_effect=run):
            counts = farm.install_from_cache("fixture-box", Path("/fixture"),
                                             ["books/example"], [], True)
        self.assertTrue(counts["recertify_closure"])
        self.assertEqual(counts["missing"], 1)


if __name__ == "__main__":
    unittest.main()
