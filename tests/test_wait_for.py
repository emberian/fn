"""tools/wait_for.sh: the one background-safe wait (friction review section 8).

Real local children; --host tests use fake ssh and never make a connection.
"""
import os
from contextlib import contextmanager
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
WAIT = ROOT / "tools" / "wait_for.sh"


def wait_for(*words, timeout=30, env=None):
    return subprocess.run(["sh", str(WAIT), "--interval", "1", *words],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, timeout=timeout, env=env)


@contextmanager
def started_child(directory, *command):
    """Stop only this test's child, using the PID recorded in its PID file."""
    child = subprocess.Popen(command)
    pid_file = Path(directory) / "child.pid"
    pid_file.write_text(f"{child.pid}\n")
    try:
        yield child, pid_file
    finally:
        if child.poll() is None:
            pid = int(pid_file.read_text())
            if pid != child.pid:
                raise AssertionError("test child's PID file changed")
            try:
                os.kill(pid, signal.SIGTERM)
            except ProcessLookupError:
                pass  # It exited between poll and the PID-specific signal.
        child.wait(timeout=5)


class WaitForTests(unittest.TestCase):
    def test_pid_file_waits_for_exit(self):
        with tempfile.TemporaryDirectory() as directory:
            with started_child(directory, "sleep", "2") as (child, pid_file):
                started = time.monotonic()
                done = wait_for("--deadline", "20", "--pid-file", str(pid_file))
                self.assertGreaterEqual(time.monotonic() - started, 1)
                child.wait(timeout=5)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, f"pid {child.pid} exited\n")

    def test_log_match_wins_while_pid_still_runs(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "worker's log"
            with started_child(directory, sys.executable, "-c",
                               "import pathlib, sys, time; time.sleep(1); "
                               "pathlib.Path(sys.argv[1]).write_text('FN_READY 7\\n'); "
                               "time.sleep(30)", str(log)) as (child, _):
                done = wait_for("--pid", str(child.pid), "--log", str(log),
                                "FN_READY [0-9]+", "--deadline", "20")
                self.assertIsNone(child.poll())
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, "FN_READY 7\n")

    def test_pid_file_exit_without_match_prints_last_five_lines(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "run.log"
            log.write_text("".join(f"line {i}\n" for i in range(8)))
            with started_child(directory, "sleep", "2") as (child, pid_file):
                done = wait_for("--log", str(log), "FN_READY", "--pid-file",
                                str(pid_file), "--deadline", "20")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, f"pid {child.pid} exited\n" +
                         "".join(f"line {i}\n" for i in range(3, 8)))

    def test_pid_exit_with_missing_log_still_succeeds(self):
        with tempfile.TemporaryDirectory() as directory:
            with started_child(directory, "sleep", "1") as (child, _):
                done = wait_for("--log", str(Path(directory) / "absent"), "READY",
                                "--pid", str(child.pid), "--deadline", "20")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, f"pid {child.pid} exited\n")

    def test_silent_log_is_stalled_without_stopping_child(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "silent.log"
            log.write_text("started\n")
            with started_child(directory, "sleep", "30") as (child, pid_file):
                done = wait_for("--pid-file", str(pid_file), "--log", str(log),
                                "READY", "--max-idle", ".04", "--deadline", "20")
                self.assertIsNone(child.poll())
        self.assertEqual(done.returncode, 5, done.stderr)
        self.assertEqual(done.stdout, "")
        self.assertRegex(done.stderr, rf"^wait_for: STALLED {log} idle [0-9.]+m\n$")

    def test_growing_log_resets_idle_until_match(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "growing.log"
            with started_child(directory, sys.executable, "-c",
                               "import sys, time\n"
                               "with open(sys.argv[1], 'w') as log:\n"
                               " for i in range(10):\n"
                               "  log.write('working\\n'); log.flush(); time.sleep(.5)\n"
                               " log.write('READY\\n'); log.flush(); time.sleep(1)\n",
                               str(log)) as (_, pid_file):
                done = wait_for("--log", str(log), "READY", "--pid-file",
                                str(pid_file), "--max-idle", ".04", "--deadline", "20")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, "READY\n")

    def test_any_repeatable_watch_mtime_resets_idle(self):
        with tempfile.TemporaryDirectory() as directory:
            silent = Path(directory) / "silent"
            active = Path(directory) / "it's active"
            ready = Path(directory) / "ready"
            silent.touch()
            active.write_text("constant size")
            with started_child(directory, sys.executable, "-c",
                               "import os, pathlib, sys, time\n"
                               "for i in range(10):\n"
                               " os.utime(sys.argv[1], None); time.sleep(.5)\n"
                               "pathlib.Path(sys.argv[2]).write_text('done')\n",
                               str(active), str(ready)):
                done = wait_for("--watch", str(silent), "--file", str(ready),
                                "--watch", str(active), "--max-idle", ".04",
                                "--deadline", "20")
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, "")

    def test_gnu_stat_growth_resets_idle(self):
        with tempfile.TemporaryDirectory() as directory:
            fake = Path(directory) / "stat"
            fake.write_text(f"#!{sys.executable}\n"
                            "import os, sys\n"
                            "if sys.argv[1:5] != ['-L', '-c', '%y:%s', '--']:\n"
                            " sys.exit(1)\n"
                            "s = os.stat(sys.argv[5])\n"
                            "print(f'{s.st_mtime_ns}:{s.st_size}')\n")
            fake.chmod(0o755)
            env = dict(os.environ, PATH=f"{directory}:{os.environ['PATH']}")
            log = Path(directory) / "growing"
            with started_child(directory, sys.executable, "-c",
                               "import sys, time\n"
                               "with open(sys.argv[1], 'w') as log:\n"
                               " for i in range(10):\n"
                               "  log.write('working\\n'); log.flush(); time.sleep(.5)\n"
                               " log.write('READY\\n')\n", str(log)):
                done = wait_for("--log", str(log), "READY", "--max-idle", ".04",
                                "--deadline", "20", env=env)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout, "READY\n")

    def test_pid_file_usage_refusals_are_immediate(self):
        with tempfile.TemporaryDirectory() as directory:
            pid_file = Path(directory) / "worker.pid"
            for contents in (None, "", "abc\n", "1\n2\n"):
                with self.subTest(contents=contents):
                    if contents is not None:
                        pid_file.write_text(contents)
                    started = time.monotonic()
                    done = wait_for("--pid-file", str(pid_file), "--deadline", "20")
                    self.assertEqual(done.returncode, 2, done.stderr)
                    self.assertIn("--pid-file must contain a PID", done.stderr)
                    self.assertLess(time.monotonic() - started, 1)

    def test_idle_usage_refusals(self):
        for minutes in ("0", "-1", "x", "1.2.3", ""):
            with self.subTest(minutes=minutes):
                self.assertEqual(wait_for("--log", "/absent", "READY",
                                          "--max-idle", minutes).returncode, 2)
        self.assertEqual(wait_for("--file", "/absent", "--max-idle", "1").returncode, 2)

    def test_host_reads_pid_file_and_watches_over_shared_connection(self):
        with tempfile.TemporaryDirectory() as directory:
            # A fake host has its own cwd; relative paths exist only there.
            # Execute only the supplied remote snippet, never a real ssh.
            fake = Path(directory) / "ssh"
            fake.write_text("#!/bin/sh\n"
                            "printf '%s\\n' \"$*\" >> \"$FAKE_SSH_CALLS\"\n"
                            "for snippet do :; done\n"
                            "cd \"$FAKE_SSH_ROOT\" || exit 1\n"
                            "exec sh -c \"$snippet\"\n")
            fake.chmod(0o755)
            calls = Path(directory) / "calls"
            env = dict(os.environ, PATH=f"{directory}:{os.environ['PATH']}",
                       FAKE_SSH_ROOT=directory, FAKE_SSH_CALLS=str(calls))
            (Path(directory) / "log").write_text("working\n")
            with started_child(directory, "sleep", "30") as (child, _):
                done = subprocess.run(
                    ["sh", str(WAIT), "--host", "fake", "--interval", "1",
                     "--deadline", "20", "--pid-file", "child.pid", "--log", "log",
                     "READY", "--max-idle", ".04", "--watch", "extra"],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                    timeout=30, env=env)
                self.assertIsNone(child.poll())
                (Path(directory) / "log").write_text("READY\n")
                matched = wait_for("--host", "fake", "--pid-file", "child.pid",
                                   "--log", "log", "READY", "--deadline", "20", env=env)
                self.assertEqual(matched.returncode, 0, matched.stderr)
                self.assertEqual(matched.stdout, "READY\n")
                self.assertIsNone(child.poll())
                missing = wait_for("--host", "fake", "--pid-file", "missing.pid",
                                   "--deadline", "20", env=env)
                self.assertEqual(missing.returncode, 2, missing.stderr)
            self.assertGreaterEqual(len(calls.read_text().splitlines()), 3)
            for flag in ("ControlMaster=auto", "ControlPersist=600", "ControlPath="):
                self.assertIn(flag, calls.read_text())
        self.assertEqual(done.returncode, 5, done.stderr)
        self.assertIn("wait_for: STALLED extra idle", done.stderr)

    def test_log_marker_that_appears_later_is_printed_and_met(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "run.log"
            writer = subprocess.Popen(
                ["sh", "-c", f"sleep 2; echo 'build done: FN_READY 7' > '{log}'"])
            try:
                done = wait_for("--deadline", "20", "--log", str(log), "FN_READY [0-9]+")
            finally:
                writer.wait()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout.strip(), "build done: FN_READY 7")

    def test_deadline_is_124_not_success(self):
        with tempfile.TemporaryDirectory() as directory:
            done = wait_for("--deadline", "1", "--file", str(Path(directory) / "never"))
        self.assertEqual(done.returncode, 124)
        self.assertIn("deadline 1s passed", done.stderr)

    def test_pid_waits_for_exit_without_matching_patterns(self):
        child = subprocess.Popen(["sleep", "2"])
        started = time.monotonic()
        done = wait_for("--deadline", "20", "--pid", str(child.pid))
        child.wait()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertGreaterEqual(time.monotonic() - started, 1)
        self.assertIn(f"pid {child.pid} exited", done.stdout)

    def test_farm_status_returns_the_runs_own_code(self):
        with tempfile.TemporaryDirectory() as directory:
            status = Path(directory) / "build/farm/run-a.status"
            status.parent.mkdir(parents=True)
            status.write_text("3\n")
            done = wait_for("--deadline", "5", "--farm", "run-a", directory)
        self.assertEqual(done.returncode, 3)
        self.assertIn("finished with exit code 3", done.stderr)

    def test_a_quote_in_a_path_is_one_word(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "it's here"
            path.write_text("x")
            done = wait_for("--deadline", "5", "--file", str(path))
        self.assertEqual(done.returncode, 0, done.stderr)

    def test_options_may_follow_the_condition(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "there"
            path.write_text("x")
            done = subprocess.run(["sh", str(WAIT), "--file", str(path), "--deadline", "5",
                                   "--interval", "1"],
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  text=True, timeout=30)
            self.assertEqual(done.returncode, 0, done.stderr)
            late = wait_for("--file", str(Path(directory) / "never"), "--deadline", "1")
        self.assertEqual(late.returncode, 124, late.stderr)
        self.assertIn("deadline 1s passed", late.stderr)

    def test_an_unobservable_host_is_4_and_quotes_ssh(self):
        with tempfile.TemporaryDirectory() as directory:
            fake = Path(directory) / "ssh"
            fake.write_text("#!/bin/sh\necho 'kex_exchange_identification: "
                            "Connection closed by remote host' >&2\nexit 255\n")
            fake.chmod(0o755)
            env = dict(os.environ, PATH=f"{directory}:{os.environ['PATH']}",
                       FN_WAIT_FOR_UNOBSERVED_S="0")
            done = subprocess.run(["sh", str(WAIT), "--host", "nowhere", "--interval", "1",
                                   "--deadline", "60", "--file", "/x"],
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  text=True, timeout=60, env=env)
        self.assertEqual(done.returncode, 4, done.stderr)
        self.assertIn("Connection closed by remote host", done.stderr)

    def test_usage_errors_are_2(self):
        self.assertEqual(wait_for("--file", "/", "--pid", "1").returncode, 2)
        self.assertEqual(wait_for("--pid", "abc").returncode, 2)
        self.assertEqual(wait_for("--deadline", "x", "--file", "/").returncode, 2)
        self.assertEqual(wait_for().returncode, 2)


if __name__ == "__main__":
    unittest.main()
