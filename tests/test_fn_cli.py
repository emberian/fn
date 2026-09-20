"""The operator surface: `bin/fn` from init to a running service and back.

One store, one owner process, one configuration file.  The sequence is the
one docs/operator.md documents: init, run, post, read the article back with
an independent NNTP client, look at the store, stop with SIGTERM, and show
that the writer lock came back so recovery and a configuration change
succeed afterwards.  The three outcomes are asserted on their three distinct
exit codes, never on message text alone.

This spawns exactly one ACL2 (inside the owner) for the service case; the
refusal cases spawn their own short-lived ones.
"""
import os
import select
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FN = ROOT / "bin" / "fn"
PY312 = "/opt/homebrew/bin/python3.12"

EXIT_OK = 0
EXIT_REFUSED = 1
EXIT_UNCERTAIN = 3
EXIT_FAULT = 4

ARTICLE = (b"From: operator@example.invalid\r\nSubject: first light\r\n"
           b"Newsgroups: fn.letters\r\nMessage-ID: <first@example.invalid>\r\n"
           b"\r\nThe node is up.\r\n")


class Service:
    """`fn run` as the operator starts it: a foreground process, then SIGTERM."""

    def __init__(self, config):
        self.config = config
        self.proc = None
        self.port = None
        self.control = None

    def start(self):
        self.proc = subprocess.Popen(
            [sys.executable, str(FN), "--config", str(self.config), "run"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        deadline = time.monotonic() + 300
        while time.monotonic() < deadline and not (self.port and self.control):
            ready, _, _ = select.select([self.proc.stdout], [], [], 0.5)
            if ready:
                line = self.proc.stdout.readline()
                if not line:
                    break
                if line.startswith(b"LISTENING "):
                    self.port = int(line.split()[1])
                elif line.startswith(b"CONTROL "):
                    self.control = line.split(None, 1)[1].strip().decode()
            if self.proc.poll() is not None:
                break
        if not (self.port and self.control):
            self.terminate()
            raise RuntimeError("fn run did not start")
        return self

    def terminate(self, expected=None):
        if self.proc is None:
            return None
        if self.proc.poll() is None:
            self.proc.send_signal(signal.SIGTERM)
        try:
            code = self.proc.wait(timeout=90)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            code = self.proc.wait(timeout=10)
        errors = self.proc.stderr.read()
        self.proc.stdout.close()
        self.proc.stderr.close()
        self.proc = None
        if expected is not None and code != expected:
            raise AssertionError("fn run exited {} (expected {}): {!r}".format(
                code, expected, errors))
        return code


class FnCliTests(unittest.TestCase):
    maxDiff = None

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-cli-")
        self.base = Path(self.temp.name)
        self.config = self.base / "fn.toml"
        self.store = self.base / "store"
        self.log = self.base / "fn.log"
        self.payload = self.base / "article"
        self.payload.write_bytes(ARTICLE)
        self.service = None

    def tearDown(self):
        if self.service is not None:
            self.service.terminate()
        self.temp.cleanup()

    # -- helpers ----------------------------------------------------------
    def fn(self, *arguments, config=True, expected=EXIT_OK):
        command = [sys.executable, str(FN)]
        if config:
            command += ["--config", str(self.config)]
        command += [str(argument) for argument in arguments]
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=600)
        if expected is not None and result.returncode != expected:
            self.fail("fn {} exited {} (expected {})\nstdout={!r}\nstderr={!r}".format(
                " ".join(map(str, arguments)), result.returncode, expected,
                result.stdout, result.stderr))
        # Exactly one outcome line on stderr, and its first word is the outcome.
        lines = [line for line in result.stderr.decode().splitlines() if line.strip()]
        self.assertEqual(len(lines), 1, result.stderr)
        self.assertIn(lines[0].split()[0],
                      ("accepted", "refused", "uncertain", "fault", "usage"))
        return result

    def fn_init(self):
        result = subprocess.run(
            [sys.executable, str(FN), "--config", str(self.config), "init",
             "--store", str(self.store), "--group", "fn.letters", "--group", "fn.test",
             "--listen", "127.0.0.1:0", "--agent", "operator@example.invalid",
             "--log", str(self.log)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
        self.assertEqual(result.returncode, EXIT_OK, result.stderr)
        self.assertTrue(result.stderr.decode().startswith("accepted init "), result.stderr)
        return result

    # -- the whole operator sequence --------------------------------------
    def test_init_run_post_read_group_status_sigterm_recover(self):
        self.fn_init()
        self.assertTrue(self.config.is_file())
        self.assertTrue((self.store / "writer.lock").is_file())
        self.assertIn('host = "127.0.0.1"', self.config.read_text())

        self.service = Service(self.config).start()
        self.assertTrue(Path(self.service.control).exists())

        # POST goes through the running owner's control socket.
        posted = self.fn("post", "--message-id", "<first@example.invalid>",
                         "--payload", self.payload, "--group", "fn.letters")
        self.assertIn(b"committed sequence=0", posted.stdout)
        self.assertIn(b"path=control", posted.stderr)

        # An independent client reads it back through the running server.
        if os.path.exists(PY312):
            probe = subprocess.run(
                [PY312, str(ROOT / "tests" / "interop_fn_cli_nntplib.py"),
                 str(self.service.port), "fn.letters", "<first@example.invalid>"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
            self.assertEqual(probe.returncode, 0, probe.stdout + probe.stderr)
            self.assertIn(b"read <first@example.invalid>", probe.stdout)

        # A configuration record needs the writer lock the owner holds: the
        # answer while the service is live is a refusal, distinctly.
        live = self.fn("group", "create", "fn.announce", expected=EXIT_REFUSED)
        self.assertIn(b"an owner is live", live.stderr)

        # Status sees the owner and reports what the control channel answers.
        status = self.fn("status")
        self.assertIn(b"owner=live", status.stdout)
        self.assertIn(b"version 1", status.stdout)

        # SIGTERM is the clean stop: exit 0 and the writer lock released.
        self.assertEqual(self.service.terminate(expected=EXIT_OK), EXIT_OK)
        self.service = None
        self.assertFalse(Path(self.store / "control.sock").exists())

        # The lock really came back: recovery and a group change both succeed.
        recovered = self.fn("recover")
        self.assertIn(b"recovered transactions=1 articles=1", recovered.stdout)
        self.assertIn(b"anchor=none", recovered.stdout)
        created = self.fn("group", "create", "fn.announce")
        self.assertIn(b"group created name=fn.announce generation=2", created.stdout)
        after = self.fn("status")
        self.assertIn(b"owner=absent generation=2 transactions=1 articles=1", after.stdout)
        self.assertIn(b"anchor=none", after.stdout)

        # The service log carries one outcome-first line per post and per
        # reader connection.
        log = self.log.read_text().splitlines()
        self.assertTrue(any(line.startswith("accepted post path=control "
                                            "message-id=<first@example.invalid>")
                            for line in log), log)
        self.assertTrue(any(line.startswith("accepted shutdown reason=sigterm") for line in log),
                        log)
        if os.path.exists(PY312):
            self.assertTrue(any(line.startswith("accepted reader connection=") for line in log),
                            log)

    # -- the three outcomes on three codes --------------------------------
    def test_a_refused_post_and_a_missing_store_are_distinct_codes(self):
        self.fn_init()
        refused = self.fn("post", "--message-id", "<nogroup@example.invalid>",
                          "--payload", self.payload, "--group", "fn.absent",
                          expected=EXIT_REFUSED)
        self.assertTrue(refused.stderr.decode().startswith("refused post "), refused.stderr)

        missing = self.base / "missing.toml"
        missing.write_text('[store]\npath = "{}"\n'.format(self.base / "no-such-store"))
        result = subprocess.run(
            [sys.executable, str(FN), "--config", str(missing), "post",
             "--message-id", "<gone@example.invalid>", "--payload", str(self.payload),
             "--group", "fn.letters"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
        self.assertEqual(result.returncode, EXIT_FAULT, result.stderr)
        self.assertTrue(result.stderr.decode().startswith("fault post "), result.stderr)
        self.assertNotEqual(EXIT_REFUSED, EXIT_FAULT)
        self.assertNotEqual(EXIT_UNCERTAIN, EXIT_REFUSED)

    def test_a_non_loopback_listener_is_refused_before_anything_starts(self):
        self.fn_init()
        self.config.write_text(self.config.read_text().replace(
            'host = "127.0.0.1"', 'host = "0.0.0.0"'))
        refused = self.fn("run", expected=EXIT_REFUSED)
        self.assertIn(b"is not loopback", refused.stderr)

    def test_a_missing_configuration_is_refused_not_faulted(self):
        result = subprocess.run(
            [sys.executable, str(FN), "--config", str(self.base / "absent.toml"), "status"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
        self.assertEqual(result.returncode, EXIT_REFUSED, result.stderr)
        self.assertTrue(result.stderr.decode().startswith("refused status "), result.stderr)


if __name__ == "__main__":
    unittest.main()
