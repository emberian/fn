"""Native outage/restart evidence for the durable BP lifecycle service."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpServiceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = ROOT / "build" / "fn-host-dtn"
        if not os.access(cls.image, os.X_OK):
            raise unittest.SkipTest(
                f"DTN native image missing: {cls.image} "
                "(FN_NATIVE_BUILD=host/native/build-dtn.lisp tools/build_native_host.sh)"
            )

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-bp-service-"))
        self.journal = self.tmp / "journal"
        self.adu = self.tmp / "adu"
        self.adu.write_bytes(b"hello lifecycle")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def invoke(self, *args, env=None):
        return subprocess.run(
            [str(self.image), "--fn", "bp-service", *map(str, args)],
            cwd=ROOT,
            env=env or self.env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
            text=True,
        )

    def run_outage(self, adu=None, env=None):
        return self.invoke(
            "run", "127.0.0.1", "1", adu or self.adu, self.journal,
            "dtn://fn-a/", "dtn://fn-b/", "work-1", "attempt-1", "0",
            env=env,
        )

    def records(self):
        return sorted((self.journal / "lifecycle").glob("*.fnb"))

    def test_outage_restart_duplicate_and_conflict(self):
        first = self.run_outage()
        self.assertEqual(first.returncode, 3, first.stderr)
        self.assertIn("BP queue accepted", first.stdout)
        self.assertIn("BP forwarding retained reason=uncertain", first.stdout)
        self.assertEqual(len(self.records()), 3)  # queued, attempting, requeued

        frontier = (self.journal / "sequence" / "frontier.fnb").read_bytes()
        resumed = self.invoke("resume", self.journal, "dtn://fn-a/")
        self.assertEqual(resumed.returncode, 3, resumed.stderr)
        self.assertIn("BP queue recovered jobs=1", resumed.stdout)
        self.assertEqual(len(self.records()), 5)

        duplicate = self.run_outage()
        self.assertEqual(duplicate.returncode, 3, duplicate.stderr)
        self.assertIn("status=duplicate", duplicate.stdout)
        self.assertEqual(
            (self.journal / "sequence" / "frontier.fnb").read_bytes(), frontier,
            "an idempotent enqueue must reuse its durable object binding",
        )

        contrary = self.tmp / "contrary"
        contrary.write_bytes(b"contrary bytes")
        conflict = self.run_outage(contrary)
        self.assertEqual(conflict.returncode, 3, conflict.stderr)
        self.assertIn("BP queue refused reason=enqueue-conflict", conflict.stdout)

    def test_shared_spool_owner_precedes_lifecycle_mutation(self):
        owner = subprocess.Popen(
            [str(self.image), "--fn", "tcpcl", "listen", "0", "1",
             str(self.journal), "dtn://fn-a/", "-", "4", "1024",
             "1048576", "-", "-"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True,
        )
        try:
            line = owner.stdout.readline()
            self.assertIn("TCPCL LISTENING", line)
            refused = self.run_outage()
            self.assertEqual(refused.returncode, 1, refused.stderr)
            self.assertIn("spool is already owned", refused.stderr)
            self.assertFalse((self.journal / "sequence").exists())
            self.assertFalse((self.journal / "lifecycle").exists())
            self.assertIsNone(owner.poll())
        finally:
            owner.kill()
            owner.wait(timeout=10)
            owner.stdout.close()

    def test_visible_final_never_converts_failed_barrier_to_durable(self):
        for variable in (
            "FN_BP_SERVICE_TEST_FAIL_FIRST_DIR_BARRIER",
            "FN_BP_SERVICE_TEST_FAIL_SECOND_DIR_BARRIER",
        ):
            with self.subTest(variable=variable):
                shutil.rmtree(self.journal, ignore_errors=True)
                injected_env = dict(self.env)
                injected_env[variable] = "1"
                cut = self.run_outage(env=injected_env)
                self.assertEqual(cut.returncode, 3, cut.stderr)
                self.assertIn("BP queue uncertain reason=persistence", cut.stdout)
                self.assertNotIn("BP queue accepted", cut.stdout)
                self.assertEqual(
                    len(self.records()), 1,
                    "the uncertain persist must fence before attempting/forwarding records",
                )

                recovered = self.invoke("resume", self.journal, "dtn://fn-a/")
                self.assertEqual(recovered.returncode, 3, recovered.stderr)
                self.assertIn("BP queue recovered jobs=1", recovered.stdout)
                self.assertNotIn("restart fenced", recovered.stderr)

    def test_transport_uncertain_dominates_refused_article(self):
        malformed = self.tmp / "malformed.bundle"
        malformed.write_bytes(b"not a BPv7 bundle")
        listener_log = self.tmp / "listener.log"
        sender_log = self.tmp / "sender.log"
        with listener_log.open("wb") as listener_output:
            listener = subprocess.Popen(
                [str(self.image), "--fn", "bp", "receive", "0", "1",
                 str(self.tmp / "bp-journal"), "dtn://fn-b/", "-",
                 "3600000", "2", "32", "1048576", str(self.adu),
                 "dtn://fn-a/", "-", "0"],
                cwd=ROOT, env=self.env, stdout=listener_output,
                stderr=subprocess.STDOUT,
            )
            sender = None
            try:
                deadline = time.time() + 15
                port = None
                while time.time() < deadline:
                    text = listener_log.read_text(errors="replace")
                    for line in text.splitlines():
                        if line.startswith("BP LISTENING "):
                            port = int(line.rsplit(" ", 1)[1])
                            break
                    if port is not None:
                        break
                    if listener.poll() is not None:
                        self.fail(f"listener exited before listen: {text}")
                    time.sleep(0.02)
                self.assertIsNotNone(port, "listener did not publish a port")

                with sender_log.open("wb") as sender_output:
                    sender_env = dict(self.env)
                    sender_env["FN_TCPCL_TEST_PAUSE_AFTER_STAGE_DATA"] = "1"
                    sender = subprocess.Popen(
                        [str(self.image), "--fn", "tcpcl", "send", "127.0.0.1",
                         str(port), str(malformed), str(self.tmp / "peer-journal"),
                         "dtn://fn-a/", "-", "4", "1024", "1048576", "1", "-"],
                        cwd=ROOT, env=sender_env, stdout=sender_output,
                        stderr=subprocess.STDOUT,
                    )
                    deadline = time.time() + 20
                    while time.time() < deadline:
                        refused = "BP refused xfer=" in listener_log.read_text(
                            errors="replace")
                        held_ack = "TCPCL TEST STAGE-DATA " in sender_log.read_text(
                            errors="replace")
                        if refused and held_ack:
                            break
                        if sender.poll() is not None:
                            break
                        time.sleep(0.02)
                    self.assertIn(
                        "BP refused xfer=", listener_log.read_text(errors="replace"),
                        "the mixed-outcome cut requires a reachable refused article",
                    )
                    self.assertIn(
                        "TCPCL TEST STAGE-DATA ",
                        sender_log.read_text(errors="replace"),
                        "the peer must still hold the reply's final ACK",
                    )
                    listener.wait(timeout=30)
                    sender.kill()
                    sender.wait(timeout=10)

                output = listener_log.read_text(errors="replace")
                self.assertIn("BP summary accepted=0 refused=1 uncertain=0", output)
                self.assertIn("TCPCL passive uncertain", output)
                self.assertEqual(listener.returncode, 3, output)
            finally:
                if listener.poll() is None:
                    listener.kill()
                    listener.wait(timeout=10)
                if sender is not None and sender.poll() is None:
                    sender.kill()
                    sender.wait(timeout=10)


if __name__ == "__main__":
    unittest.main()
