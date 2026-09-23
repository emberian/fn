"""Native BP receive evidence identity, fencing, and fault taxonomy."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent


class NativeBpReceiveIntegrityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.image = ROOT / "build" / "fn-host-dtn"
        if not os.access(cls.image, os.X_OK):
            raise unittest.SkipTest(f"DTN native image missing: {cls.image}")

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-bp-receive-integrity-"))
        self.journal = self.tmp / "journal"
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.processes = []

    def tearDown(self):
        for process in self.processes:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=10)
            if getattr(process, "_fn_log_handle", None):
                process._fn_log_handle.close()
        shutil.rmtree(self.tmp)

    def spawn_receive(self, name, *, once="1", env=None):
        log = self.tmp / f"{name}.log"
        handle = log.open("wb")
        process = subprocess.Popen(
            [str(self.image), "--fn", "bp", "receive", "0", once,
             str(self.journal), "dtn://fn-b/", "-", "3600000", "2", "32",
             "1048576", "-", "-", "-", "0"],
            cwd=ROOT, env=env or self.env, stdout=handle,
            stderr=subprocess.STDOUT,
        )
        process._fn_log_handle = handle
        process._fn_log_path = log
        self.processes.append(process)
        deadline = time.time() + 15
        while time.time() < deadline:
            text = log.read_text(errors="replace")
            for line in text.splitlines():
                if line.startswith("BP LISTENING "):
                    return process, int(line.rsplit(" ", 1)[1])
            if process.poll() is not None:
                self.fail(f"receiver exited before listen: {text}")
            time.sleep(0.02)
        self.fail("receiver did not publish a port")

    def send(self, port, payload, name):
        source = self.tmp / f"{name}.bundle"
        source.write_bytes(payload)
        return subprocess.run(
            [str(self.image), "--fn", "tcpcl", "send", "127.0.0.1", str(port),
             str(source), str(self.tmp / f"{name}-peer"), "dtn://fn-a/", "-",
             "4", "1024", "1048576", "0", "-"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=30, check=False, text=True,
        )

    def wait_for_wire_count(self, count, timeout=15):
        evidence = self.journal / "receive-evidence"
        deadline = time.time() + timeout
        while time.time() < deadline:
            wires = sorted(evidence.glob("*.wire")) if evidence.exists() else []
            if len(wires) >= count:
                return wires
            time.sleep(0.02)
        self.fail(f"did not observe {count} durable wire records")

    def test_receive_core_fault_remains_exit_four(self):
        fault_env = dict(self.env)
        fault_env["FN_BP_TEST_DELIVER_FAULT"] = "1"
        receiver, port = self.spawn_receive("fault", env=fault_env)
        self.send(port, b"trigger receive callback", "fault-input")
        receiver.wait(timeout=20)
        output = receiver._fn_log_path.read_text(errors="replace")
        self.assertEqual(receiver.returncode, 4, output)
        self.assertIn("injected receive core fault", output)
        self.assertNotIn("BP refused xfer=", output)

    def test_two_sessions_reusing_transfer_zero_keep_both_exact_wires(self):
        receiver, port = self.spawn_receive("two-sessions", once="0")
        first = b"first malformed BP transfer"
        second = b"second distinct malformed BP transfer"

        sent1 = self.send(port, first, "first")
        sent2 = self.send(port, second, "second")
        self.assertEqual(sent1.returncode, 1, sent1.stdout + sent1.stderr)
        self.assertEqual(sent2.returncode, 1, sent2.stdout + sent2.stderr)
        self.assertIn("outbound xfer=0", sent1.stdout)
        self.assertIn("outbound xfer=0", sent2.stdout)
        self.assertNotIn("accepted outbound xfer=0", sent1.stdout)
        self.assertNotIn("accepted outbound xfer=0", sent2.stdout)

        wires = self.wait_for_wire_count(2)
        self.assertEqual({path.read_bytes() for path in wires}, {first, second})
        self.assertEqual(
            [path.name for path in wires],
            ["00000000000000000000.wire", "00000000000000000001.wire"],
        )
        output = receiver._fn_log_path.read_text(errors="replace")
        self.assertEqual(output.count("BP refused xfer=0"), 2, output)

    def test_uncertain_publication_exits_and_prevents_next_session_mutation(self):
        fault_env = dict(self.env)
        fault_env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = "namespace"
        receiver, port = self.spawn_receive("uncertain", once="0", env=fault_env)
        first = b"visible wire with uncertain namespace barrier"
        self.send(port, first, "uncertain-first")

        receiver.wait(timeout=20)
        output = receiver._fn_log_path.read_text(errors="replace")
        self.assertEqual(receiver.returncode, 3, output)
        self.assertIn("receive wire evidence publication uncertain", output)
        wires = self.wait_for_wire_count(1)
        self.assertEqual([path.read_bytes() for path in wires], [first])

        second = self.send(port, b"must not reach the fenced owner", "after-fence")
        self.assertNotEqual(second.returncode, 0, second.stdout + second.stderr)
        time.sleep(0.1)
        self.assertEqual(
            len(list((self.journal / "receive-evidence").glob("*.wire"))), 1
        )

        # Reopen barriers and ACL2 recovery consume the visible wire-only
        # identity.  The next process must not reuse or replace it.
        restarted, restarted_port = self.spawn_receive("after-restart", once="1")
        after_restart = b"new transfer after authoritative recovery"
        sent = self.send(restarted_port, after_restart, "after-restart-input")
        restarted.wait(timeout=20)
        self.assertEqual(sent.returncode, 0, sent.stdout + sent.stderr)
        self.assertIn(restarted.returncode, (0, 1))
        wires = self.wait_for_wire_count(2)
        self.assertEqual(
            [path.name for path in wires],
            ["00000000000000000000.wire", "00000000000000000001.wire"],
        )
        self.assertEqual({path.read_bytes() for path in wires}, {first, after_restart})


if __name__ == "__main__":
    unittest.main()
