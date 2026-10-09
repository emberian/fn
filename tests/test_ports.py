"""NATIVE-HARNESS-PORT-RACE: the ports the harness gives its nodes.

The drain image gate (hbox:/tank/fn/scratch/drain/native-drain-c0e35e156) lost
25 tests in 11 modules to EADDRINUSE at the node's bind: `free_port` probed a
port with bind(0), closed the probe and wrote the port into fn.toml, and any
socket on the box (a client connect, another probe, the load sweep's nodes)
could be given that port by the kernel before the node bound it.
"""
import os
import random
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def kernel_ephemeral_low():
    """The first port the kernel assigns on its own (bind to 0, connect)."""
    try:
        return int(Path("/proc/sys/net/ipv4/ip_local_port_range").read_text().split()[0])
    except (OSError, ValueError, IndexError):
        out = subprocess.run(["sysctl", "-n", "net.inet.ip.portrange.first"],
                             capture_output=True, text=True)
        return int(out.stdout.strip())


class HarnessPortTests(unittest.TestCase):
    def test_a_handed_out_port_is_outside_the_kernels_ephemeral_range(self):
        from tests import native_harness
        low = kernel_ephemeral_low()
        port = native_harness.free_port()
        self.assertTrue(port < low, "the harness handed out a port the kernel can give "
                                    "to another socket before the node binds it")


HOLDER = r'''
import sys, time
sys.path.insert(0, sys.argv[1])
from tools import ports
got = [ports.reserve() for _ in range(int(sys.argv[2]))]
print(" ".join(map(str, got)), flush=True)
sys.stdin.read()
'''


class ReservationTests(unittest.TestCase):
    def setUp(self):
        self.dir = Path(tempfile.mkdtemp(prefix="fn-ports-test-"))
        self.dir.chmod(0o700)
        self.env = dict(os.environ, FN_PORT_LOCK_DIR=str(self.dir))
        self.old = os.environ.get("FN_PORT_LOCK_DIR")
        os.environ["FN_PORT_LOCK_DIR"] = str(self.dir)
        self.addCleanup(self.restore)

    def restore(self):
        if self.old is None:
            os.environ.pop("FN_PORT_LOCK_DIR", None)
        else:
            os.environ["FN_PORT_LOCK_DIR"] = self.old

    def holder(self, count):
        p = subprocess.Popen([sys.executable, "-c", HOLDER, str(ROOT), str(count)], env=self.env,
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.addCleanup(lambda: (p.stdin.close(), p.wait(timeout=30)))
        return p, {int(x) for x in p.stdout.readline().split()}

    def test_two_processes_never_hold_the_same_port(self):
        # a 300-port pool, 120 ports each: probe-and-release would collide
        env_low, env_high = 40000, 40300
        code = HOLDER.replace("ports.reserve()", f"ports.reserve(low={env_low}, high={env_high})")
        procs = []
        for _ in range(2):
            p = subprocess.Popen([sys.executable, "-c", code, str(ROOT), "120"], env=self.env,
                                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
            self.addCleanup(lambda p=p: (p.stdin.close(), p.wait(timeout=30)))
            procs.append(p)
        a, b = ({int(x) for x in p.stdout.readline().split()} for p in procs)
        self.assertEqual((len(a), len(b)), (120, 120))
        self.assertEqual(a & b, set())

    def test_a_dead_holders_ports_are_free_again(self):
        p, held = self.holder(5)
        from tools import ports
        p.stdin.close()
        p.wait(timeout=30)
        port = next(iter(held))
        fixed = random.Random(0)
        fixed.randrange = lambda lo, hi: port
        self.assertEqual(ports.reserve(rng=fixed), port)

    def test_a_port_something_is_bound_to_is_skipped(self):
        from tools import ports
        with socket.socket() as busy:
            busy.bind(("127.0.0.1", 0))
            taken = busy.getsockname()[1]
            order = iter([taken, 21234])
            rng = random.Random(0)
            rng.randrange = lambda lo, hi: next(order)
            self.assertEqual(ports.reserve(low=1024, high=65535, rng=rng), 21234)

    def test_the_pool_lies_below_the_ephemeral_range(self):
        from tools import ports
        low = kernel_ephemeral_low()
        self.assertEqual(ports.ephemeral_low(), low)
        for _ in range(50):
            self.assertTrue(ports.POOL_LOW <= ports.reserve() < low)

    def test_a_lock_directory_others_can_write_is_refused(self):
        from tools import ports
        self.dir.chmod(0o777)
        self.addCleanup(self.dir.chmod, 0o700)
        with self.assertRaises(RuntimeError):
            ports.reserve()

    def test_a_pool_too_small_is_refused(self):
        from tools import ports
        with self.assertRaises(RuntimeError):
            ports.reserve(low=30000, high=30100)


if __name__ == "__main__":
    unittest.main()
