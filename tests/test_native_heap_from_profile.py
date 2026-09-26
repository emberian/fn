"""The process heap from the store profile, native (lane heap-from-profile,
2026-09-26; PKT-016; PRF-198; HST-013; SCN-127).

The installed `bin/fn` (packaging/fn with libexec/fn beside it) no longer
runs every command under the image launcher's `--dynamic-space-size 32000`:
it first runs the same image as `heap -- ARGV`, where ACL2 decides the
figure from the command's store profile and this machine's memory
(books/heap-figure.lisp `fn-heap-decide'), and then execs the command with
that figure; a profile the machine cannot hold is refused there by name,
exit 1, and nothing else runs.

The case is the friend's machine: the module runs under a 2 GiB memory
limit (tools/hbox_native.sh --mem 2G: `systemd-run --user --scope -p
MemoryMax=2G`), which the host reads as the machine (the cgroup's
memory.max).  It needs FN_NATIVE_HOST (the production image) and skips, by
name, outside a limit of at most 2 GiB.

* A fresh node: `init` with no profile word on a machine under 4 GiB writes
  the small preset (`fn-heap-init-request'); `status' prints
  `heap=N MB profile=small machine=2048 MB'.  The node starts under that
  figure, takes 100 POSTs of 2 KiB, serves them (ARTICLE, OVER), publishes
  one automatic checkpoint (K = 128: at 64), stops, reopens from the
  checkpoint and serves them again.  Each run's VmHWM is printed.
* The refusal: the development profile (figure 2,671 MB on the 69046a76
  core) is refused by name at `init' and, for a store made without the
  launcher, at `run' and `status'.
"""
import os
import re
import shutil
import signal
import socket
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IMAGE = os.environ.get("FN_NATIVE_HOST")
EXIT_OK, EXIT_REFUSED = 0, 1
HEAP_LINE = re.compile(r"^heap=(\d+) MB profile=([a-z]+) machine=(\d+) MB$", re.M)
REFUSED = re.compile(
    r"refused machine-cannot-hold-profile heap=(\d+) MB machine=(\d+) MB")


def cgroup_limit():
    """The least memory.max from this process's cgroup up, or None."""
    try:
        line = next(l for l in Path("/proc/self/cgroup").read_text().splitlines()
                    if l.startswith("0::"))
    except (OSError, StopIteration):
        return None
    path, found = line[3:], []
    while path and path != "/":
        try:
            text = (Path("/sys/fs/cgroup" + path) / "memory.max").read_text().strip()
            if text.isdigit():
                found.append(int(text))
        except OSError:
            pass
        path = path.rsplit("/", 1)[0]
    return min(found) if found else None


LIMIT = cgroup_limit()
READY = bool(IMAGE and Path(IMAGE).is_file() and Path(IMAGE + ".core").is_file())
SMALL = bool(LIMIT and LIMIT <= 2 * 1024 ** 3)


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def text(result):
    return (result.stdout + result.stderr).decode("utf-8", "replace")


def vmhwm(pid):
    for line in Path("/proc/{}/status".format(pid)).read_text().splitlines():
        if line.startswith("VmHWM:"):
            return int(line.split()[1])
    return None


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to the production image")
@unittest.skipUnless(SMALL, "run under a memory limit of at most 2 GiB "
                            "(tools/hbox_native.sh --mem 2G)")
class HeapFromProfileTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-heap-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        prefix = self.tmp / "opt" / "fn"
        (prefix / "bin").mkdir(parents=True)
        (prefix / "libexec" / "fn").mkdir(parents=True)
        shutil.copy(ROOT / "packaging" / "fn", prefix / "bin" / "fn")
        os.symlink(IMAGE, prefix / "libexec" / "fn" / "fn-host")
        os.symlink(IMAGE + ".core", prefix / "libexec" / "fn" / "fn-host.core")
        self.fn = str(prefix / "bin" / "fn")
        self.owner = None

    def config(self, name):
        store, port = self.tmp / name, free_port()
        path = self.tmp / (name + ".toml")
        path.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\n'
                        'port = {}\n'.format(store, port), encoding="ascii")
        return path, port

    def env(self):
        env = dict(os.environ)
        for name in list(env):
            if name.startswith(("FN_NATIVE_", "FN_RUN_", "FN_TEST_", "SBCL_")):
                env.pop(name)
        return env

    def run_fn(self, *words, command=None):
        result = subprocess.run([*(command or [self.fn]), *map(str, words)],
                                env=self.env(), stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=600, check=False)
        print("NATIVE-HEAP", " ".join(map(str, words[1:3])), "->", result.returncode,
              text(result).strip().replace("\n", " | ")[-300:])
        return result

    def start(self, config, port, log):
        self.owner = subprocess.Popen([self.fn, "operator", str(config), "run"],
                                      env=self.env(), stdout=subprocess.DEVNULL,
                                      stderr=open(log, "wb"))
        self.addCleanup(self.reap)
        deadline = time.monotonic() + 600
        while time.monotonic() < deadline:
            self.assertIsNone(self.owner.poll(), Path(log).read_text(errors="replace"))
            try:
                with socket.create_connection(("127.0.0.1", port), timeout=5) as conn:
                    if conn.makefile("rb").readline().startswith(b"20"):
                        return
            except OSError:
                time.sleep(0.5)
        self.fail("the owner did not listen within 600 s")

    def reap(self):
        if self.owner and self.owner.poll() is None:
            self.owner.kill()
            self.owner.wait(timeout=60)

    def stop(self):
        hwm = vmhwm(self.owner.pid)
        self.owner.send_signal(signal.SIGTERM)
        self.assertEqual(self.owner.wait(timeout=120), EXIT_OK)
        return hwm

    def post(self, port, ids):
        body = ("x" * 72 + "\r\n") * 28  # 2,072 octets
        with socket.create_connection(("127.0.0.1", port), timeout=300) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"20"))
            for message_id in ids:
                stream.write(b"POST\r\n")
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"340"))
                stream.write(("From: author@example.invalid\r\nNewsgroups: local.test\r\n"
                              "Subject: heap\r\nMessage-ID: {}\r\n\r\n{}.\r\n"
                              .format(message_id, body)).encode("ascii"))
                stream.flush()
                self.assertEqual(stream.readline().rstrip(b"\r\n"),
                                 b"240 article received OK")
            stream.write(b"QUIT\r\n")
            stream.flush()

    def serve(self, port, ids):
        with socket.create_connection(("127.0.0.1", port), timeout=300) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"20"))
            for message_id in (ids[0], ids[-1]):
                stream.write("ARTICLE {}\r\n".format(message_id).encode("ascii"))
                stream.flush()
                self.assertTrue(stream.readline().startswith(b"220"))
                lines = []
                while True:
                    line = stream.readline()
                    if line == b".\r\n":
                        break
                    lines.append(line)
                self.assertIn(("Message-ID: " + message_id + "\r\n").encode("ascii"), lines)
            stream.write(b"GROUP local.test\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"211 100 "))
            stream.write(b"OVER 1-100\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"224"))
            rows = 0
            while stream.readline() != b".\r\n":
                rows += 1
            self.assertEqual(rows, 100)
            stream.write(b"QUIT\r\n")
            stream.flush()

    def wait_for(self, log, pattern, port, seconds=300):
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            found = re.search(pattern, Path(log).read_bytes())
            if found:
                return found
            try:  # the owner publishes between accepts
                with socket.create_connection(("127.0.0.1", port), timeout=5) as conn:
                    conn.makefile("rb").readline()
            except OSError:
                pass
            time.sleep(1)
        self.fail("no {!r} in the owner's log".format(pattern))

    def test_a_small_node_starts_serves_checkpoints_and_reopens_in_2g(self):
        config, port = self.config("small")
        made = self.run_fn("operator", config, "init", "local.test")
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        status = self.run_fn("operator", config, "status")
        self.assertEqual(status.returncode, EXIT_OK, text(status))
        out = status.stdout.decode()
        self.assertIn("max-history-octets=8388608", out)
        heap = HEAP_LINE.search(out)
        self.assertIsNotNone(heap, out)
        figure, word, machine = int(heap.group(1)), heap.group(2), int(heap.group(3))
        self.assertEqual(word, "small")
        self.assertEqual(machine, LIMIT // (1024 * 1024))
        self.assertLessEqual(figure, machine)
        print("NATIVE-HEAP figure={} MB machine={} MB".format(figure, machine))

        ids = ["<heap-{}@example.invalid>".format(n) for n in range(100)]
        log1 = self.tmp / "owner-1.log"
        self.start(config, port, log1)
        self.post(port, ids)
        self.serve(port, ids)
        auto = self.wait_for(log1, rb"CHECKPOINT auto sequence=(\d+) suffix=(\d+) "
                                   rb"octets=(\d+) ms=(\d+)", port)
        print("NATIVE-HEAP", auto.group(0).decode())
        hwm1 = self.stop()
        print("NATIVE-HEAP vmhwm run=1 kB={}".format(hwm1))

        reopened = self.run_fn("operator", config, "status")
        self.assertEqual(reopened.returncode, EXIT_OK, text(reopened))
        self.assertRegex(reopened.stdout.decode(), r"open=checkpoint:\d+")
        log2 = self.tmp / "owner-2.log"
        self.start(config, port, log2)
        self.serve(port, ids)
        hwm2 = self.stop()
        print("NATIVE-HEAP vmhwm run=2 kB={}".format(hwm2))
        self.assertLess(max(hwm1, hwm2) * 1024, LIMIT)

    def test_a_profile_the_machine_cannot_hold_is_refused_by_name_at_start(self):
        config, port = self.config("development")
        refused = self.run_fn("operator", config, "init", "--profile", "development",
                              "local.test")
        self.assertEqual(refused.returncode, EXIT_REFUSED, text(refused))
        self.assertRegex(text(refused), REFUSED)
        self.assertFalse((self.tmp / "development").exists())
        # The same store made without the launcher (the image's own figure).
        made = self.run_fn("operator", config, "init", "--profile", "development",
                           "local.test", command=[IMAGE, "--fn"])
        self.assertEqual(made.returncode, EXIT_OK, text(made))
        for verb in ("run", "status"):
            result = self.run_fn("operator", config, verb)
            self.assertEqual(result.returncode, EXIT_REFUSED, text(result))
            found = REFUSED.search(text(result))
            self.assertIsNotNone(found, text(result))
            self.assertGreater(int(found.group(1)), int(found.group(2)))
            self.assertEqual(int(found.group(2)), LIMIT // (1024 * 1024))
            self.assertEqual(result.stdout, b"")
        with self.assertRaises(OSError):
            socket.create_connection(("127.0.0.1", port), timeout=2).close()


if __name__ == "__main__":
    unittest.main()
