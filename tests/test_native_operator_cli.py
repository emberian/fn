#!/usr/bin/env python3
"""Executable boundary checks for the installed native operator image."""
import os
from pathlib import Path
import select
import socket
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def invoke(config, *words):
    return subprocess.run(
        [str(IMAGE), "--fn", "operator", str(config), *words],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=30, check=False,
    )


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeOperatorCliTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-operator-")
        self.root = Path(self.temporary.name)

    def tearDown(self):
        self.temporary.cleanup()

    def test_help_does_not_open_missing_config(self):
        result = invoke(self.root / "missing.toml", "help", "run")
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(result.stdout.decode(), "usage: fn operator CONFIG run [--once]\n")

    def test_missing_directory_and_oversize_config_are_usage(self):
        missing = invoke(self.root / "missing.toml", "status")
        directory = self.root / "directory"
        directory.mkdir()
        nonregular = invoke(directory, "status")
        large = self.root / "large.toml"
        large.write_bytes(b"x" * 16385)
        oversize = invoke(large, "status")
        for result in (missing, nonregular, oversize):
            self.assertEqual(result.returncode, 5, result.stderr.decode())

    def test_unreadable_config_is_fault(self):
        config = self.root / "private.toml"
        config.write_text('[store]\npath = "/tmp/fn"\n', encoding="ascii")
        config.chmod(0)
        try:
            result = invoke(config, "status")
        finally:
            config.chmod(0o600)
        self.assertEqual(result.returncode, 4, result.stderr.decode())

    def initialize_store(self, name):
        store = self.root / name
        result = subprocess.run(
            [str(IMAGE), "--fn", "store", str(store), "init", "fn.test"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=180, check=False)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return store

    @staticmethod
    def reserve_port(host, family):
        reservation = socket.socket(family, socket.SOCK_STREAM)
        try:
            reservation.bind((host, 0))
            return reservation.getsockname()[1]
        finally:
            reservation.close()

    def assert_operator_once_binds(self, host, family):
        store = self.initialize_store("store-" + host.replace(":", "v"))
        port = self.reserve_port(host, family)
        config = self.root / ("listener-" + host.replace(":", "v") + ".toml")
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "{}"\nport = {}\n'.format(
            store, host, port), encoding="ascii")
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(config), "run", "--once"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            ready = select.select([process.stdout], [], [], 180)[0]
            self.assertTrue(ready, "operator did not announce its port")
            line = process.stdout.readline()
            self.assertEqual(line, "LISTENING {}\n".format(port).encode(),
                             "unexpected listener announcement; process status={!r}".format(
                                 process.poll()))
            with socket.create_connection((host, port), timeout=30) as client:
                stream = client.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"QUIT\r\n")
                self.assertTrue(stream.readline().startswith(b"205 "))
            self.assertEqual(process.wait(timeout=60), 0,
                             process.stderr.read().decode("utf-8", "replace"))
        finally:
            if process.poll() is None:
                process.terminate()
                process.wait(timeout=10)
            process.stdout.close()
            process.stderr.close()

    def test_operator_run_uses_acl2_projected_ipv4_loopbacks(self):
        for host in ("127.0.0.1", "localhost"):
            with self.subTest(host=host):
                self.assert_operator_once_binds(host, socket.AF_INET)

    def test_operator_run_uses_acl2_projected_ipv6_loopback(self):
        self.assert_operator_once_binds("::1", socket.AF_INET6)


if __name__ == "__main__":
    unittest.main()
