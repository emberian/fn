#!/usr/bin/env python3
"""Executable boundary checks for the installed native operator image."""
import re
import socket
import unittest

from tests.native_harness import EXIT, ROOT, Client, Node, native_image, requires, run

IMAGE = native_image("FN_NATIVE_HOST")


class NativeOperatorPrincipalCompositionTests(unittest.TestCase):
    def test_operator_calls_existing_acl2_credential_plan_and_executor(self):
        model = (ROOT / "books" / "native-operator.lisp").read_text(encoding="ascii")
        # `principal' is the credentials surface: host/native/operator-live.lisp
        # carries its executor and registers it with operator.lisp's dispatch.
        host = (ROOT / "host" / "native" / "operator-live.lisp").read_text(encoding="ascii")
        # The ACL2 credential parser reads the words after `principal', so
        # the operator must hand it the tail of argv: `cdr' itself, or a
        # book function whose definition is the guard-total tail.
        principal = model[model.index("(defun fn-nop-parse-principal"):]
        principal = principal[:principal.index("\n(defun ")]
        call = re.search(r"\(fn-native-auth-admin-parse-argv \(([a-z0-9-]+) argv\)\)",
                         principal)
        self.assertIsNotNone(call, "principal plan does not parse a function of argv")
        tail = call.group(1)
        if tail != "cdr":
            definitions = [
                match for book in sorted((ROOT / "books").glob("*.lisp"))
                for match in re.findall(
                    rf"\(defun {re.escape(tail)} \((\S+)\)\s+"
                    r"\(declare \(xargs :guard t\)\)\s+"
                    r"\(if \(consp (\S+)\) \(cdr (\S+)\) nil\)\)",
                    book.read_text(encoding="utf-8"))]
            self.assertEqual(len(definitions), 1, f"{tail} is not defined once as argv's tail")
            self.assertEqual(len(set(definitions[0])), 1, f"{tail} is not the tail of its argument")
        self.assertIn("'fn-native-operator-host-result-principal-plan result", host)
        self.assertIn("(fnn-native-auth-admin-execute", host)
        self.assertIn("(fnn-operator-register-action :principal "
                      "#'fnn-operator-execute-principal)", host)


def invoke(config, *words):
    return run([IMAGE, "--fn", "operator", config, *words], timeout=30)


@requires(IMAGE)
class NativeOperatorCliTests(unittest.TestCase):
    def setUp(self):
        self.node = Node(self, IMAGE, listener=False, control=False)
        self.root = self.node.root

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
            self.assertEqual(result.returncode, EXIT.USAGE, result.stderr.decode())

    def test_unreadable_config_is_fault(self):
        config = self.root / "private.toml"
        config.write_text('[store]\npath = "/tmp/fn"\n', encoding="ascii")
        config.chmod(0)
        try:
            result = invoke(config, "status")
        finally:
            config.chmod(0o600)
        self.assertEqual(result.returncode, EXIT.FAULT, result.stderr.decode())

    @staticmethod
    def reserve_port(host, family):
        reservation = socket.socket(family, socket.SOCK_STREAM)
        try:
            reservation.bind((host, 0))
            return reservation.getsockname()[1]
        finally:
            reservation.close()

    def assert_operator_once_binds(self, host, family):
        name = host.replace(":", "v")
        node = Node(self, IMAGE, root=self.root / ("node-" + name), listener=False,
                    control=False)
        node.store("init", "fn.test", expect=EXIT.OK)
        node.port = self.reserve_port(host, family)
        node.config.write_text('[store]\npath = "{}"\n[listener]\nhost = "{}"\nport = {}\n'.format(
            node.store_path, host, node.port), encoding="ascii")
        node.start(verb=("run", "--once"))
        with Client(node.port, host=host, timeout=30, greeting=(b"200",)) as client:
            self.assertTrue(client.command(b"QUIT").startswith(b"205 "))
        node.exited(EXIT.OK)

    def test_operator_run_uses_acl2_projected_ipv4_loopbacks(self):
        for host in ("127.0.0.1", "localhost"):
            with self.subTest(host=host):
                self.assert_operator_once_binds(host, socket.AF_INET)

    def test_operator_run_uses_acl2_projected_ipv6_loopback(self):
        self.assert_operator_once_binds("::1", socket.AF_INET6)


if __name__ == "__main__":
    unittest.main()
