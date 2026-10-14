"""The funded operator slot at public saturation, and its exact control refusal.

Startup installs fn-adm-lease-startup-cfg before the live raise drives fn-adm-priced-cfg and its retained-bank claim
fn-adm-priced-cfg-keeps-the-installed-bank through the configured owner.
The configured run derives fn-adm-capacity and prices its control admission
through fn-adm-run-gate-held and fn-mm-gate-p. The serialized private open calls
fn-adm-operator-open; the test book supplies its record-growth witnesses.
The developer probe makes two logical private opens overlap within one owner
step. It calls the actual operator wrapper twice and forwards ACL2's second
refusal through the regular administrative control reply. It is a test of
simultaneous slot custody; it does not rely on scheduler timing.
"""
import socket
import unittest

from tests.campaign import native_cuts
from tests.native_harness import EXIT_OK, EXIT_REFUSED, ROOT, Node, native_image, requires
from tests.test_native_public_limits import first_line

PRODUCTION = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
SELECTOR = "FN_NATIVE_OPERATOR_SLOT_TEST"


class OperatorSlotSourceTests(unittest.TestCase):
    def test_admin_forwards_the_book_word_id_and_reason(self):
        text = (ROOT / "host/native/admin.lisp").read_text()
        stage = native_cuts.host_function(text, "fnn-rc-do-stage")
        self.assertIn("'fn-owner-operator-open", stage)
        for accessor in ("word", "id", "reason"):
            self.assertIn("'fn-adm-operator-open-" + accessor, stage)
        self.assertNotIn(":none", stage)
        self.assertLess(stage.index("(eq word :refused)"), stage.index("(funcall stage cid)"))
        self.assertIn("'fn-owner-close cid", stage)

    def test_probe_uses_the_real_second_open_and_the_shared_developer_gate(self):
        text = (ROOT / "host/native/admin.lisp").read_text()
        body = native_cuts.host_function(text, "fnn-operator-slot-test-stage")
        self.assertIn("'fn-owner-operator-open", body)
        self.assertIn("'fn-adm-operator-open-reason second", body)
        self.assertIn("'fn-ores-config-refused", body)
        self.assertNotIn(":operator-slot-held", body)
        io = (ROOT / "host/native/io.lisp").read_text(encoding="ascii")
        register = io[io.index("(defparameter +fnn-developer-selectors+"):
                      io.index("(defun fnn-developer-selector ")]
        self.assertIn('"' + SELECTOR + '"', register)
        self.assertNotIn('(pushnew "' + SELECTOR + '"', text)
        self.assertIn('(fnn-developer-selector "' + SELECTOR + '")', text)

    def test_owner_installs_all_three_coordinates_in_one_owner_step(self):
        host = (ROOT / "host/owner-host.lisp").read_text()
        body = native_cuts.host_function(host, "fn-owner-operator-open")
        self.assertLess(body.index("fn-owner-record-totals"), body.index("fn-owner-memory-run-cfg"))
        self.assertIn("(fn-exp-at 10 r)", body)
        book = (ROOT / "books/owner-connection-callbacks.lisp").read_text()
        install = native_cuts.host_function(book, "fn-owner-held-callback-operator-open-at")
        self.assertIn("update-nth 10", body)
        self.assertNotIn("fn-owner-memory-run", install)
        for part in ("fn-owner-memory-held-install", "fn-owner-install-ocfg"):
            self.assertIn(part, install)


class OperatorSlotCase:
    IMAGE = None

    def setUp(self):
        self.node = Node(self, self.IMAGE)
        self.held = []
        self.addCleanup(self.release)
        self.node.store("init", "fn.test", expect=EXIT_OK)
        self.node.write_config(extra='[auth]\nrequired = false\nprotected_only = false\n')
        self.node.operator("policy", "set", "exposure-connections", "40", expect=EXIT_OK)

    def release(self):
        for sock in self.held:
            sock.close()
        self.held.clear()

    def saturate(self):
        for _ in range(40):
            sock = socket.create_connection(("127.0.0.1", self.node.port), timeout=30)
            line = first_line(sock)
            self.assertTrue(line.startswith((b"200 ", b"201 ")), line)
            self.held.append(sock)


@requires(PRODUCTION)
class NativeOperatorSlotRaiseTests(OperatorSlotCase, unittest.TestCase):
    IMAGE = PRODUCTION

    def test_the_slot_allows_the_live_raise_at_public_saturation(self):
        self.node.start()
        self.saturate()
        result = self.node.operator("policy", "set", "exposure-connections", "45")
        self.assertEqual(result.returncode, EXIT_OK, result.stderr.decode())
        self.assertIsNone(self.node.process.poll())


@requires(DEVELOPER)
class NativeOperatorSlotRefusalTests(OperatorSlotCase, unittest.TestCase):
    IMAGE = DEVELOPER

    def test_second_overlapping_private_open_returns_the_exact_control_word(self):
        self.node.start(env={SELECTOR: "1"})
        self.saturate()
        result = self.node.operator("policy", "set", "exposure-connections", "45")
        self.assertEqual(result.returncode, EXIT_REFUSED, result.stderr.decode())
        words = (result.stdout + result.stderr).decode("ascii", "replace").split()
        self.assertIn("operator-slot-held", words)
        self.assertNotIn("none", words)
        self.assertIsNone(self.node.process.poll())
