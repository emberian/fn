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
import re
import socket
import unittest

from tests.campaign import native_cuts
from tests.native_harness import EXIT_OK, EXIT_REFUSED, ROOT, Node, native_image, requires
from tests.test_native_public_limits import first_line

PRODUCTION = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")
SELECTOR = "FN_NATIVE_OPERATOR_SLOT_TEST"
CONFIG_EDGE_SELECTOR = "FN_NATIVE_CONFIG_MEMORY_EDGE_TEST"


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

    def test_config_edge_probe_prices_the_real_request_before_staging(self):
        host = (ROOT / "host/owner-host.lisp").read_text()
        candidate = native_cuts.host_function(host, "fn-owner-memory-candidate-refusal")
        self.assertIn("fn-adm-config-change-admitp", candidate)
        self.assertIn(":config-exceeds-memory", candidate)
        self.assertIn("(projected-cap (if raises-c c2 cap))", candidate)
        self.assertIn("(fn-exp-at 10 r)", candidate)
        stage = native_cuts.host_function(host, "fn-owner-reconfigure-deltas")
        self.assertIn("(len (fn-cfg-encode (fn-ocfg-reconfig-record oc deltas)))", stage)
        self.assertIn("(okp (fn-ocfg-reconfig-okp oc id deltas))", stage)
        self.assertIn("(memory (and okp", stage)
        admitted = native_cuts.host_function(host, "fn-owner-reconfigure-deltas-admitted")
        self.assertIn("(reason (if (fn-ocfg-reconfig-okp oc id deltas) nil", admitted)
        self.assertIn("(if (and staged (not reason))", admitted)
        self.assertIn("fn-owner-memory-config-grow", admitted)
        self.assertLess(stage.index("fn-owner-memory-candidate-refusal"),
                        stage.index("fn-owner-reconfigure-deltas-admitted"))
        native = (ROOT / "host/native/admin.lisp").read_text()
        probe = native_cuts.host_function(native, "fnn-config-memory-edge-stage")
        self.assertIn("'fn-owner-memory-config-edge-observation", probe)
        observation = native_cuts.host_function(host, "fn-owner-memory-config-edge-observation")
        self.assertIn("fn-adm-config-edge-resident", observation)
        self.assertIn("'fn-owner-memory-gate-install", probe)
        self.assertIn("'fn-owner-memory-reclaim-complete", probe)
        self.assertNotIn(":config-exceeds-memory", probe)
        self.assertIn('(fnn-developer-selector "' + CONFIG_EDGE_SELECTOR + '")', native)
        io = (ROOT / "host/native/io.lisp").read_text()
        register = io[io.index("(defparameter +fnn-developer-selectors+"):
                      io.index("(defun fnn-developer-selector ")]
        self.assertIn('"' + CONFIG_EDGE_SELECTOR + '"', register)

    def test_close_and_fault_install_the_one_paired_close_result(self):
        host = (ROOT / "host/owner-host.lisp").read_text()
        for name in ("fn-owner-close", "fn-owner-fault"):
            body = native_cuts.host_function(host, name)
            self.assertEqual(body.count("(fn-adm-operator-close "), 1)
            self.assertIn("'fn-owner-memory-held-bank (fn-exp-at 0 closed)", body)
            self.assertIn("(update-nth 10 (fn-exp-at 1 closed)", body)
            self.assertNotIn("fn-owner-memory-held-close", body)

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

    def public_capacity(self):
        """The run's own public capacity C' from its capacity line; the test pins no figure (the
        over-window term keeps C' below the configured 40 until OVER landing 2, and below it
        after any profile change)."""
        found = re.search(rb"memory capacity=(\d+) of (\d+) bound-by=", self.node.process.stderr.since(0))
        self.assertIsNotNone(found, self.node.process.stderr.since(0)[-2000:])
        capacity = int(found.group(1))
        self.assertGreater(capacity, 0)
        self.assertLessEqual(capacity, 40)
        return capacity

    def saturate(self):
        for _ in range(self.public_capacity()):
            sock = socket.create_connection(("127.0.0.1", self.node.port), timeout=30)
            line = first_line(sock)
            self.assertTrue(line.startswith((b"200 ", b"201 ")), line)
            self.held.append(sock)


@requires(PRODUCTION)
class NativeOperatorSlotRaiseTests(OperatorSlotCase, unittest.TestCase):
    IMAGE = PRODUCTION

    def test_the_slot_allows_the_live_raise_at_public_saturation(self):
        # Measure this node's own capacity K, then configure K-2 so that a raise to K-1
        # still fits the memory (which holds K public readers plus the operator slot).
        # At public saturation the raise must go through the private slot and be admitted;
        # before STEP 5 it was refused until a reader left.
        self.node.start()
        capacity = self.public_capacity()
        self.assertGreaterEqual(capacity, 3)
        self.node.stop()
        self.node.operator("policy", "set", "exposure-connections", str(capacity - 2), expect=EXIT_OK)
        self.node.start()
        self.assertEqual(self.public_capacity(), capacity - 2)
        self.saturate()
        result = self.node.operator("policy", "set", "exposure-connections", str(capacity - 1))
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


@requires(DEVELOPER)
class NativeConfigHistoryEdgeTests(OperatorSlotCase, unittest.TestCase):
    IMAGE = DEVELOPER

    def test_unchanged_policy_at_the_memory_edge_returns_the_exact_refusal_text(self):
        # The real request preserves C/H. ACL2 chooses the pre-change edge;
        # fn-adm-config-change-admitp prices its positive encoded history charge.
        self.node.start(env={CONFIG_EDGE_SELECTOR: "1"})
        result = self.node.operator("policy", "set", "posting-policy", "open")
        self.assertEqual(result.returncode, EXIT_REFUSED, result.stderr.decode())
        words = (result.stdout + result.stderr).decode("ascii", "replace").split()
        self.assertIn("config-exceeds-memory", words)
        self.assertNotIn("none", words)
        self.assertIsNone(self.node.process.poll())
