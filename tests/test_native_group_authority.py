"""SUB-007: the real operator config path reaches a governed transit gate.
Unsigned input proves the explicit binding is observed as no-statement, not
ungoverned. Productive verified authority and equivocation join this fixture
once the snapshot/statement bridge is implemented; this test alone makes no
admitted-authority claim. Run only the runner's new immutable image.
"""
import time
import unittest
from tests.native_harness import EXIT, Client, Node, free_port, native_image, requires, scratch
IMAGE = native_image("FN_NATIVE_HOST", "build/fn-host-developer")
P = "55" * 32
Q = "66" * 32
@requires(IMAGE)
class NativeGroupAuthorityTests(unittest.TestCase):
    def test_durable_binding_replacement_obeys_connection_pin(self):
        root = scratch(self, "fn-native-group-authority-")
        node = Node(self, IMAGE, root=root, name="authority")
        node.log = node.root / "service.log"
        node.write_config(extra='[log]\npath = "{}"\n'.format(node.log))
        node.store("init", "fn.test", expect=EXIT.OK)
        node.operator("peer", "add", "upstream", "upstream.invalid", "127.0.0.1",
                      str(free_port()), "fn.*", "-", "127.0.0.1", "true", expect=EXIT.OK)
        node.operator("group", "authority", "fn.test", P, expect=EXIT.OK)
        def transit(client, stem):
            mid = "<" + stem + "@authority.invalid>"
            wire = ("Path: upstream!not-for-mail\r\nFrom: a@example.invalid\r\n"
                    "Newsgroups: fn.test\r\nSubject: governed\r\nMessage-ID: "
                    + mid + "\r\n\r\nbody\r\n").encode()
            offer, reply = client.post(wire, verb="IHAVE " + mid)
            self.assertTrue(offer.startswith(b"335 "), offer)
            self.assertTrue(reply.startswith(b"235 "), reply)
            return mid
        def verdict(mid, expected):
            deadline = time.monotonic() + 15
            while True:
                text = node.log.read_text() if node.log.exists() else ""
                lines = [s for s in text.splitlines() if " transit " in s and "message-id=" + mid + " " in s]
                if lines or time.monotonic() >= deadline:
                    break
                time.sleep(0.05)
            self.assertEqual(len(lines), 1, text)
            self.assertIn("authority=" + expected, lines[0])
        try:
            node.start()
            with Client(node.port, timeout=30, greeting=(b"200",)) as old:
                verdict(transit(old, "governed-before"), "no-statement")
                node.operator("group", "authority", "fn.test", "ungoverned", expect=EXIT.OK)
                verdict(transit(old, "old-pin"), "no-statement")
                with Client(node.port, timeout=30, greeting=(b"200",)) as new:
                    verdict(transit(new, "new-pin"), "ungoverned")
                node.operator("group", "authority", "fn.test", Q, expect=EXIT.OK)
            node.stop()
            node.start()
            with Client(node.port, timeout=30, greeting=(b"200",)) as restarted:
                verdict(transit(restarted, "replacement-replayed"), "no-statement")
            print("NATIVE-GROUP-AUTHORITY-CONFIG-WITNESS governed old-pin new-pin replacement-replayed", flush=True)
        finally:
            node.stop()
