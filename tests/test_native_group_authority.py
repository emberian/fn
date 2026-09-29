"""SUB-007 explicit config and productive enrolled statement-authority fixtures.
The unsigned fixture checks pinned configuration. The productive fixture uses
real native ML keys, enrollment and restart/rotation, and requires a matching
new runner image plus FN_RUN_HYBRID_E2E=1. No old-image verdict is transferred.
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

# Real native ML suite and real enrollment/control publication, never an
# injected Store or toy signature state. Run against a matching new image.
import os
import subprocess
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
@unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                     "set FN_RUN_HYBRID_E2E=1 for real ML-DSA authority bridge")
@requires(IMAGE)
class NativeProductiveGroupAuthorityTests(unittest.TestCase):
    def test_enrolled_statement_policy_rotation_and_replay(self):
        node = Node(self, IMAGE, root=scratch(self, "fn-native-authority-productive-"), name="productive")
        node.log = node.root / "service.log"
        node.write_config(extra='[log]\npath = "{}"\n'.format(node.log))
        node.store("init", "fn.test", expect=EXIT.OK)
        node.operator("peer", "add", "upstream", "upstream.invalid", "127.0.0.1",
                      str(free_port()), "fn.*", "-", "127.0.0.1", "true", expect=EXIT.OK)
        node.operator("group", "authority", "fn.test", P, expect=EXIT.OK)
        principal, ed = node.root / "principal.bin", node.root / "ed-public.bin"
        principal.write_bytes(bytes.fromhex(P))
        ed.write_bytes(bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        keys = []
        for n in range(2):
            private, public = node.root / (str(n) + "-private.pem"), node.root / (str(n) + "-public.pem")
            made = subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(private)],
                                  capture_output=True, timeout=60, check=False)
            self.assertEqual(made.returncode, 0, made.stderr.decode("utf-8", "replace"))
            subprocess.run([OPENSSL, "pkey", "-in", str(private), "-pubout", "-out", str(public)],
                           capture_output=True, timeout=60, check=True)
            keys.append((private, public))
        def invoke(*words):
            result = node.invoke(*map(str, words), timeout=90)
            self.assertEqual(result.returncode, EXIT.OK, result.stderr.decode("utf-8", "replace"))
            return result
        def signed(stem, seq, key=0, kind="article", inc=0, body=b"body\r\n"):
            mid = "<" + stem + "@authority.invalid>"
            source, output = node.root / (stem + ".source"), node.root / (stem + ".signed")
            source.write_bytes(("Path: upstream!not-for-mail\r\nFrom: a@example.invalid\r\n"
                                "Date: Wed, 30 Sep 2026 12:00:00 +0000\r\nNewsgroups: fn.test\r\n"
                                "Subject: authority\r\nMessage-ID: " + mid + "\r\n\r\n").encode() + body)
            private, public = keys[key]
            invoke("statement-sign", principal, inc, seq, kind, "fn.test", private, public, source, output)
            return mid, output.read_bytes()
        def policy(stem, seq, key=0, body=b"terms"):
            mid, wire = signed(stem, seq, key, "policy", body=body)
            with Client(node.port, timeout=60, greeting=(b"200",)) as client:
                offer, reply = client.post(wire)
                self.assertTrue(offer.startswith(b"340 "), offer)
                self.assertTrue(reply.startswith(b"240 "), reply)
            return mid
        def transit(stem, seq, expected, key=0, inc=0):
            mid, wire = signed(stem, seq, key, inc=inc)
            with Client(node.port, timeout=60, greeting=(b"200",)) as client:
                offer, reply = client.post(wire, verb="IHAVE " + mid)
                self.assertTrue(offer.startswith(b"335 "), offer)
                self.assertTrue(reply.startswith(b"235 "), reply)
            deadline = time.monotonic() + 15
            while True:
                text = node.log.read_text() if node.log.exists() else ""
                rows = [s for s in text.splitlines() if " transit " in s and "message-id=" + mid + " " in s]
                if rows or time.monotonic() >= deadline:
                    break
                time.sleep(0.05)
            self.assertEqual(len(rows), 1, text)
            self.assertIn("authority=" + expected, rows[0])
            return mid
        try:
            node.start()
            invoke("hybrid-enroll", node.control, 1, principal, ed, keys[0][1])
            policy("policy-original", 0)
            transit("admitted-live", 1, "admitted")
            node.stop()
            node.start()
            transit("admitted-replay", 2, "admitted")
            invoke("hybrid-enroll", node.control, 2, principal, ed, keys[1][1])
            transit("old-policy-refused-after-rotation", 3, "no-policy", key=1)
            policy("policy-new-key", 4, key=1)
            transit("admitted-new-key", 5, "admitted", key=1)
            node.stop()
            node.start()
            transit("admitted-new-key-replay", 6, "admitted", key=1)
            transit("poster-fork", 6, "equivocation", key=1)
            # Forked incarnation is retained; a different incarnation reaches
            # the policy gate before introducing an authority policy fork.
            transit("new-incarnation", 0, "admitted", key=1, inc=1)
            policy("policy-fork", 4, key=1, body=b"different terms")
            transit("authority-fork", 1, "authority-equivocation", key=1, inc=1)
            node.stop()
            node.start()
            transit("authority-fork-replay", 2, "authority-equivocation", key=1, inc=1)
            print("NATIVE-GROUP-AUTHORITY-PRODUCTIVE-WITNESS live replay rotation old-policy-refusal new-key replay poster-fork authority-fork retained", flush=True)
        finally:
            node.stop()
