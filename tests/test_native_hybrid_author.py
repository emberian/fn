#!/usr/bin/env python3
"""Opt-in saved-image vertical for the mandatory hybrid author profile."""
import base64
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import unittest
from tests.native_process import wait_for_announcement, stop_and_diagnostics

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


@unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                     "set FN_RUN_HYBRID_E2E=1 for the OpenSSL 3.5 saved-image gate")
@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host is required")
class NativeHybridAuthorTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-hybrid-author-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.store = self.root / "store"
        self.control = self.root / "control.sock"
        self.service_log = self.root / "service.log"
        self.port = free_port()
        self.config = self.root / "fn.toml"
        initialized = self.invoke("store", str(self.store), "init", "fn.test", timeout=180)
        self.assertEqual(initialized.returncode, 0, initialized.stderr.decode())
        self.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                self.store, self.port, self.control, self.service_log),
            encoding="ascii")
        self.principal = self.root / "principal.bin"
        self.ed_public = self.root / "ed-public.bin"
        self.ed_secret = self.root / "ed-secret.bin"
        self.principal.write_bytes(bytes([85]) * 32)
        self.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ml_private = self.root / "ml-private.pem"
        self.ml_public = self.root / "ml-public.pem"
        generated = subprocess.run(
            [OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out", str(self.ml_private)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, check=False)
        self.assertEqual(generated.returncode, 0,
                         "opted-in hybrid gate requires working ML-DSA-65: "
                         + generated.stderr.decode("utf-8", "replace"))
        subprocess.run([OPENSSL, "pkey", "-in", str(self.ml_private), "-pubout",
                        "-out", str(self.ml_public)], timeout=60, check=True)
        self.ml_private_b = self.root / "ml-private-b.pem"
        self.ml_public_b = self.root / "ml-public-b.pem"
        subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                        str(self.ml_private_b)], timeout=60, check=True)
        subprocess.run([OPENSSL, "pkey", "-in", str(self.ml_private_b), "-pubout",
                        "-out", str(self.ml_public_b)], timeout=60, check=True)

    def invoke(self, *args, timeout=60):
        return subprocess.run([str(IMAGE), "--fn", *args], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)

    def start_owner(self):
        proc = subprocess.Popen([str(IMAGE), "--fn", "operator", str(self.config), "run"],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        wait_for_announcement(proc, b"LISTENING ")
        return proc

    def stop_owner(self, proc):
        diagnostic = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostic)

    def test_enroll_author_refuse_tamper_and_restart_query(self):
        article = self.root / "article.eml"
        msgid = "<hybrid-native@example.invalid>"
        article.write_bytes(b"From: author@example.invalid\r\n"
                            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                            b"Newsgroups: fn.test\r\n"
                            b"Subject: hybrid\r\nMessage-ID: " + msgid.encode() +
                            b"\r\n\r\nexact bytes\r\n")
        owner = self.start_owner()
        try:
            enrolled = self.invoke("hybrid-enroll", str(self.control), "1",
                                str(self.principal), str(self.ed_public), str(self.ml_public))
            self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
            signed = self.invoke("hybrid-sign", str(self.principal), str(self.ed_public),
                              str(self.ed_secret), str(self.ml_public), str(self.ml_private),
                              str(article))
            self.assertEqual(signed.returncode, 0, signed.stderr.decode())
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = self.root / "ed.sig", self.root / "ml.sig"
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            bad = self.root / "bad-ml.sig"
            damaged = bytearray(ml_sig.read_bytes()); damaged[0] ^= 1; bad.write_bytes(damaged)
            common = [str(self.control), "1", str(article), str(ed_sig)]
            refused = self.invoke("hybrid-author", *(common + [str(bad), str(self.ml_public)]))
            self.assertEqual(refused.returncode, 1, refused.stderr.decode())

            accepted = self.invoke("hybrid-author", *(common + [str(ml_sig), str(self.ml_public)]))
            self.assertEqual(accepted.returncode, 0, accepted.stderr.decode())

            # The same Message-ID with a different, correctly signed source
            # passes admission but must be refused by the bound Store commit.
            # A distinct signed request then proves the control slot cleared.
            def signed_variant(source, stem):
                result = self.invoke(
                    "hybrid-sign", str(self.principal), str(self.ed_public),
                    str(self.ed_secret), str(self.ml_public), str(self.ml_private),
                    str(source))
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                values = dict(line.split() for line in result.stdout.decode().splitlines())
                ed_path = self.root / (stem + "-ed.sig")
                ml_path = self.root / (stem + "-ml.sig")
                ed_path.write_bytes(bytes.fromhex(values["ed25519"]))
                ml_path.write_bytes(bytes.fromhex(values["ml-dsa-65"]))
                return [str(self.control), "1", str(source), str(ed_path),
                        str(ml_path), str(self.ml_public)]

            conflict = self.root / "conflict.eml"
            conflict.write_bytes(article.read_bytes().replace(
                b"exact bytes", b"conflicting bytes"))
            conflicting = self.invoke("hybrid-author", *signed_variant(conflict, "conflict"))
            self.assertEqual(conflicting.returncode, 1, conflicting.stderr.decode())
            self.assertIn("refused post path=control message-id=" + msgid,
                          self.service_log.read_text(),
                          conflicting.stdout.decode() + "\n"
                          + conflicting.stderr.decode())
            fresh = self.root / "fresh.eml"
            fresh.write_bytes(article.read_bytes().replace(
                msgid.encode(), b"<hybrid-next-after-refusal@example.invalid>"))
            next_result = self.invoke("hybrid-author", *signed_variant(fresh, "fresh"))
            self.assertEqual(next_result.returncode, 0,
                             next_result.stderr.decode() or next_result.stdout.decode())
            enrolled_b = self.invoke("hybrid-enroll", str(self.control), "2",
                                  str(self.principal), str(self.ed_public), str(self.ml_public_b))
            self.assertEqual(enrolled_b.returncode, 0, enrolled_b.stderr.decode())
            retired_source = self.root / "retired.eml"
            retired_source.write_bytes(article.read_bytes().replace(
                msgid.encode(), b"<hybrid-retired@example.invalid>"))
            retired_generation = self.invoke(
                "hybrid-author", *signed_variant(retired_source, "retired"))
            self.assertEqual(retired_generation.returncode, 1,
                             retired_generation.stderr.decode())
            rotated_source = self.root / "rotated.eml"
            rotated_source.write_bytes(article.read_bytes().replace(
                msgid.encode(), b"<hybrid-rotated@example.invalid>"))
            def sign_rotated(source, stem):
                result = self.invoke("hybrid-sign", str(self.principal),
                                     str(self.ed_public), str(self.ed_secret),
                                     str(self.ml_public_b), str(self.ml_private_b),
                                     str(source))
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                values = dict(line.split() for line in result.stdout.decode().splitlines())
                ed_path = self.root / (stem + "-ed.sig")
                ml_path = self.root / (stem + "-ml.sig")
                ed_path.write_bytes(bytes.fromhex(values["ed25519"]))
                ml_path.write_bytes(bytes.fromhex(values["ml-dsa-65"]))
                return [str(self.control), "2", str(source), str(ed_path),
                        str(ml_path), str(self.ml_public_b)]
            rotated = self.invoke("hybrid-author", *sign_rotated(rotated_source, "rotated"))
            self.assertEqual(rotated.returncode, 0, rotated.stderr.decode())
            after_revoke = self.root / "after-revoke.eml"
            after_revoke.write_bytes(article.read_bytes().replace(
                msgid.encode(), b"<hybrid-after-revoke@example.invalid>"))
            delayed = sign_rotated(after_revoke, "after-revoke")
            revoked = self.invoke("hybrid-revoke", str(self.control), "3",
                                  str(self.principal))
            self.assertEqual(revoked.returncode, 0, revoked.stderr.decode())
            self.assertEqual(self.invoke("hybrid-author", *delayed).returncode, 1)
        finally:
            self.stop_owner(owner)
        history = self.invoke("hybrid-key-history", str(self.store))
        self.assertEqual(history.returncode, 0, history.stderr.decode())
        self.assertEqual(history.stdout.decode().splitlines(), [
            "generation=3 state=revoked principal=" + self.principal.read_bytes().hex(),
            "generation=2 state=retired principal=" + self.principal.read_bytes().hex(),
            "generation=1 state=retired principal=" + self.principal.read_bytes().hex(),
        ])
        owner = self.start_owner()
        try:
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(("ARTICLE {}\r\n".format(msgid)).encode())
                    self.assertTrue(stream.readline().startswith(b"220 "))
                    returned = bytearray()
                    while True:
                        line = stream.readline()
                        self.assertTrue(line, "ARTICLE response ended before dot terminator")
                        if line == b".\r\n":
                            break
                        returned.extend(line[1:] if line.startswith(b"..") else line)
                    self.assertIn(b"FN-Authorship: ", bytes(returned)[:200])
                    self.assertTrue(bytes(returned).endswith(article.read_bytes()))
                    received = self.root / "received.eml"
                    received.write_bytes(bytes(returned))
                    checked = self.invoke("hybrid-verify-carrier", str(received),
                                          str(self.ml_public))
                    self.assertEqual(checked.returncode, 0, checked.stderr.decode())
                    stream.write(("HDR :fn-verified {}\r\n".format(msgid)).encode())
                    self.assertEqual(stream.readline(), b"225 headers follow\r\n")
                    # Generation 2 has replaced the enrolled key set, but
                    # the recovered schema-1 verdict keeps its original pin.
                    self.assertEqual(stream.readline(),
                                     b"0 verified " + b"55" * 32 +
                                     b" keyring 1\r\n")
                    self.assertEqual(stream.readline(), b".\r\n")
        finally:
            self.stop_owner(owner)

    def test_portable_carrier_verifies_exact_source_and_keyset(self):
        source = self.root / "authored.eml"
        source.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: portable hybrid\r\n"
            b"Message-ID: <portable-hybrid@example.invalid>\r\n"
            b"X-Unknown: authored and signed\r\n\r\nexact source bytes\r\n")
        carried = self.root / "carried.eml"
        signed = self.invoke(
            "hybrid-sign-carrier", str(self.principal), str(self.ed_public),
            str(self.ed_secret), str(self.ml_public), str(self.ml_private),
            str(source), str(carried))
        self.assertEqual(signed.returncode, 0, signed.stderr.decode())
        received = carried.read_bytes()
        self.assertTrue(received.endswith(source.read_bytes()))
        checked = self.invoke("hybrid-verify-carrier", str(carried),
                              str(self.ml_public))
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())
        self.assertIn(self.principal.read_bytes().hex().encode(), checked.stdout)

        relayed = self.root / "relayed.eml"
        relayed.write_bytes(b"Path: relay.example!fn\r\n"
                            b"Xref: relay.example fn.test:7\r\n" + received)
        checked = self.invoke("hybrid-verify-carrier", str(relayed),
                              str(self.ml_public))
        self.assertEqual(checked.returncode, 0, checked.stderr.decode())

        altered_source = self.root / "altered-source.eml"
        altered_source.write_bytes(received.replace(b"exact source bytes",
                                                    b"Exact source bytes", 1))
        refused = self.invoke("hybrid-verify-carrier", str(altered_source),
                              str(self.ml_public))
        self.assertEqual(refused.returncode, 1, refused.stderr.decode())

        # Change one byte of the Ed25519 public key inside the canonical
        # carrier while preserving the field's original folding.  This is a
        # valid carrier grammar with the wrong key set, not a parser negative.
        prefix, authored = received.split(b"From: ", 1)
        header_name, folded = prefix.split(b": ", 1)
        self.assertEqual(header_name, b"FN-Authorship")
        encoded = b"".join(folded.split())
        binary = base64.b64decode(encoded, validate=True)
        ed_public = self.ed_public.read_bytes()
        self.assertEqual(binary.count(ed_public), 1)
        wrong_key = bytes([ed_public[0] ^ 1]) + ed_public[1:]
        mutated = base64.b64encode(binary.replace(ed_public, wrong_key, 1))
        self.assertEqual(len(mutated), len(encoded))
        field = bytearray(prefix)
        start = len(header_name) + 2
        for octet in mutated:
            while field[start] in b"\r\n\t ":
                start += 1
            field[start] = octet
            start += 1
        altered_key = self.root / "altered-key.eml"
        altered_key.write_bytes(bytes(field) + b"From: " + authored)
        refused = self.invoke("hybrid-verify-carrier", str(altered_key),
                              str(self.ml_public))
        self.assertEqual(refused.returncode, 1, refused.stderr.decode())

        # The source alone is under the article cap, but adding the required
        # carrier would exceed it.  The ACL2 total bound refuses emission.
        large_source = self.root / "large-source.eml"
        large_source.write_bytes(source.read_bytes() + b"x" * 26000)
        refused_output = self.root / "too-large-carried.eml"
        refused = self.invoke(
            "hybrid-sign-carrier", str(self.principal), str(self.ed_public),
            str(self.ed_secret), str(self.ml_public), str(self.ml_private),
            str(large_source), str(refused_output))
        self.assertEqual(refused.returncode, 1, refused.stderr.decode())
        self.assertFalse(refused_output.exists())

    def test_local_revocation_targets_one_principal(self):
        other_principal = self.root / "other-principal.bin"
        other_principal.write_bytes(bytes([86]) * 32)

        def source(stem):
            path = self.root / (stem + ".eml")
            path.write_bytes(
                b"From: author@example.invalid\r\n"
                b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                b"Newsgroups: fn.test\r\nSubject: local lifecycle\r\n"
                b"Message-ID: <" + stem.encode() + b"@example.invalid>\r\n\r\nbody\r\n")
            return path

        def author(generation, principal, ml_public, ml_private, stem):
            article = source(stem)
            signed = self.invoke("hybrid-sign", str(principal), str(self.ed_public),
                                 str(self.ed_secret), str(ml_public), str(ml_private),
                                 str(article))
            self.assertEqual(signed.returncode, 0, signed.stderr.decode())
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_path = self.root / (stem + ".ed.sig")
            ml_path = self.root / (stem + ".ml.sig")
            ed_path.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_path.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            return self.invoke("hybrid-author", str(self.control), str(generation),
                               str(article), str(ed_path), str(ml_path), str(ml_public))

        owner = self.start_owner()
        try:
            for generation, principal, ml_public in (
                    (1, self.principal, self.ml_public),
                    (2, other_principal, self.ml_public_b)):
                enrolled = self.invoke("hybrid-enroll", str(self.control),
                                       str(generation), str(principal),
                                       str(self.ed_public), str(ml_public))
                self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
            # B's later global generation leaves A's local capability intact.
            self.assertEqual(author(1, self.principal, self.ml_public,
                                    self.ml_private, "a-after-b").returncode, 0)
            self.assertEqual(author(2, other_principal, self.ml_public_b,
                                    self.ml_private_b, "b-before-revoke").returncode, 0)
            revoked = self.invoke("hybrid-revoke", str(self.control), "3",
                                  str(other_principal))
            self.assertEqual(revoked.returncode, 0, revoked.stderr.decode())
            self.assertEqual(author(1, self.principal, self.ml_public,
                                    self.ml_private, "a-after-b-revoke").returncode, 0)
            self.assertEqual(author(2, other_principal, self.ml_public_b,
                                    self.ml_private_b, "b-after-revoke").returncode, 1)
        finally:
            self.stop_owner(owner)
        history = self.invoke("hybrid-key-history", str(self.store))
        self.assertEqual(history.returncode, 0, history.stderr.decode())
        self.assertEqual(history.stdout.decode().splitlines(), [
            "generation=3 state=revoked principal=" + other_principal.read_bytes().hex(),
            "generation=2 state=retired principal=" + other_principal.read_bytes().hex(),
            "generation=1 state=active principal=" + self.principal.read_bytes().hex(),
        ])

    def test_authored_carrier_survives_native_peering_and_receiver_restart(self):
        """Real owner/feed/receiver path; portable verification is independent.

        This does not claim a receiver-local enrolled verdict or protected
        transport. Those have separate gates. Both peers are loopback fixtures.
        """
        other_store = self.root / "receiver"
        other_control = self.root / "receiver.sock"
        other_port = free_port()
        self.assertNotEqual(self.port, other_port)
        other_config = self.root / "receiver.toml"
        other_config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(
                other_store, other_port, other_control), encoding="ascii")

        def ok(*args):
            result = self.invoke(*map(str, args), timeout=180)
            self.assertEqual(result.returncode, 0,
                             result.stderr.decode("utf-8", "replace"))
            return result

        ok("store", other_store, "init", "fn.test")
        for config, identity, peer, peer_port in (
                (self.config, "author.example.invalid", "relay.example.invalid", other_port),
                (other_config, "relay.example.invalid", "author.example.invalid", self.port)):
            ok("operator", config, "policy", "set", "path-identity", identity)
            ok("operator", config, "peer", "add", "other", peer,
               "127.0.0.1", peer_port, "fn.*", "fn.*", "127.0.0.1", "true")

        msgid = "<hybrid-native-relay@example.invalid>"
        source = self.root / "peer-source.eml"
        source.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\nSubject: signed relay\r\n"
            b"Message-ID: " + msgid.encode() + b"\r\n"
            b"X-Unknown: preserve these authored bytes\r\n\r\n"
            b".dot-prefixed body\r\nexact relay source\r\n")
        signed = ok("hybrid-sign", self.principal, self.ed_public,
                    self.ed_secret, self.ml_public, self.ml_private, source)
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_sig, ml_sig = self.root / "peer-ed.sig", self.root / "peer-ml.sig"
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))

        def read_article(port):
            with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(b"ARTICLE " + msgid.encode() + b"\r\n")
                    status = stream.readline()
                    if status.startswith(b"430 "):
                        return None
                    self.assertTrue(status.startswith(b"220 "), status)
                    article = bytearray()
                    while True:
                        line = stream.readline(32769)
                        self.assertTrue(line, "unterminated ARTICLE")
                        if line == b".\r\n":
                            return bytes(article)
                        article.extend(line[1:] if line.startswith(b"..") else line)
                        self.assertLessEqual(len(article), 32768)

        owners = []

        def start(config):
            proc = subprocess.Popen(
                [str(IMAGE), "--fn", "operator", str(config), "run"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            owners.append(proc)
            wait_for_announcement(proc, b"LISTENING ")
            return proc

        try:
            start(self.config)
            receiver = start(other_config)
            ok("hybrid-enroll", self.control, "1", self.principal,
               self.ed_public, self.ml_public)
            ok("hybrid-author", self.control, "1", source, ed_sig, ml_sig, self.ml_public)
            original = read_article(self.port)
            self.assertIsNotNone(original)
            deadline = time.monotonic() + 45
            received = None
            while time.monotonic() < deadline:
                received = read_article(other_port)
                if received is not None:
                    break
                time.sleep(0.1)
            self.assertIsNotNone(received, "native feed did not deliver authored article")
            self.assertTrue(received.endswith(source.read_bytes()))
            original_paths = [line for line in original.split(b"\r\n")
                              if line.startswith(b"Path: ")]
            received_paths = [line for line in received.split(b"\r\n")
                              if line.startswith(b"Path: ")]
            self.assertEqual(len(original_paths), 1,
                             "native authored article lacks one injected Path")
            self.assertEqual(len(received_paths), 1,
                             "native relayed article lacks one Path")
            original_path, received_path = original_paths[0], received_paths[0]
            self.assertEqual(received_path,
                             b"Path: relay.example.invalid!!" + original_path[6:])
            self.assertEqual(received.replace(received_path + b"\r\n", b"", 1),
                             original.replace(original_path + b"\r\n", b"", 1))
            carried = self.root / "peer-received.eml"
            carried.write_bytes(received)
            ok("hybrid-verify-carrier", carried, self.ml_public)
            owners.remove(receiver)
            self.stop_owner(receiver)
            start(other_config)
            self.assertEqual(read_article(other_port), received)
            # Verify the recovered bytes, rather than reusing a sender verdict.
            carried.write_bytes(read_article(other_port))
            ok("hybrid-verify-carrier", carried, self.ml_public)
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)


if __name__ == "__main__":
    unittest.main()
