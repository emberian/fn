#!/usr/bin/env python3
"""Opt-in saved-image vertical for the mandatory hybrid author profile."""
import base64
import os
from pathlib import Path
import socket
import subprocess
import sys
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

    def test_signed_post_over_nntp_gets_the_transit_classification(self):
        """A served POST of an FN-Authorship carrier, without the control socket.

        The served POST arm calls the attempt transit uses
        (host/native/owner.lisp fnn-owner-attempt-served): ACL2's
        fn-pa-current-plan over the POST's octets and this Store's
        enrollment.  Present and valid under the enrollment is a kind-4
        acceptance whose verdict HDR :fn-verified reports; present and
        refused is 441 with the plan's reason (fn-pa-served-word, one line
        per reason); absent is the unsigned arm, 240 with no verdict.
        """
        other_principal = self.root / "unenrolled-principal.bin"
        other_principal.write_bytes(bytes([86]) * 32)

        def carrier(stem, principal=None, tamper=False):
            source = self.root / (stem + "-source.eml")
            source.write_bytes(
                b"From: agent@example.invalid\r\n"
                b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
                b"Newsgroups: fn.test\r\nSubject: signed over NNTP\r\n"
                b"Message-ID: <" + stem.encode() + b"@example.invalid>\r\n"
                b"\r\n.dot-prefixed signed body\r\nexact post source\r\n")
            carried = self.root / (stem + ("-tampered" if tamper else "")
                                   + "-carried.eml")
            signed = self.invoke(
                "hybrid-sign-carrier", str(principal or self.principal),
                str(self.ed_public), str(self.ed_secret), str(self.ml_public),
                str(self.ml_private), str(source), str(carried))
            self.assertEqual(signed.returncode, 0, signed.stderr.decode())
            octets = carried.read_bytes()
            if tamper:
                octets = octets.replace(b"exact post source",
                                        b"Exact post source", 1)
            return octets

        def post(octets):
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(b"POST\r\n")
                    self.assertTrue(stream.readline().startswith(b"340 "))
                    body = b"".join(
                        (b"." + line if line.startswith(b".") else line)
                        for line in octets.splitlines(keepends=True))
                    stream.write(body + b".\r\n")
                    return stream.readline()

        def verdict(msgid):
            with socket.create_connection(("127.0.0.1", self.port), timeout=30) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(b"HDR :fn-verified " + msgid + b"\r\n")
                    status = stream.readline()
                    if not status.startswith(b"225 "):
                        return status
                    field = stream.readline()
                    self.assertEqual(stream.readline(), b".\r\n")
                    return field

        unsigned = (b"From: agent@example.invalid\r\nNewsgroups: fn.test\r\n"
                    b"Subject: unsigned over NNTP\r\n"
                    b"Message-ID: <nntp-unsigned@example.invalid>\r\n\r\nplain\r\n")
        owner = self.start_owner()
        try:
            enrolled = self.invoke("hybrid-enroll", str(self.control), "1",
                                   str(self.principal), str(self.ed_public),
                                   str(self.ml_public))
            self.assertEqual(enrolled.returncode, 0, enrolled.stderr.decode())
            # Present, tampered: the primitive observation refuses; the
            # Message-ID is then still free for the valid post below.
            self.assertEqual(
                post(carrier("nntp-signed", tamper=True)),
                b"441 posting failed; the author signature does not verify\r\n")
            # Present, signed by a principal this Store never enrolled.
            self.assertEqual(
                post(carrier("nntp-unenrolled", principal=other_principal)),
                b"441 posting failed; the signer has no current enrollment here"
                b" (local-enrollment)\r\n")
            # Present, malformed: never the unsigned arm.
            malformed = (b"FN-Authorship: !!!\r\n" + unsigned.replace(
                b"nntp-unsigned", b"nntp-malformed"))
            self.assertEqual(
                post(malformed),
                b"441 posting failed; the FN-Authorship carrier is malformed\r\n")
            # Present and valid under the enrollment: kind-4, verified.
            self.assertTrue(post(carrier("nntp-signed")).startswith(b"240 "))
            self.assertEqual(verdict(b"<nntp-signed@example.invalid>"),
                             b"0 verified " + b"55" * 32 + b" keyring 1\r\n")
            # Absent: the unsigned arm, unchanged.
            self.assertTrue(post(unsigned).startswith(b"240 "))
            for refused in (b"<nntp-unenrolled@example.invalid>",
                            b"<nntp-malformed@example.invalid>"):
                self.assertTrue(verdict(refused).startswith(b"430 "), refused)
        finally:
            self.stop_owner(owner)
        owner = self.start_owner()
        try:
            self.assertEqual(verdict(b"<nntp-signed@example.invalid>"),
                             b"0 verified " + b"55" * 32 + b" keyring 1\r\n")
        finally:
            self.stop_owner(owner)

    def test_authored_carrier_survives_native_peering_and_receiver_restart(self):
        """Real owner/feed/receiver path; portable verification is independent.

        Since receiver-local authorship at transit ingress
        (planning/evidence/peer-authored-ingress-2026-09-24.md) the receiver
        stores a signed carrier only under its OWN current enrollment of the
        carried principal (fn-pa-current-plan); without one it answers 439
        with reason local-enrollment.  The receiver therefore enrolls the
        author's key set here, as the two-Store join provisions it, and its
        own HDR :fn-verified verdict is checked after delivery and restart.
        Protected transport has its own gate. Both peers are loopback fixtures.
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
            for control in (self.control, other_control):
                ok("hybrid-enroll", control, "1", self.principal,
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
            # The receiver's own kind-4 verdict, recovered after restart.
            with socket.create_connection(("127.0.0.1", other_port), timeout=15) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(b"HDR :fn-verified " + msgid.encode() + b"\r\n")
                    self.assertEqual(stream.readline(), b"225 headers follow\r\n")
                    self.assertEqual(stream.readline(),
                                     b"0 verified " + b"55" * 32 + b" keyring 1\r\n")
                    self.assertEqual(stream.readline(), b".\r\n")
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)

    def test_unenrolled_receiver_refuses_authored_carrier_once_and_both_sides_log_it(self):
        """A receiver without its own enrollment of the principal refuses.

        The refusal is 439 (refused, not deferred), so the sender drops the
        entry and does not re-offer it; each side writes exactly one
        ACL2-rendered line naming the refusal (books/owner-log.lisp
        fn-olog-transit-line, fn-olog-feed-reply-line).  This is the 1a9dd747
        failure-8 configuration with its silence removed.
        """
        other_store = self.root / "receiver"
        other_control = self.root / "receiver.sock"
        other_log = self.root / "receiver.log"
        other_port = free_port()
        other_config = self.root / "receiver.toml"
        other_config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                other_store, other_port, other_control, other_log), encoding="ascii")

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
        msgid = "<hybrid-unenrolled-relay@example.invalid>"
        source = self.root / "unenrolled-source.eml"
        source.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\nSubject: unenrolled relay\r\n"
            b"Message-ID: " + msgid.encode() + b"\r\n\r\nbody\r\n")
        signed = ok("hybrid-sign", self.principal, self.ed_public,
                    self.ed_secret, self.ml_public, self.ml_private, source)
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_sig, ml_sig = self.root / "unenrolled-ed.sig", self.root / "unenrolled-ml.sig"
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        owners = []
        try:
            for config in (self.config, other_config):
                proc = subprocess.Popen(
                    [str(IMAGE), "--fn", "operator", str(config), "run"],
                    cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                owners.append(proc)
                wait_for_announcement(proc, b"LISTENING ")
            ok("hybrid-enroll", self.control, "1", self.principal,
               self.ed_public, self.ml_public)
            ok("hybrid-author", self.control, "1", source, ed_sig, ml_sig, self.ml_public)
            sender_line = ("refused feed peer=other message-id=" + msgid + " code=439 ")
            receiver_line = ("refused transit connection=")
            deadline = time.monotonic() + 30
            while time.monotonic() < deadline:
                sent = self.service_log.read_text() if self.service_log.exists() else ""
                if sender_line in sent:
                    break
                time.sleep(0.2)
            self.assertIn(sender_line, sent)
            received = other_log.read_text()
            refusals = [line for line in received.splitlines()
                        if line.startswith(receiver_line)]
            self.assertEqual(len(refusals), 1, received)
            self.assertIn(" message-id=" + msgid + " code=439 decision=want ", refusals[0])
            self.assertIn(" detail=no-local-binding ", refusals[0])
            # Refused is final: no re-offer after several backoff periods.
            time.sleep(4)
            self.assertEqual(self.service_log.read_text().count(sender_line), 1)
            self.assertEqual(
                sum(1 for line in other_log.read_text().splitlines()
                    if line.startswith(receiver_line)), 1)
            with socket.create_connection(("127.0.0.1", other_port), timeout=15) as sock:
                with sock.makefile("rwb", buffering=0) as stream:
                    self.assertTrue(stream.readline().startswith(b"200 "))
                    stream.write(b"STAT " + msgid.encode() + b"\r\n")
                    self.assertTrue(stream.readline().startswith(b"430 "))
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)

    # ------------------------------------------------------------------
    # D23: A signs and posts; relay R has no enrollment of A's principal and
    # allowlists it on its boundary for A (`carries HEX'); C enrolls it.  R
    # stores and relays with a `carried' verdict, C verifies.  Without the
    # list R refuses (439, no-local-binding), as D02 did.  PRF-099: a listed
    # principal is carried only within the boundary's budget.
    def _chain(self, listed, budget=("1048576", "8")):
        nodes = {}
        for name in ("relay", "sink"):
            root = self.root / name
            nodes[name] = {"store": root, "control": self.root / (name + ".sock"),
                           "log": self.root / (name + ".log"), "port": free_port(),
                           "config": self.root / (name + ".toml")}
            n = nodes[name]
            n["config"].write_text(
                '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                    n["store"], n["port"], n["control"], n["log"]), encoding="ascii")
        relay, sink = nodes["relay"], nodes["sink"]

        def ok(*args):
            result = self.invoke(*map(str, args), timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr.decode("utf-8", "replace"))
            return result

        hexp = self.principal.read_bytes().hex()
        for n in (relay, sink):
            ok("store", n["store"], "init", "fn.test")
        ok("operator", self.config, "policy", "set", "path-identity", "author.example.invalid")
        ok("operator", relay["config"], "policy", "set", "path-identity", "relay.example.invalid")
        ok("operator", sink["config"], "policy", "set", "path-identity", "sink.example.invalid")
        # A feeds R.  R takes A's feed (source 127.0.0.1) and feeds C; its C
        # record's source address is one nothing connects from.  C takes R.
        ok("operator", self.config, "peer", "add", "relay", "relay.example.invalid",
           "127.0.0.1", relay["port"], "-", "fn.*", "127.0.0.9", "true")
        carries = ["carries", hexp] if listed else []
        ok("operator", relay["config"], "peer", "add", "author", "author.example.invalid",
           "127.0.0.1", self.port, "fn.*", "-", "127.0.0.1", "true", *carries)
        if listed and budget:
            ok("operator", relay["config"], "peer", "budget", "author", *budget)
        ok("operator", relay["config"], "peer", "add", "sink", "sink.example.invalid",
           "127.0.0.1", sink["port"], "-", "fn.*", "127.0.0.9", "true")
        ok("operator", sink["config"], "peer", "add", "relay", "relay.example.invalid",
           "127.0.0.1", relay["port"], "fn.*", "-", "127.0.0.1", "true")
        msgid = "<d23-carried-{}@example.invalid>".format("listed" if listed else "unlisted")
        source = self.root / "d23-source.eml"
        source.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Thu, 24 Sep 2026 22:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\nSubject: carried relay\r\n"
            b"Message-ID: " + msgid.encode() + b"\r\n\r\ncarried body\r\n")
        signed = ok("hybrid-sign", self.principal, self.ed_public,
                    self.ed_secret, self.ml_public, self.ml_private, source)
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_sig, ml_sig = self.root / "d23-ed.sig", self.root / "d23-ml.sig"
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        return nodes, msgid, source, ed_sig, ml_sig, ok

    def _hdr(self, port, msgid):
        with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
            with sock.makefile("rwb", buffering=0) as stream:
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"HDR :fn-verified " + msgid.encode() + b"\r\n")
                status = stream.readline()
                if not status.startswith(b"225 "):
                    return None
                line = stream.readline()
                self.assertEqual(stream.readline(), b".\r\n")
                return line

    def _start(self, owners, config):
        proc = subprocess.Popen([str(IMAGE), "--fn", "operator", str(config), "run"],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        owners.append(proc)
        wait_for_announcement(proc, b"LISTENING ")

    def _verify(self, port, msgid):
        keyring = self.root / "d23-keyring.json"
        entry = subprocess.run([sys.executable, str(ROOT / "tools" / "fn_verify.py"),
                                "keyring-entry", str(self.principal), str(self.ed_public),
                                str(self.ml_public)], stdout=subprocess.PIPE, check=True)
        keyring.write_text('{"format": "fn-verify-keyring-v1", "principals": [%s]}'
                           % entry.stdout.decode().strip())
        run = subprocess.run([sys.executable, str(ROOT / "tools" / "fn_verify.py"),
                              msgid, "--node", "127.0.0.1:{}".format(port), "--plain",
                              "--keyring", str(keyring)],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
        return run.returncode, run.stdout.decode("utf-8", "replace")

    def test_d23_allowlisted_relay_carries_and_the_enrolled_sink_verifies(self):
        nodes, msgid, source, ed_sig, ml_sig, ok = self._chain(listed=True)
        relay, sink = nodes["relay"], nodes["sink"]
        owners = []
        try:
            for config in (self.config, relay["config"], sink["config"]):
                self._start(owners, config)
            for control in (self.control, sink["control"]):
                ok("hybrid-enroll", control, "1", self.principal,
                   self.ed_public, self.ml_public)
            ok("hybrid-author", self.control, "1", source, ed_sig, ml_sig, self.ml_public)
            deadline, at_sink = time.monotonic() + 60, None
            while time.monotonic() < deadline:
                at_sink = self._hdr(sink["port"], msgid)
                if at_sink is not None:
                    break
                time.sleep(0.2)
            hexp = self.principal.read_bytes().hex().encode()
            self.assertEqual(self._hdr(relay["port"], msgid), b"0 carried " + hexp + b"\r\n")
            self.assertEqual(at_sink, b"0 verified " + hexp + b" keyring 1\r\n")
            carried = [line for line in relay["log"].read_text().splitlines()
                       if " message-id=" + msgid + " " in line and " detail=carried " in line]
            self.assertEqual(len(carried), 1, relay["log"].read_text())
            if os.environ.get("FN_D23_VERIFY") == "1":
                self.assertEqual(self._verify(sink["port"], msgid)[0], 0)
                code, out = self._verify(relay["port"], msgid)
                self.assertEqual(code, 3, out)
                self.assertIn("carried this article", out)
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)

    def test_d23_unlisted_relay_refuses_439_and_logs_it(self):
        nodes, msgid, source, ed_sig, ml_sig, ok = self._chain(listed=False)
        relay = nodes["relay"]
        owners = []
        try:
            for config in (self.config, relay["config"]):
                self._start(owners, config)
            ok("hybrid-enroll", self.control, "1", self.principal,
               self.ed_public, self.ml_public)
            ok("hybrid-author", self.control, "1", source, ed_sig, ml_sig, self.ml_public)
            sender_line = "refused feed peer=relay message-id=" + msgid + " code=439 "
            deadline, sent = time.monotonic() + 30, ""
            while time.monotonic() < deadline:
                sent = self.service_log.read_text() if self.service_log.exists() else ""
                if sender_line in sent:
                    break
                time.sleep(0.2)
            self.assertIn(sender_line, sent)
            refusals = [line for line in relay["log"].read_text().splitlines()
                        if line.startswith("refused transit ") and msgid in line]
            self.assertEqual(len(refusals), 1, relay["log"].read_text())
            self.assertIn(" detail=no-local-binding ", refusals[0])
            self.assertIsNone(self._hdr(relay["port"], msgid))
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)

    # ------------------------------------------------------------------
    # PRF-099: the opaque-carriage budget and the refusal classes.
    def _sign(self, msgid, body):
        source = self.root / ("pcb-" + str(abs(hash(msgid))) + ".eml")
        source.write_bytes(
            b"From: author@example.invalid\r\n"
            b"Date: Thu, 24 Sep 2026 22:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\nSubject: carried budget\r\n"
            b"Message-ID: " + msgid.encode() + b"\r\n\r\n" + body + b"\r\n")
        signed = self.invoke("hybrid-sign", *map(str, (
            self.principal, self.ed_public, self.ed_secret, self.ml_public,
            self.ml_private, source)), timeout=180)
        self.assertEqual(signed.returncode, 0, signed.stderr)
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_sig, ml_sig = source.with_suffix(".ed"), source.with_suffix(".ml")
        ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        return source, ed_sig, ml_sig

    def _article(self, port, msgid):
        with socket.create_connection(("127.0.0.1", port), timeout=15) as sock:
            with sock.makefile("rwb", buffering=0) as stream:
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"ARTICLE " + msgid.encode() + b"\r\n")
                self.assertTrue(stream.readline().startswith(b"220 "))
                article = bytearray()
                while True:
                    line = stream.readline(65536)
                    self.assertTrue(line)
                    if line == b".\r\n":
                        return bytes(article)
                    article.extend(line[1:] if line.startswith(b"..") else line)

    def _ihave(self, port, msgid, article):
        with socket.create_connection(("127.0.0.1", port), timeout=30) as sock:
            with sock.makefile("rwb", buffering=0) as stream:
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"IHAVE " + msgid.encode() + b"\r\n")
                self.assertTrue(stream.readline().startswith(b"335 "))
                for line in article.split(b"\r\n")[:-1]:
                    stream.write((b"." + line if line.startswith(b".") else line)
                                 + b"\r\n")
                stream.write(b".\r\n")
                return stream.readline()

    @staticmethod
    def _patch_carrier(article, msgid, patch):
        """Rewrite the FN-Authorship items with PATCH (a function of the
        binary) and the Message-ID with MSGID; everything else unchanged."""
        import base64, re
        head, body = article.split(b"\r\n\r\n", 1)
        lines = head.split(b"\r\n")
        out, i = [], 0
        while i < len(lines):
            line = lines[i]
            if line.lower().startswith(b"fn-authorship:"):
                value = line.split(b":", 1)[1]
                while i + 1 < len(lines) and lines[i + 1][:1] in (b" ", b"\t"):
                    i += 1
                    value += lines[i]
                binary = bytearray(base64.b64decode(re.sub(rb"\s", b"", value)))
                encoded = base64.b64encode(bytes(patch(binary)))
                folded = [encoded[k:k + 64] for k in range(0, len(encoded), 64)]
                out.append(b"FN-Authorship: " + folded[0])
                out.extend(b" " + chunk for chunk in folded[1:])
            elif line.lower().startswith(b"message-id:"):
                out.append(b"Message-ID: " + msgid.encode())
            elif line.lower().startswith(b"path:"):
                out.append(b"Path: author.example.invalid!not-for-mail")
            elif line.lower().startswith(b"xref:"):
                pass
            else:
                out.append(line)
            i += 1
        return b"\r\n".join(out) + b"\r\n\r\n" + body

    def test_carried_budget_and_refusal_classes(self):
        nodes, msgid, source, ed_sig, ml_sig, ok = self._chain(listed=False)
        relay = nodes["relay"]
        hexp = self.principal.read_bytes().hex()
        # The list and the budget arrive by separate requests.
        ok("operator", relay["config"], "peer", "carries", "author", hexp)
        ok("operator", relay["config"], "peer", "budget", "author", "1048576", "1")
        owners = []
        try:
            for config in (self.config, relay["config"]):
                self._start(owners, config)
            ok("hybrid-enroll", self.control, "1", self.principal,
               self.ed_public, self.ml_public)
            ok("hybrid-author", self.control, "1", source, ed_sig, ml_sig, self.ml_public)
            deadline = time.monotonic() + 60
            while time.monotonic() < deadline and self._hdr(relay["port"], msgid) is None:
                time.sleep(0.2)
            self.assertEqual(self._hdr(relay["port"], msgid),
                             b"0 carried " + hexp.encode() + b"\r\n")
            # The second carried article exhausts the count of one.
            second = "<pcb-second@example.invalid>"
            src2, ed2, ml2 = self._sign(second, b"second carried body")
            ok("hybrid-author", self.control, "1", src2, ed2, ml2, self.ml_public)
            want = " message-id=" + second + " "
            deadline, lines = time.monotonic() + 60, []
            while time.monotonic() < deadline:
                lines = [l for l in relay["log"].read_text().splitlines()
                         if l.startswith("refused transit ") and want in l]
                if lines:
                    break
                time.sleep(0.2)
            self.assertEqual(len(lines), 1, relay["log"].read_text())
            self.assertIn(" detail=carried-count-exhausted ", lines[0])
            self.assertIsNone(self._hdr(relay["port"], second))
            # From the author's address, by IHAVE: items naming suite 2, and a
            # principal the relay neither enrolled nor carries.
            carried = self._article(relay["port"], msgid)

            def suite_two(binary):
                binary[1] = 2
                return binary

            def other_principal(binary):
                binary[4] ^= 0xFF
                return binary

            for name, patch, detail in (
                    ("<pcb-unsupported@example.invalid>", suite_two,
                     "unsupported-profile"),
                    ("<pcb-unbound@example.invalid>", other_principal,
                     "no-local-binding")):
                reply = self._ihave(relay["port"], name,
                                    self._patch_carrier(carried, name, patch))
                self.assertTrue(reply.startswith(b"437 "), reply)
                lines = [l for l in relay["log"].read_text().splitlines()
                         if l.startswith("refused transit ")
                         and " message-id=" + name + " " in l]
                self.assertEqual(len(lines), 1, relay["log"].read_text())
                self.assertIn(" detail=" + detail + " ", lines[0])
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)

    def test_carrying_boundary_without_budget_carries_nothing(self):
        nodes, msgid, source, ed_sig, ml_sig, ok = self._chain(listed=True, budget=None)
        relay = nodes["relay"]
        owners = []
        try:
            for config in (self.config, relay["config"]):
                self._start(owners, config)
            ok("hybrid-enroll", self.control, "1", self.principal,
               self.ed_public, self.ml_public)
            ok("hybrid-author", self.control, "1", source, ed_sig, ml_sig, self.ml_public)
            want = " message-id=" + msgid + " "
            deadline, lines = time.monotonic() + 60, []
            while time.monotonic() < deadline:
                lines = [l for l in relay["log"].read_text().splitlines()
                         if l.startswith("refused transit ") and want in l]
                if lines:
                    break
                time.sleep(0.2)
            self.assertEqual(len(lines), 1, relay["log"].read_text())
            self.assertIn(" detail=carried-budget-unset ", lines[0])
            self.assertIsNone(self._hdr(relay["port"], msgid))
        finally:
            for owner in reversed(owners):
                self.stop_owner(owner)


if __name__ == "__main__":
    unittest.main()
