"""Isolated e160 native A/B owner for Mini's finite E1/E2 handoff."""
import json
import os
from pathlib import Path
import re
import socket
import ssl
import subprocess
import time

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import ed25519
from tests.test_native_protected_peering import NativeProtectedPeeringTests, IMAGE, free_port

OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
HANDOFF = Path(os.environ["FN_E1E2_HANDOFF"])
R_INPUT = Path(os.environ["FN_E1E2_R_SOURCE"])
R_ID = "<mini-e1-1bea29c16a63e8722f156770@example.invalid>"


class NativeTwoStoreMiniHandoff(NativeProtectedPeeringTests):
    def native(self, *args, expected=0):
        return self.command([IMAGE, "--fn", *args], expected=expected)

    def signer(self, root, label, principal_byte):
        key = ed25519.Ed25519PrivateKey.generate()
        seed = key.private_bytes(serialization.Encoding.Raw,
                                 serialization.PrivateFormat.Raw,
                                 serialization.NoEncryption())
        ed = key.public_key().public_bytes(serialization.Encoding.Raw,
                                           serialization.PublicFormat.Raw)
        principal = root / (label + "-principal.bin")
        ed_public = root / (label + "-ed-public.bin")
        ed_secret = root / (label + "-ed-secret.bin")
        ml_private = root / (label + "-ml-private.pem")
        ml_public = root / (label + "-ml-public.pem")
        ml_raw = root / (label + "-ml-public.raw")
        principal.write_bytes(bytes([principal_byte]) * 32)
        ed_public.write_bytes(ed)
        ed_secret.write_bytes(seed + ed)
        generated = subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65",
                                    "-out", str(ml_private)], capture_output=True,
                                   timeout=60)
        self.assertEqual(generated.returncode, 0, generated.stderr)
        exported = subprocess.run([OPENSSL, "pkey", "-in", str(ml_private),
                                   "-pubout", "-out", str(ml_public)],
                                  capture_output=True, timeout=60)
        self.assertEqual(exported.returncode, 0, exported.stderr)
        raw = subprocess.run([OPENSSL, "asn1parse", "-inform", "PEM", "-in",
                              str(ml_public), "-strparse", "17", "-noout",
                              "-out", str(ml_raw)], capture_output=True, timeout=60)
        self.assertEqual(raw.returncode, 0, raw.stderr)
        self.assertEqual(len(ml_raw.read_bytes()), 1952)
        return dict(principal=principal, ed_public=ed_public, ed_secret=ed_secret,
                    ml_public=ml_public, ml_private=ml_private, ml_raw=ml_raw)

    def enroll(self, node, generation, signer):
        self.native("hybrid-enroll", node["control"], generation,
                    signer["principal"], signer["ed_public"], signer["ml_public"])

    def verify(self, carrier, signer, source):
        answer = self.native("hybrid-verify-source", carrier, signer["ml_public"])
        fields = answer.stdout.decode("ascii").strip().split()
        self.assertEqual(len(fields), 6, answer.stdout)
        self.assertEqual(fields[0], "fn-portable-v1")
        self.assertEqual(fields[1], signer["principal"].read_bytes().hex())
        self.assertEqual(fields[3], signer["ed_public"].read_bytes().hex())
        self.assertEqual(fields[4], signer["ml_raw"].read_bytes().hex())
        self.assertEqual(bytes.fromhex(fields[5]), source)
        return answer.stdout, fields[2]

    def consumer(self, verb, node, *args):
        return self.native("consumer", verb, node["control"], *args)

    def projected_source(self, cursor, report):
        fields = self.native("consumer-project", cursor, report).stdout.decode("ascii").strip().split()
        self.assertEqual(len(fields), 18, fields)
        self.assertEqual(fields[0], "fn-consumer-project-v1")
        return bytes.fromhex(fields[14]), bytes.fromhex(fields[13]).decode("ascii")

    def verified_header(self, node, message_id):
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=15) as raw:
            with raw.makefile("rwb", buffering=0) as stream:
                self.assertTrue(stream.readline().startswith((b"200 ", b"201 ")))
                stream.write(b"STARTTLS\r\n")
                self.assertTrue(stream.readline().startswith(b"382 "))
            context = ssl.create_default_context(cafile=str(node["certificate"]))
            with context.wrap_socket(raw, server_hostname="localhost") as tls:
                with tls.makefile("rwb", buffering=0) as stream:
                    stream.write(b"AUTHINFO USER " + node["login"].encode() + b"\r\n")
                    self.assertTrue(stream.readline().startswith(b"381 "))
                    stream.write(b"AUTHINFO PASS " + node["password"].encode() + b"\r\n")
                    self.assertTrue(stream.readline().startswith(b"281 "))
                    stream.write(b"HDR :fn-verified " + message_id.encode() + b"\r\n")
                    status = stream.readline()
                    if not status.startswith(b"225 "):
                        return status
                    value = stream.readline()
                    self.assertEqual(stream.readline(), b".\r\n")
                    return value

    def test_two_store_mini_exchange(self):
        self.assertTrue(HANDOFF.is_absolute())
        self.assertFalse(HANDOFF.exists())
        source = R_INPUT.read_bytes()
        self.assertIn(("Message-ID: " + R_ID).encode("ascii"), source)
        a = self.initialize("a", free_port(), "b-at-a", "isolated-a-secret")
        b = self.initialize("b", free_port(), "a-at-b", "isolated-b-secret")
        self.configure_peer(a, b, self.profile(a, b))
        self.configure_peer(b, a, self.profile(b, a))
        r = self.signer(a["root"], "r", 0x52)
        q = self.signer(b["root"], "q", 0x51)
        self.assertNotEqual(r["principal"].read_bytes(), q["principal"].read_bytes())
        self.assertNotEqual(r["ed_public"].read_bytes(), q["ed_public"].read_bytes())
        self.assertNotEqual(r["ml_raw"].read_bytes(), q["ml_raw"].read_bytes())
        r_source = a["root"] / "r.source"
        r_source.write_bytes(source)
        self.start(a)
        self.start(b)
        self.consumer("bootstrap", a)
        self.consumer("bootstrap", b)
        a_registered = a["root"] / "a-registered.fncu"
        b_registered = b["root"] / "b-registered.fncu"
        self.consumer("register", a, "worker-a", "fn.test", a_registered)
        self.consumer("register", b, "worker", "fn.test", b_registered)
        self.enroll(a, 1, r)
        self.enroll(b, 1, r)
        signed = self.native("hybrid-sign", r["principal"], r["ed_public"],
                             r["ed_secret"], r["ml_public"], r["ml_private"], r_source)
        values = dict(line.split() for line in signed.stdout.decode("ascii").splitlines())
        ed_sig = a["root"] / "r-ed.sig"
        ml_sig = a["root"] / "r-ml.sig"
        ed_sig.write_bytes(bytes.fromhex(values["ed25519"]))
        ml_sig.write_bytes(bytes.fromhex(values["ml-dsa-65"]))
        self.native("hybrid-author", a["control"], 1, r_source, ed_sig, ml_sig, r["ml_public"])
        r_at_b = self.await_article(b, R_ID, timeout=120)
        r_carrier = b["root"] / "r-at-b.eml"
        r_carrier.write_bytes(r_at_b)
        _, r_source_id = self.verify(r_carrier, r, source)
        # The receiver verdict must be in its completed Store history, not
        # merely in the owner process that handled the peer connection.
        b["process"].terminate()
        b["process"].wait(timeout=30)
        self.start(b)
        self.assertEqual(self.await_article(b, R_ID, timeout=30), r_at_b)
        r_header_b_gen1 = self.verified_header(b, R_ID)
        expected_r_header = (b"0 verified " + r["principal"].read_bytes().hex().encode("ascii")
                             + b" keyring 1\r\n")
        self.assertEqual(r_header_b_gen1, expected_r_header)
        preflight = os.environ.get("FN_E1E2_PREFLIGHT_ARTIFACTS")
        if preflight:
            target = Path(preflight)
            target.mkdir(parents=True, exist_ok=True)
            (target / "b-r-header-gen1.txt").write_bytes(r_header_b_gen1)
        r_at_a = a["root"] / "r-at-a.eml"
        r_at_a.write_bytes(self.await_article(a, R_ID, timeout=30))
        self.verify(r_at_a, r, source)
        a_r_cursor = a["root"] / "a-r.fncu"
        a_r_report = a["root"] / "a-r.fn-e"
        self.consumer("poll", a, "worker-a", a_r_cursor, a_r_report)
        observed_source, observed_id = self.projected_source(a_r_cursor, a_r_report)
        self.assertEqual(observed_source, source)
        self.assertEqual(observed_id, R_ID)
        self.consumer("ack", a, a_r_cursor)
        self.enroll(a, 2, q)
        self.enroll(b, 2, q)
        r_header_b_gen2 = self.verified_header(b, R_ID)
        self.assertEqual(r_header_b_gen2, expected_r_header)
        if preflight:
            (Path(preflight) / "b-r-header-gen2.txt").write_bytes(r_header_b_gen2)
        preview_cursor = b["root"] / "b-preview.fncu"
        preview_report = b["root"] / "b-preview.fn-e"
        self.consumer("poll", b, "worker", preview_cursor, preview_report)
        if preflight:
            target = Path(preflight)
            target.mkdir(parents=True, exist_ok=True)
            (target / "b-preview.fncu").write_bytes(preview_cursor.read_bytes())
            (target / "b-preview.fn-e").write_bytes(preview_report.read_bytes())
            (target / "r-at-b.eml").write_bytes(r_at_b)
            answer = self.native("consumer-project", preview_cursor, preview_report,
                                 expected=1)
            (target / "b-project-refusal.txt").write_bytes(answer.stdout + answer.stderr)
        observed_source, observed_id = self.projected_source(preview_cursor, preview_report)
        self.assertEqual(observed_source, source)
        self.assertEqual(observed_id, R_ID)
        if os.environ.get("FN_E1E2_PREFLIGHT") == "1":
            return
        password_file = b["root"] / "observer.password"
        password_file.write_text(b["password"] + "\n", encoding="ascii")
        password_file.chmod(0o600)
        HANDOFF.mkdir(parents=True)
        ready = {"version": 1, "image": str(IMAGE), "a_control": str(a["control"]),
                 "b_control": str(b["control"]), "a_port": a["port"], "b_port": b["port"],
                 "consumer_b": "worker", "r_message_id": R_ID,
                 "r_source": str(r_source), "r_carrier_b": str(r_carrier),
                 "r_principal": str(r["principal"]), "r_ed_public": str(r["ed_public"]),
                 "r_ml_public": str(r["ml_public"]), "r_ml_public_raw": str(r["ml_raw"]),
                 "b_registered_cursor": str(b_registered), "b_preview_cursor": str(preview_cursor),
                 "b_preview_report": str(preview_report), "q_principal": str(q["principal"]),
                 "q_ed_public": str(q["ed_public"]), "q_ed_secret": str(q["ed_secret"]),
                 "q_ml_public": str(q["ml_public"]), "q_ml_public_raw": str(q["ml_raw"]),
                 "q_ml_private": str(q["ml_private"]), "q_generation": 2,
                 "b_login": b["login"], "b_password_file": str(password_file),
                 "b_tls_cert": str(b["certificate"])}
        (HANDOFF / "ready.json.tmp").write_text(json.dumps(ready, sort_keys=True) + "\n")
        (HANDOFF / "ready.json.tmp").replace(HANDOFF / "ready.json")
        deadline = time.monotonic() + 900
        marker = HANDOFF / "mini-finished.json"
        while not marker.is_file() and time.monotonic() < deadline:
            self.assertIsNone(a["process"].poll(), "A owner exited before Mini marker")
            self.assertIsNone(b["process"].poll(), "B owner exited before Mini marker")
            time.sleep(0.1)
        self.assertTrue(marker.is_file(), "Mini marker timed out")
        outcome = json.loads(marker.read_text("ascii"))
        self.assertEqual(outcome["result"], "accepted")
        q_id = outcome["message_id"]
        q_source = (HANDOFF / "posted.source").read_bytes()
        self.assertTrue(q_id.startswith("<") and q_id.endswith(">"))
        self.assertIn(("In-Reply-To: " + R_ID).encode("ascii"), q_source)
        q_at_a = self.await_article(a, q_id, timeout=120)
        self.stop_all()
        self.start(a)
        self.start(b)
        q_at_a_reopen = self.await_article(a, q_id, timeout=60)
        self.assertEqual(q_at_a_reopen, q_at_a)
        q_carrier = HANDOFF / "a-q-carrier.eml"
        q_carrier.write_bytes(q_at_a_reopen)
        verifier, source_id = self.verify(q_carrier, q, q_source)
        self.assertEqual(source_id, outcome["source_identity"])
        (HANDOFF / "a-q-verifier.txt").write_bytes(verifier)
        (HANDOFF / "a-q-verified-source.bin").write_bytes(q_source)
        before = a["root"] / "a-before-q.fncu"
        after = a["root"] / "a-after-q.fncu"
        q_cursor = HANDOFF / "a-q-poll.fncu"
        q_report = HANDOFF / "a-q-poll.fn-e"
        self.consumer("position", a, "worker-a", before)
        self.consumer("poll", a, "worker-a", q_cursor, q_report)
        observed_source, observed_id = self.projected_source(q_cursor, q_report)
        self.assertEqual(observed_source, q_source)
        self.assertEqual(observed_id, q_id)
        self.consumer("position", a, "worker-a", after)
        self.assertEqual(before.read_bytes(), after.read_bytes())
        finished = {"result": "accepted", "message_id": q_id,
                    "source_identity": source_id, "a_q_position_unchanged": True}
        (HANDOFF / "owner-finished.json.tmp").write_text(json.dumps(finished, sort_keys=True) + "\n")
        (HANDOFF / "owner-finished.json.tmp").replace(HANDOFF / "owner-finished.json")
