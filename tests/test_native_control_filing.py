"""Opt-in native witness for control-message filing (packet C1).

A control article (RFC 5537 section 5: one carrying a Control field) is filed
only in control.<verb> when the operator created that group, and refused
:control-not-filed otherwise; it is never stored in the groups its Newsgroups
field names (RFC 5537 section 3.7).  A Subject starting "cmsg " does not make
an article a control message.  The decision is ACL2's fn-pa-filing-plan
(books/peer-authored-accept.lisp), called first by host/native/owner.lisp
fnn-owner-attempt-transit; these cases drive the served POST and the NNTP
transit (IHAVE) ingress of the saved image.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest tests.test_native_control_filing
"""

import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def article(message_id, subject, control=None, path=None):
    lines = []
    if path:
        lines.append("Path: " + path)
    lines += ["From: poster@example.invalid", "Newsgroups: fn.test",
              "Subject: " + subject,
              "Date: Fri, 25 Sep 2026 03:00:00 +0000",
              "Message-ID: " + message_id]
    if control:
        lines.append("Control: " + control)
    return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeControlFilingTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-control-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.processes = []
        self.addCleanup(self.stop_all)

    def command(self, arguments, expected=0):
        result = subprocess.run(list(map(str, arguments)), cwd=ROOT, env=self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=180, check=False)
        self.assertEqual(result.returncode, expected, result)
        return result

    def initialize(self, name, groups):
        root = self.base / name
        root.mkdir()
        store, control = root / "store", root / "control.sock"
        port = free_port()
        self.command([IMAGE, "--fn", "store", store, "init", *groups])
        config = root / "fn.toml"
        config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            '[control]\npath = "{}"\n'.format(store, port, control), encoding="ascii")
        return {"name": name, "root": root, "config": config, "port": port}

    def start(self, node):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(node["config"]), "run"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.processes.append(process)
        node["process"] = process
        wait_for_announcement(process, b"LISTENING ")

    def stop(self, node):
        process = node.pop("process")
        process.terminate()
        _, err = process.communicate(timeout=60)
        self.processes.remove(process)
        return err.decode("utf-8", "replace")

    def stop_all(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                process.communicate(timeout=60)

    def session(self, node, lines):
        """One connection: send each command, collect its first reply line."""
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            replies = []
            for item in lines:
                stream.write(item)
                replies.append(stream.readline())
                if replies[-1][:3] in (b"211", b"220"):
                    body = []
                    while True:
                        line = stream.readline()
                        if line in (b".\r\n", b""):
                            break
                        body.append(line.rstrip(b"\r\n"))
                    replies.append(body)
            return replies

    def post(self, node, payload):
        first, second = self.session(node, [b"POST\r\n", payload + b".\r\n"])
        self.assertTrue(first.startswith(b"340"), first)
        return second

    def listgroup(self, node, group):
        return self.session(node, [b"LISTGROUP " + group + b"\r\n"])

    def article_reply(self, node, message_id):
        return self.session(node, [b"ARTICLE " + message_id.encode() + b"\r\n"])[0]

    def test_served_post(self):
        node = self.initialize("post", ["fn.test"])
        self.start(node)
        cancel = "<c1-cancel-1@example.invalid>"
        refused = self.post(node, article(cancel, "cmsg cancel <t@example.invalid>",
                                          control="cancel <t@example.invalid>"))
        cmsg = "<c1-cmsg@example.invalid>"
        ordinary = self.post(node, article(cmsg, "cmsg cancel <t@example.invalid>"))
        refused_absent = self.article_reply(node, cancel)
        fn_test_before = self.listgroup(node, b"fn.test")
        self.stop(node)
        self.command([IMAGE, "--fn", "operator", node["config"], "group", "create",
                      "control.cancel"])
        self.start(node)
        cancel2 = "<c1-cancel-2@example.invalid>"
        filed = self.post(node, article(cancel2, "x", control="cancel <t@example.invalid>"))
        in_control = self.listgroup(node, b"control.cancel")
        fn_test_after = self.listgroup(node, b"fn.test")
        served = self.article_reply(node, cancel2)
        self.stop(node)
        witness = {
            "post-cancel-without-group": refused.decode().strip(),
            "article-after-refusal": refused_absent.decode().strip(),
            "post-cmsg-subject": ordinary.decode().strip(),
            "listgroup-fn.test-before": [x.decode() if isinstance(x, bytes) else
                                         [y.decode() for y in x] for x in fn_test_before],
            "post-cancel-with-group": filed.decode().strip(),
            "listgroup-control.cancel": [x.decode() if isinstance(x, bytes) else
                                         [y.decode() for y in x] for x in in_control],
            "listgroup-fn.test-after": [x.decode() if isinstance(x, bytes) else
                                        [y.decode() for y in x] for x in fn_test_after],
            "article-filed": served.decode().strip(),
        }
        print("NATIVE-CONTROL-WITNESS " + json.dumps(witness, sort_keys=True))
        self.assertTrue(refused.startswith(b"441 "), refused)
        self.assertIn(b"control-not-filed", refused)
        self.assertTrue(refused_absent.startswith(b"430"), refused_absent)
        self.assertTrue(ordinary.startswith(b"240"), ordinary)
        self.assertTrue(filed.startswith(b"240"), filed)
        self.assertTrue(in_control[0].startswith(b"211 1 "), in_control)
        self.assertTrue(fn_test_after[0].startswith(b"211 1 "), fn_test_after)
        self.assertEqual(fn_test_before[1], fn_test_after[1])
        self.assertTrue(served.startswith(b"220"), served)

    def test_transit_ihave(self):
        target = self.initialize("target", ["fn.test"])
        self.command([IMAGE, "--fn", "operator", target["config"], "peer", "add",
                      "source", "source.example.invalid", "127.0.0.1",
                      str(free_port()), "fn.*", "-", "127.0.0.1", "true"])
        self.start(target)
        path = "source.example.invalid!not-for-mail"

        def offer(message_id, payload):
            return self.session(target, [b"IHAVE " + message_id.encode() + b"\r\n",
                                         payload + b".\r\n"])

        cancel = "<c1-transit-cancel-1@example.invalid>"
        refused = offer(cancel, article(cancel, "x", control="cancel <t@x.invalid>",
                                        path=path))
        cmsg = "<c1-transit-cmsg@example.invalid>"
        ordinary = offer(cmsg, article(cmsg, "cmsg cancel <t@x.invalid>", path=path))
        log_without = self.stop(target)
        self.command([IMAGE, "--fn", "operator", target["config"], "group", "create",
                      "control.cancel"])
        self.start(target)
        cancel2 = "<c1-transit-cancel-2@example.invalid>"
        filed = offer(cancel2, article(cancel2, "x", control="cancel <t@x.invalid>",
                                       path=path))
        log_with = self.stop(target)
        # The target's groups are read back through a reader port: a peer
        # address is not a reader, so reopen the same store without the peer.
        self.command([IMAGE, "--fn", "operator", target["config"], "peer", "remove",
                      "source"])
        self.start(target)
        in_control = self.listgroup(target, b"control.cancel")
        fn_test = self.listgroup(target, b"fn.test")
        absent = self.article_reply(target, cancel)
        self.stop(target)
        lines = [line for line in (log_without + log_with).splitlines()
                 if "control" in line or "transit" in line]
        witness = {
            "ihave-cancel-without-group": [x.decode().strip() for x in refused],
            "ihave-cmsg-subject": [x.decode().strip() for x in ordinary],
            "ihave-cancel-with-group": [x.decode().strip() for x in filed],
            "listgroup-control.cancel": [x.decode() if isinstance(x, bytes) else
                                         [y.decode() for y in x] for x in in_control],
            "listgroup-fn.test": [x.decode() if isinstance(x, bytes) else
                                  [y.decode() for y in x] for x in fn_test],
            "article-refused": absent.decode().strip(),
            "log": lines[:12],
        }
        print("NATIVE-CONTROL-WITNESS " + json.dumps(witness, sort_keys=True))
        self.assertTrue(refused[0].startswith(b"335"), refused)
        self.assertTrue(refused[1].startswith(b"437"), refused)
        # PKT-104: the 437 carries its reason (books/peer-inbound.lisp
        # fn-peer-transit-refusal-line over fn-post-store-refusal-text), fed
        # by host/native/owner.lisp fnn-owner-transit-complete, and its log
        # line (fn-olog-transit-line) names the code and the detail.
        self.assertEqual(
            refused[1],
            b"437 transfer rejected; control message not filed: its control group"
            b" is not configured here (control-not-filed)\r\n")
        self.assertTrue(any(line.startswith("refused transit ") and "code=437" in line
                            and "detail=control-not-filed" in line
                            and "message-id=" + cancel in line
                            for line in lines), lines)
        self.assertTrue(ordinary[1].startswith(b"235"), ordinary)
        self.assertTrue(filed[1].startswith(b"235"), filed)
        self.assertTrue(in_control[0].startswith(b"211 1 "), in_control)
        self.assertTrue(fn_test[0].startswith(b"211 1 "), fn_test)
        self.assertTrue(absent.startswith(b"430"), absent)

    @unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                         "set FN_RUN_HYBRID_E2E=1 (OpenSSL 3.5 with ML-DSA-65)")
    def test_signed_author(self):
        """The local signed-author ingress (host/native/hybrid-control.lisp
        fnn-hybrid-control-author) takes the same filing step: a signed
        control article is filed in control.cancel, the group its Store
        record's binding names (C3, books/hybrid-store.lisp
        fn-hsig-source-filed-groups), and never in fn.test, which its
        Newsgroups field names; a signed ordinary article from the same key
        is accepted into fn.test."""
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        node = self.initialize("author", ["fn.test", "control.cancel"])
        root = node["root"]
        principal, ed_public, ed_secret = (root / "principal.bin",
                                           root / "ed-public.bin", root / "ed-secret.bin")
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ml_private, ml_public = root / "ml-private.pem", root / "ml-public.pem"
        self.command([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out", ml_private])
        self.command([openssl, "pkey", "-in", ml_private, "-pubout", "-out", ml_public])
        control = root / "control.sock"
        self.start(node)

        def author(stem, message_id, control_field):
            source = root / (stem + ".eml")
            source.write_bytes(article(message_id, "signed " + stem,
                                       control=control_field))
            signed = self.command([IMAGE, "--fn", "hybrid-sign", principal, ed_public,
                                   ed_secret, ml_public, ml_private, source])
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = root / (stem + ".ed"), root / (stem + ".ml")
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            return subprocess.run(
                [str(IMAGE), "--fn", "hybrid-author", str(control), "1", str(source),
                 str(ed_sig), str(ml_sig), str(ml_public)], cwd=ROOT, env=self.env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180, check=False)

        self.command([IMAGE, "--fn", "hybrid-enroll", control, "1", principal,
                      ed_public, ml_public])
        cancel = "<c1-signed-cancel@example.invalid>"
        filed = author("cancel", cancel, "cancel <t@example.invalid>")
        ordinary = "<c1-signed-ordinary@example.invalid>"
        accepted = author("ordinary", ordinary, None)
        in_control = self.listgroup(node, b"control.cancel")
        fn_test = self.listgroup(node, b"fn.test")
        present = self.article_reply(node, cancel)
        self.stop(node)
        # Restart: replay's schema-1 binding (fn-hsig-carried-record-
        # metadatap) must admit the signed cancel's record in control.cancel.
        self.start(node)
        replayed = self.listgroup(node, b"control.cancel")
        self.stop(node)
        witness = {
            "hybrid-author-signed-cancel": [filed.returncode,
                                            filed.stdout.decode().strip(),
                                            filed.stderr.decode().strip()[-200:]],
            "hybrid-author-signed-ordinary": [accepted.returncode,
                                              accepted.stdout.decode().strip()],
            "listgroup-control.cancel": [x.decode() if isinstance(x, bytes) else
                                         [y.decode() for y in x] for x in in_control],
            "listgroup-fn.test": [x.decode() if isinstance(x, bytes) else
                                  [y.decode() for y in x] for x in fn_test],
            "article-signed-cancel": present.decode().strip(),
            "listgroup-control.cancel-after-restart": [
                x.decode() if isinstance(x, bytes) else [y.decode() for y in x]
                for x in replayed],
        }
        print("NATIVE-CONTROL-WITNESS " + json.dumps(witness, sort_keys=True))
        self.assertEqual(filed.returncode, 0, filed)
        self.assertEqual(accepted.returncode, 0, accepted)
        self.assertTrue(in_control[0].startswith(b"211 1 "), in_control)
        self.assertTrue(fn_test[0].startswith(b"211 1 "), fn_test)
        self.assertTrue(present.startswith(b"220"), present)
        self.assertTrue(replayed[0].startswith(b"211 1 "), replayed)


    def test_signed_withdrawal(self):
        """C3 on the served path (control-c3b): the owner's refresh
        (books/owner.lisp fn-own-refresh, fn-ctl-refresh-withdrawals and
        fn-ctl-refresh-visible) publishes the visible state.  A signed cancel
        by the target's own signer withdraws it from every view published
        after it (430 by Message-ID); a cancel committed before its target
        makes the target's first view exclude it; a cancel of an article
        whose verdict names nobody, by a principal holding no grant, changes
        nothing; a reader pinned before the cancel is recorded as it answers;
        a restart (a discontinuous refresh) publishes the same state."""
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        node = self.initialize("withdraw", ["fn.test", "control.cancel"])
        root = node["root"]
        principal, ed_public, ed_secret = (root / "principal.bin",
                                           root / "ed-public.bin", root / "ed-secret.bin")
        principal.write_bytes(bytes([85]) * 32)
        ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        ml_private, ml_public = root / "ml-private.pem", root / "ml-public.pem"
        self.command([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out", ml_private])
        self.command([openssl, "pkey", "-in", ml_private, "-pubout", "-out", ml_public])
        control = root / "control.sock"
        self.start(node)

        def author(stem, message_id, control_field):
            source = root / (stem + ".eml")
            source.write_bytes(article(message_id, "signed " + stem,
                                       control=control_field))
            signed = self.command([IMAGE, "--fn", "hybrid-sign", principal, ed_public,
                                   ed_secret, ml_public, ml_private, source])
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = root / (stem + ".ed"), root / (stem + ".ml")
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            done = subprocess.run(
                [str(IMAGE), "--fn", "hybrid-author", str(control), "1", str(source),
                 str(ed_sig), str(ml_sig), str(ml_public)], cwd=ROOT, env=self.env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180, check=False)
            return done.returncode

        def first_line(stream, command):
            stream.write(command)
            line = stream.readline()
            if line[:3] in (b"211", b"220"):
                while stream.readline() not in (b".\r\n", b""):
                    pass
            return line.decode().strip()

        self.command([IMAGE, "--fn", "hybrid-enroll", control, "1", principal,
                      ed_public, ml_public])
        target = "<c3b-target@example.invalid>"
        codes = {"target": author("target", target, None)}
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=30) as client:
            pinned = client.makefile("rwb", buffering=0)
            self.assertTrue(pinned.readline().startswith(b"200 "))
            pinned_before = first_line(pinned, b"ARTICLE " + target.encode() + b"\r\n")
            codes["cancel"] = author("cancel", "<c3b-cancel@example.invalid>",
                                     "cancel " + target)
            fresh = self.article_reply(node, target).decode().strip()
            pinned_after = first_line(pinned, b"ARTICLE " + target.encode() + b"\r\n")
        late = "<c3b-late@example.invalid>"
        codes["early-cancel"] = author("early", "<c3b-early@example.invalid>",
                                       "cancel " + late)
        codes["late-target"] = author("late", late, None)
        late_reply = self.article_reply(node, late).decode().strip()
        unsigned = "<c3b-unsigned@example.invalid>"
        posted = self.post(node, article(unsigned, "unsigned")).decode().strip()
        codes["no-grant-cancel"] = author("nogrant", "<c3b-nogrant@example.invalid>",
                                          "cancel " + unsigned)
        unsigned_reply = self.article_reply(node, unsigned).decode().strip()
        listed = self.listgroup(node, b"fn.test")
        self.stop(node)
        self.start(node)
        restarted = {m: self.article_reply(node, m).decode().strip()
                     for m in (target, late, unsigned)}
        listed_after = self.listgroup(node, b"fn.test")
        # control-c3e: the served withdrawal answers.  The target was the
        # first article of fn.test, number 1.
        by_number = self.session(node, [b"LISTGROUP fn.test\r\n", b"ARTICLE 1\r\n",
                                        b"STAT 1\r\n"])
        withdrawn_numbered = [by_number[2].decode().strip(), by_number[3].decode().strip()]
        withdrawn_msgid = self.article_reply(node, target).decode().strip()
        with socket.create_connection(("127.0.0.1", node["port"]), timeout=30) as client:
            stream = client.makefile("rwb", buffering=0)
            self.assertTrue(stream.readline().startswith(b"200 "))
            stream.write(b"HDR :fn-control <c3b-cancel@example.invalid>\r\n")
            hdr_status = stream.readline().decode().strip()
            hdr_lines = []
            if hdr_status.startswith("225"):
                while True:
                    line = stream.readline()
                    if line in (b".\r\n", b""):
                        break
                    hdr_lines.append(line.decode().rstrip("\r\n"))
        keyring = root / "keyring.json"
        entry = subprocess.run([sys.executable, str(ROOT / "tools" / "fn_verify.py"),
                                "keyring-entry", str(principal), str(ed_public),
                                str(ml_public)], cwd=ROOT, stdout=subprocess.PIPE,
                               check=True, timeout=60)
        keyring.write_text(json.dumps({"format": "fn-verify-keyring-v1",
                                       "principals": [json.loads(entry.stdout)]}))
        verify_cmd = [str(ROOT / "tools" / "fn_verify.py"), target,
                      "--node", "127.0.0.1:" + str(node["port"]), "--plain",
                      "--keyring", str(keyring),
                      "--withdrawal", "<c3b-cancel@example.invalid>", "--json"]
        uv = shutil.which("uv")
        verify_cmd = ([uv, "run", "--with", "cryptography", "--with", "dilithium-py",
                       "python3"] + verify_cmd) if uv else [sys.executable] + verify_cmd
        verified = subprocess.run(verify_cmd, cwd=ROOT, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, timeout=300, check=False)
        self.stop(node)
        witness = {
            "c3e-withdrawn-by-number": withdrawn_numbered,
            "c3e-withdrawn-by-msgid": withdrawn_msgid,
            "c3e-hdr-fn-control": [hdr_status] + hdr_lines,
            "c3e-fn-verify-exit": verified.returncode,
            "c3e-fn-verify-out": verified.stdout.decode("utf-8", "replace")[-2000:],
            "c3e-fn-verify-err": verified.stderr.decode("utf-8", "replace")[-2000:],
            "author-codes": codes, "pinned-before": pinned_before,
            "fresh-after-cancel": fresh, "pinned-after-cancel": pinned_after,
            "cancel-before-target": late_reply, "unsigned-post": posted,
            "no-grant-unsigned-target": unsigned_reply,
            "listgroup-fn.test": [x.decode() if isinstance(x, bytes) else
                                  [y.decode() for y in x] for x in listed],
            "after-restart": restarted,
            "listgroup-fn.test-after-restart": [
                x.decode() if isinstance(x, bytes) else [y.decode() for y in x]
                for x in listed_after],
        }
        print("NATIVE-WITHDRAWAL-WITNESS " + json.dumps(witness, sort_keys=True))
        self.assertTrue(all(code == 0 for code in codes.values()), codes)
        self.assertTrue(pinned_before.startswith("220"), pinned_before)
        self.assertTrue(fresh.startswith("430"), fresh)
        self.assertTrue(late_reply.startswith("430"), late_reply)
        self.assertTrue(posted.startswith("240"), posted)
        self.assertTrue(unsigned_reply.startswith("220"), unsigned_reply)
        self.assertTrue(restarted[target].startswith("430"), restarted)
        self.assertTrue(restarted[late].startswith("430"), restarted)
        self.assertTrue(restarted[unsigned].startswith("220"), restarted)
        self.assertEqual(withdrawn_numbered, ["423 withdrawn", "423 withdrawn"])
        self.assertEqual(withdrawn_msgid, "430 withdrawn")
        self.assertTrue(hdr_status.startswith("225"), hdr_status)
        self.assertEqual(hdr_lines,
                         ["0 executed withdrawal <c3b-target@example.invalid> author"])
        self.assertEqual(verified.returncode, 0, witness)

    @unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                         "set FN_RUN_HYBRID_E2E=1 (OpenSSL 3.5 with ML-DSA-65)")
    def test_two_node_withdrawal(self):
        """C3 across two nodes (control-c3d).  A and B each decide under their
        own enrolment and grants (design section 3, "the receiver decides
        again"): articles authored on one node reach the other over IHAVE,
        relayed by this test (Path prefixed with the peer's name; the carrier
        excludes Path).  P is enrolled on both; Q on both, granted cancel over
        fn.mod.* on B only.  Cases: P's cancel of P's T1 (author basis) on
        both, with a reader on B pinned before it; Q's cancel of an unsigned
        U (authority basis) executes on B and not on A (no grant); P's cancel
        of T2 before T2, with B killed between the two arrivals; Q's grant
        revoked on B and B restarted (the record decided at the cancel's own
        txid stands); P's S superseding T3."""
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        groups = ["fn.test", "fn.mod.a", "control.cancel"]
        a, b = self.initialize("a", groups), self.initialize("b", groups)
        for node in (a, b):
            self.command([IMAGE, "--fn", "operator", node["config"], "peer", "add",
                          "source", "source.example.invalid", "127.0.0.1",
                          str(free_port()), "fn.*", "-", "127.0.0.1", "true"])
            node["control"] = node["root"] / "control.sock"

        def signer(label, principal_byte, ed_public_hex, ed_seed_hex):
            root = self.base / ("signer-" + label)
            root.mkdir()
            keys = {"principal": root / "principal.bin", "ed_public": root / "ed-public.bin",
                    "ed_secret": root / "ed-secret.bin", "ml_private": root / "ml.pem",
                    "ml_public": root / "ml-public.pem", "root": root}
            keys["principal"].write_bytes(bytes([principal_byte]) * 32)
            keys["ed_public"].write_bytes(bytes.fromhex(ed_public_hex))
            keys["ed_secret"].write_bytes(bytes.fromhex(ed_seed_hex + ed_public_hex))
            self.command([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                          keys["ml_private"]])
            self.command([openssl, "pkey", "-in", keys["ml_private"], "-pubout", "-out",
                          keys["ml_public"]])
            keys["generation"] = "1" if label == "p" else "2"
            return keys

        # RFC 8032 section 7.1, TEST 1 and TEST 2.
        p = signer("p", 0x55,
                   "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                   "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
        q = signer("q", 0x66,
                   "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
                   "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb")

        def source(message_id, newsgroups, extra=None):
            lines = ["From: poster@example.invalid", "Newsgroups: " + newsgroups,
                     "Subject: two-node " + message_id,
                     "Date: Fri, 25 Sep 2026 03:00:00 +0000",
                     "Message-ID: " + message_id] + ([extra] if extra else [])
            return ("\r\n".join(lines) + "\r\n\r\nbody\r\n").encode("ascii")

        codes = {}

        def author(node, keys, message_id, newsgroups, extra=None):
            path = keys["root"] / (message_id.strip("<>").replace("@", "_") + ".eml")
            path.write_bytes(source(message_id, newsgroups, extra))
            signed = self.command([IMAGE, "--fn", "hybrid-sign", keys["principal"],
                                   keys["ed_public"], keys["ed_secret"], keys["ml_public"],
                                   keys["ml_private"], path])
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = path.with_suffix(".ed"), path.with_suffix(".ml")
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            done = subprocess.run(
                [str(IMAGE), "--fn", "hybrid-author", str(node["control"]),
                 keys["generation"], str(path),
                 str(ed_sig), str(ml_sig), str(keys["ml_public"])], cwd=ROOT, env=self.env,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180, check=False)
            codes[node["name"] + " " + message_id] = done.returncode

        def fetch(node, message_id):
            with socket.create_connection(("127.0.0.1", node["port"]), timeout=30) as c:
                stream = c.makefile("rwb", buffering=0)
                self.assertTrue(stream.readline().startswith(b"200 "))
                stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
                status = stream.readline()
                self.assertTrue(status.startswith(b"220"), (node["name"], message_id, status))
                lines = []
                while True:
                    line = stream.readline()
                    if line in (b".\r\n", b""):
                        break
                    lines.append(line[1:] if line.startswith(b".") else line)
                return b"".join(lines)

        def relay(origin, destination, message_id):
            octets = fetch(origin, message_id)
            head, _, body = octets.partition(b"\r\n\r\n")
            fields = head.split(b"\r\n")
            rest = [f for f in fields if not f.lower().startswith(b"path:")]
            old = [f for f in fields if f.lower().startswith(b"path:")]
            tail = old[0].split(b":", 1)[1].strip() if old else b"not-for-mail"
            relayed = b"\r\n".join([b"Path: source.example.invalid!" + tail] + rest) \
                + b"\r\n\r\n" + body
            stuffed = b"".join((b"." + line if line.startswith(b".") else line)
                               for line in relayed.splitlines(keepends=True))
            first, second = self.session(destination, [
                b"IHAVE " + message_id.encode() + b"\r\n", stuffed + b".\r\n"])
            codes["relay {}->{} {}".format(origin["name"], destination["name"],
                                            message_id)] = (first + second).decode().strip()

        def reply(node, message_id):
            return self.article_reply(node, message_id).decode().strip()[:3]

        for node in (a, b):
            self.start(node)
            for keys in (p, q):
                self.command([IMAGE, "--fn", "hybrid-enroll", node["control"],
                              keys["generation"], keys["principal"], keys["ed_public"],
                              keys["ml_public"]])
        granted = self.command([IMAGE, "--fn", "operator", b["config"], "control", "grant",
                                "66" * 32, "cancel", "fn.mod.*"])
        witness = {"grant-q-on-b": granted.returncode}

        # 1. Author basis, and a reader on B pinned before the cancel.
        t1, c1 = "<cd-t1@example.invalid>", "<cd-c1@example.invalid>"
        author(a, p, t1, "fn.test")
        relay(a, b, t1)
        with socket.create_connection(("127.0.0.1", b["port"]), timeout=30) as client:
            pinned = client.makefile("rwb", buffering=0)
            self.assertTrue(pinned.readline().startswith(b"200 "))

            def pinned_article(message_id):
                pinned.write(b"ARTICLE " + message_id.encode() + b"\r\n")
                line = pinned.readline()
                if line.startswith(b"220"):
                    while pinned.readline() not in (b".\r\n", b""):
                        pass
                return line.decode().strip()[:3]
            witness["b-pinned-before"] = pinned_article(t1)
            author(a, p, c1, "fn.test", "Control: cancel " + t1)
            relay(a, b, c1)
            witness["a-t1-after-cancel"] = reply(a, t1)
            witness["b-t1-fresh-after-cancel"] = reply(b, t1)
            witness["b-pinned-after"] = pinned_article(t1)

        # 2. Authority basis: Q's cancel of an unsigned U, granted on B only.
        u, cq = "<cd-u@example.invalid>", "<cd-cq@example.invalid>"
        witness["a-post-u"] = self.post(a, source(u, "fn.mod.a")).decode().strip()[:3]
        relay(a, b, u)
        author(b, q, cq, "fn.mod.a", "Control: cancel " + u)
        relay(b, a, cq)
        witness["b-u-authority"] = reply(b, u)
        witness["a-u-no-grant"] = reply(a, u)

        # 3. Cancel before target, B killed between the two arrivals.
        t2, c2 = "<cd-t2@example.invalid>", "<cd-c2@example.invalid>"
        author(a, p, c2, "fn.test", "Control: cancel " + t2)
        relay(a, b, c2)
        b["process"].kill()
        b["process"].communicate(timeout=60)
        self.processes.remove(b.pop("process"))
        self.start(b)
        # A withdraws T2 on arrival, so it cannot serve T2 to relay: the
        # same signed source reaches B through B's own author ingress.
        author(a, p, t2, "fn.test")
        author(b, p, t2, "fn.test")
        witness["a-t2-early-cancel"] = reply(a, t2)
        witness["b-t2-after-kill-and-recovery"] = reply(b, t2)

        # 4. Supersedes: P's S replaces P's T3.
        t3, s3 = "<cd-t3@example.invalid>", "<cd-s3@example.invalid>"
        author(a, p, t3, "fn.test")
        relay(a, b, t3)
        author(a, p, s3, "fn.test", "Supersedes: " + t3)
        relay(a, b, s3)
        witness["a-t3-superseded"], witness["a-s3"] = reply(a, t3), reply(a, s3)
        witness["b-t3-superseded"], witness["b-s3"] = reply(b, t3), reply(b, s3)

        # 5. Revoke Q on B, restart B: the decided record stands.
        revoked = self.command([IMAGE, "--fn", "operator", b["config"], "control", "revoke",
                                "66" * 32, "cancel", "fn.mod.*"])
        witness["revoke-q-on-b"] = revoked.returncode
        self.stop(b)
        self.start(b)
        witness["b-after-revoke-and-restart"] = {
            m: reply(b, m) for m in (t1, u, t2, t3, s3)}
        witness["b-listgroup-fn.mod.a"] = self.listgroup(b, b"fn.mod.a")[0].decode().strip()
        self.stop(b)
        self.stop(a)
        witness["codes"] = codes
        print("NATIVE-TWO-NODE-WITHDRAWAL-WITNESS " + json.dumps(witness, sort_keys=True))
        self.assertTrue(all(v == 0 for k, v in codes.items() if not k.startswith("relay")),
                        codes)
        self.assertTrue(all(v.startswith("335") and "235" in v
                            for k, v in codes.items() if k.startswith("relay")), codes)
        expect = {"b-pinned-before": "220", "a-t1-after-cancel": "430",
                  "b-t1-fresh-after-cancel": "430", "b-pinned-after": "220",
                  "a-post-u": "240", "b-u-authority": "430", "a-u-no-grant": "220",
                  "a-t2-early-cancel": "430", "b-t2-after-kill-and-recovery": "430",
                  "a-t3-superseded": "430", "a-s3": "220", "b-t3-superseded": "430",
                  "b-s3": "220"}
        self.assertEqual({k: witness[k] for k in expect}, expect)
        self.assertEqual(witness["b-after-revoke-and-restart"],
                         {t1: "430", u: "430", t2: "430", t3: "430", s3: "220"})


if __name__ == "__main__":
    unittest.main()
