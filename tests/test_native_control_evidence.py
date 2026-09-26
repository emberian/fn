"""Native witness for `control log` and `control evidence MESSAGE-ID` (PKT-209,
PRF-185, SCN-114).

A signed target and its author's signed cancel go to a running owner; the
owner's refresh decides the withdrawal record (books/control-visible.lisp
fn-ctl-article-withdrawals).  `operator CONFIG control log` then asks the
owner over its control socket (FNLS frame kind 3, books/control-evidence.lisp
fn-cev-request-encode) and prints the record the owner's view carries;
`control evidence` prints the cancel's decision context (stored, txid,
verdict, the decision: the same words as the log's line) and the target's
(withdrawn by that record, on the author basis).  After the owner stops, the
offline command renders the same words over the replayed Store (recovery's
decision, fn-cev-offline-report).

Run: FN_NATIVE_HOST=<launcher> FN_TEST_OPENSSL=<openssl 3.5> python3 -m unittest -v tests.test_native_control_evidence
"""

import os
from pathlib import Path
import re
import unittest

from tests import test_native_control_filing as filing

IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = Path(IMAGE_TEXT) if IMAGE_TEXT else None
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
article = filing.article

TARGET = "<cev-target@example.invalid>"
CANCEL = "<cev-cancel@example.invalid>"


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a native launcher")
class NativeControlEvidenceTests(filing.NativeControlFilingTests):
    """The control-filing harness; only the case below runs here."""

    test_served_post = None
    test_transit_ihave = None
    test_signed_author = None
    test_signed_withdrawal = None
    test_two_node_withdrawal = None

    def operator(self, node, *words, expected=0):
        return self.command([IMAGE, "--fn", "operator", node["config"], *words],
                            expected=expected).stdout.decode("ascii")

    def test_log_and_evidence_live_and_offline(self):
        openssl = os.environ.get("FN_TEST_OPENSSL", "openssl")
        node = self.initialize("evidence", ["fn.test", "control.cancel"])
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
            source.write_bytes(article(message_id, "signed " + stem, control=control_field))
            signed = self.command([IMAGE, "--fn", "hybrid-sign", principal, ed_public,
                                   ed_secret, ml_public, ml_private, source])
            parts = dict(line.split() for line in signed.stdout.decode().splitlines())
            ed_sig, ml_sig = root / (stem + ".ed"), root / (stem + ".ml")
            ed_sig.write_bytes(bytes.fromhex(parts["ed25519"]))
            ml_sig.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
            self.command([IMAGE, "--fn", "hybrid-author", control, "1", source,
                          ed_sig, ml_sig, ml_public])

        self.command([IMAGE, "--fn", "hybrid-enroll", control, "1", principal,
                      ed_public, ml_public])
        author("target", TARGET, None)
        author("cancel", CANCEL, "cancel " + TARGET)
        self.assertTrue(self.article_reply(node, TARGET).startswith(b"430"))

        live_log = self.operator(node, "control", "log")
        live_cancel = self.operator(node, "control", "evidence", CANCEL)
        live_target = self.operator(node, "control", "evidence", TARGET)
        live_absent = self.operator(node, "control", "evidence", "<absent@example.invalid>")
        usage = self.command([IMAGE, "--fn", "operator", node["config"], "control",
                              "evidence", "not-a-message-id"], expected=5)
        self.stop(node)
        offline_log = self.operator(node, "control", "log")
        offline_cancel = self.operator(node, "control", "evidence", CANCEL)
        offline_target = self.operator(node, "control", "evidence", TARGET)
        print("NATIVE-CONTROL-EVIDENCE " + repr({
            "log": live_log, "cancel": live_cancel, "target": live_target,
            "absent": live_absent, "usage": usage.stderr[-400:]}))

        record = re.compile(
            r"^withdrawal target=" + re.escape(TARGET) + " cause=" + re.escape(CANCEL)
            + r" principal=(55){32} scope=- generation=\d+$")
        lines = live_log.splitlines()
        self.assertEqual(lines[0], "withdrawals=1", live_log)
        self.assertRegex(lines[1], record)
        cancel_lines = live_cancel.splitlines()
        self.assertRegex(cancel_lines[0], r"^evidence message-id=" + re.escape(CANCEL)
                         + r" stored=yes txid=\d+ verdict=verified$")
        # The decision's words are "decision=" and the log's line.
        self.assertEqual(cancel_lines[1], "decision=" + lines[1])
        target_lines = live_target.splitlines()
        self.assertRegex(target_lines[0], r"^evidence message-id=" + re.escape(TARGET)
                         + r" stored=yes txid=\d+ verdict=verified$")
        self.assertEqual(target_lines[1], "decision=none")
        self.assertEqual(target_lines[2],
                         "withdrawn-by" + lines[1][len("withdrawal"):] + " effect=author")
        self.assertEqual(live_absent,
                         "evidence message-id=<absent@example.invalid> stored=no\n")
        # Offline (recovery's decision over the replayed Store): the same words.
        self.assertEqual(offline_log, live_log)
        self.assertEqual(offline_cancel, live_cancel)
        self.assertEqual(offline_target, live_target)


if __name__ == "__main__":
    unittest.main()
