"""End to end over the FN-Statement carrier: sign, attach, verify.

Every value these tests compare against is produced by ACL2 through
`tools/stx.py`; the test computes no encoding of its own.  It exercises the
three outcomes and the three exit codes that keep them distinct (D13), and
one negative case per outcome.

The verdict is computed under the TOY crypto realiser
(`tests/acl2/crypto-seam-tests.lisp`), so nothing here is evidence about
unforgeability.  What it is evidence about: the field survives being written
into an article and parsed back, the payload projection subtracts the carrier,
and a rewritten body loses authority without losing bytes.

The served path (POST, then HDR :fn-verified) is NOT exercised: the HDR hook
is a one-line change to `books/nntp-responses.lisp` that this lane does not
make (board CHANGE w7/substrate-s1), so the verdict is read through
`tools/stx.py verify`.  When the hook lands, add the POST/HDR transcript here.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
STX = ROOT / "tools" / "stx.py"
ACL2 = shutil.which(os.environ.get("FN_ACL2", "acl2"))

AUTHORED = (b"From: agent-a@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: hello\r\n"
            b"Message-ID: <a1@example.invalid>\r\n"
            b"\r\n"
            b"body line\r\n")
TAMPERED = AUTHORED.replace(b"body line", b"body lone")
SEED = "07" * 32


def run_stx(args, **kwargs):
    return subprocess.run([sys.executable, str(STX)] + args, cwd=str(ROOT),
                          capture_output=True, timeout=1800, **kwargs)


@unittest.skipUnless(ACL2, "ACL2 is not on PATH; the carrier's owner is ACL2")
class StatementCarrier(unittest.TestCase):
    """One ACL2 session per case: the tool owns the session, not the test."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(os.environ.get("TMPDIR", "/tmp")) / "fn-stx-test"
        cls.tmp.mkdir(parents=True, exist_ok=True)
        (cls.tmp / "seed").write_text(SEED + "\n")
        (cls.tmp / "authored").write_bytes(AUTHORED)
        (cls.tmp / "tampered").write_bytes(TAMPERED)
        signed = run_stx(["sign", "--seed", str(cls.tmp / "seed"),
                          "--payload", str(cls.tmp / "authored")])
        if signed.returncode != 0:
            # `tools/stx.py sign` is the subject of this class, not one of
            # its dependencies.  Until 2026-09-21 a non-zero exit here raised
            # SkipTest, so any defect in the signer turned the whole carrier
            # suite green-by-absence; the only honest skip is the one on the
            # class, which is ACL2 being absent.
            raise AssertionError(
                "tools/stx.py sign exited {}: {}".format(
                    signed.returncode,
                    signed.stderr.decode("utf-8", "replace")[-2000:]))
        cls.field = signed.stdout.rstrip(b"\r\n")
        creator = [line.split()[1] for line in
                   signed.stderr.decode().splitlines() if line.startswith("creator ")]
        cls.creator = creator[0]
        public = "07" * 32   # the toy scheme publishes the seed as the key
        (cls.tmp / "keyring").write_text("{} {}\n".format(cls.creator, public))
        (cls.tmp / "article").write_bytes(cls.field + b"\r\n" + AUTHORED)
        (cls.tmp / "tampered-article").write_bytes(cls.field + b"\r\n" + TAMPERED)

    def test_the_field_is_one_header_line_of_base64(self):
        self.assertTrue(self.field.startswith(b"FN-Statement: "))
        value = self.field[len(b"FN-Statement: "):]
        self.assertTrue(value)
        self.assertNotIn(b"\r", value)
        self.assertNotIn(b"\n", value)
        alphabet = set(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=")
        self.assertTrue(set(value) <= alphabet)

    def test_a_signed_article_verifies_under_the_nodes_keyring(self):
        done = run_stx(["verify", "--article", str(self.tmp / "article"),
                        "--keyring", str(self.tmp / "keyring"), "--generation", "7"])
        self.assertEqual(done.returncode, 0, done.stderr.decode("utf-8", "replace"))
        self.assertIn(b"verified " + self.creator.encode(), done.stdout)
        self.assertIn(b"keyring 7", done.stdout)

    def test_a_rewritten_body_loses_authority_and_not_bytes(self):
        done = run_stx(["verify", "--article", str(self.tmp / "tampered-article"),
                        "--keyring", str(self.tmp / "keyring"), "--generation", "7"])
        self.assertEqual(done.returncode, 3, done.stderr.decode("utf-8", "replace"))
        self.assertIn(b"unverified ref-mismatch", done.stdout)

    def test_an_unknown_creator_is_unverified_not_refused(self):
        done = run_stx(["verify", "--article", str(self.tmp / "article"),
                        "--generation", "7"])
        self.assertEqual(done.returncode, 3, done.stderr.decode("utf-8", "replace"))
        self.assertIn(b"unverified signature", done.stdout)

    def test_no_field_is_absent_and_absent_is_its_own_outcome(self):
        done = run_stx(["verify", "--article", str(self.tmp / "authored"),
                        "--keyring", str(self.tmp / "keyring"), "--generation", "7"])
        self.assertEqual(done.returncode, 4, done.stderr.decode("utf-8", "replace"))
        self.assertIn(b"absent no-field", done.stdout)


if __name__ == "__main__":
    unittest.main()
