#!/usr/bin/env python3
"""tools/fn_verify.py: the node's verdict against an independent check.

Two layers.

`FakeNodeVerifyTests` serves articles from an in-process fake NNTP node.  Its
carriers are signed here with pyca/cryptography (Ed25519) and dilithium-py
(ML-DSA-65) over the preimage this file writes from the specification, so it
tests the verifier's comparison logic and its refusals, and says nothing
about whether fn signs what the specification says.

`NativeVerifyTests` (FN_RUN_VERIFY_E2E=1, FN_NATIVE_HOST, FN_ACL2,
FN_TEST_OPENSSL) runs a scratch owner from a saved image with STARTTLS and a
required login.  FN_VERIFY_LARGE=1 adds a 60 KiB v1 and a 200 KiB v2 signed
POST and a tampered v2 one (the image's article bound must admit them), and
FN_VERIFY_OLD_HOST names an image from before carrier v2 that signs, POSTs
and stores one v1 article in the same Store before the image under test
opens it.  The article is signed by the image's own
`hybrid-sign-carrier` (libsodium and OpenSSL) and POSTed over NNTP; the
verifier checks it with the other libraries.  That is the independent half.
A proxy that holds a real login and rewrites what the node said is the
lying node.
"""
import base64
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import fn_verify  # noqa: E402

TOOL = ROOT / "tools" / "fn_verify.py"

try:
    from cryptography.hazmat.primitives.asymmetric import ed25519
    from dilithium_py.ml_dsa import ML_DSA_65
    HAVE_LIBS = True
except ImportError:
    HAVE_LIBS = False


def dot_stuff(octets):
    return b"".join((b"." + line if line.startswith(b".") else line)
                    for line in octets.splitlines(keepends=True))


def run_verifier(*args, env=None):
    result = subprocess.run([sys.executable, str(TOOL), *map(str, args), "--json"],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=300, env=env, check=False)
    try:
        report = json.loads(result.stdout.decode())
    except ValueError:
        report = {"stdout": result.stdout.decode(), "stderr": result.stderr.decode()}
    return result.returncode, report


class FakeNode:
    """A plain NNTP responder: ARTICLE and HDR :fn-verified from two tables."""

    def __init__(self, articles, verdicts):
        self.articles, self.verdicts = articles, verdicts
        self.listener = socket.socket()
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(8)
        self.port = self.listener.getsockname()[1]
        threading.Thread(target=self.serve, daemon=True).start()

    def serve(self):
        while True:
            try:
                conn, _ = self.listener.accept()
            except OSError:
                return
            threading.Thread(target=self.session, args=(conn,), daemon=True).start()

    def session(self, conn):
        with conn, conn.makefile("rwb", buffering=0) as stream:
            stream.write(b"200 fake node\r\n")
            for raw in stream:
                verb, _, arg = raw.decode().strip().partition(" ")
                if verb == "QUIT":
                    stream.write(b"205 bye\r\n")
                    return
                if verb == "ARTICLE":
                    if arg in self.articles:
                        stream.write(b"220 0 " + arg.encode() + b"\r\n"
                                     + dot_stuff(self.articles[arg]) + b".\r\n")
                    else:
                        stream.write(b"430 no such article\r\n")
                elif verb == "HDR":
                    msgid = arg.split(" ", 1)[1]
                    if msgid in self.verdicts:
                        stream.write(b"225 Headers follow\r\n0 "
                                     + self.verdicts[msgid].encode() + b"\r\n.\r\n")
                    else:
                        stream.write(b"430 no such article\r\n")
                else:
                    stream.write(b"500 what\r\n")

    def close(self):
        self.listener.close()


def fold_carrier(value):
    """fn-hc-field-lines: 72 characters on the first line, tab-folded after."""
    chunks = [value[i:i + 72] for i in range(0, len(value), 72)]
    return b"FN-Authorship: " + chunks[0] + b"\r\n" + b"".join(
        b"\t" + chunk + b"\r\n" for chunk in chunks[1:])


class Signer:
    def __init__(self, principal):
        self.principal = principal
        self.ed = ed25519.Ed25519PrivateKey.generate()
        self.ed_public = self.ed.public_key().public_bytes_raw()
        self.ml_public, self.ml_secret = ML_DSA_65.keygen()

    def entry(self):
        return {"principal": self.principal.hex(), "ed25519": self.ed_public.hex(),
                "ml-dsa-65": self.ml_public.hex(), "generation": 1}

    def carried(self, source, claim_version=None):
        """Sign SOURCE as fn does: v1 (u16 length) up to 65535 octets, v2
        (u32 length, the v2 tag) above.  CLAIM_VERSION overrides only the
        carrier's item 1, after signing."""
        if len(source) <= 65535:
            version, tag, width = 1, b"fn-authored-source-hybrid-v1", 2
        else:
            version, tag, width = 2, b"fn-authored-source-hybrid-v2", 4
        preimage = (b"\x58\x1c" + tag + bytes([version, 1]) + self.principal
                    + bytes([1]) + self.ed_public + bytes([2]) + self.ml_public
                    + len(source).to_bytes(width, "big") + source)
        claimed = version if claim_version is None else claim_version
        items = [bytes([claimed]), bytes([1]), b"\x58\x20" + self.principal, bytes([1]),
                 b"\x58\x20" + self.ed_public, bytes([2]),
                 b"\x59\x07\xa0" + self.ml_public,
                 b"\x58\x40" + self.ed.sign(preimage),
                 b"\x59\x0c\xed" + ML_DSA_65.sign(self.ml_secret, preimage)]
        value = base64.b64encode(b"".join(items))
        return (b"Path: node.example.invalid!not-for-mail\r\n"
                + fold_carrier(value) + source)


def big_body(octets):
    """Numbered 72-octet CRLF lines, at least OCTETS long."""
    lines = [b"line %05d " % i + b"x" * 60 + b"\r\n" for i in range(octets // 72 + 1)]
    return b"".join(lines)


def source_for(msgid, body=b"exact post source\r\n"):
    return (b"From: agent@example.invalid\r\nDate: Wed, 23 Sep 2026 12:00:00 +0000\r\n"
            b"Newsgroups: fn.test\r\nSubject: signed\r\nMessage-ID: "
            + msgid.encode() + b"\r\n\r\n.dot-prefixed line\r\n" + body)


@unittest.skipUnless(HAVE_LIBS, "pip install cryptography dilithium-py")
class FakeNodeVerifyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-verify-")
        root = Path(cls.temp.name)
        cls.author = Signer(bytes([0x55]) * 32)
        cls.stranger = Signer(bytes([0x66]) * 32)
        impostor = Signer(bytes([0x55]) * 32)       # same principal, other keys
        cls.keyring = root / "keyring.json"
        cls.keyring.write_text(json.dumps({"format": "fn-verify-keyring-v1",
                                           "principals": [cls.author.entry()]}))
        good = cls.author.carried(source_for("<good@x.invalid>"))
        tampered = cls.author.carried(source_for("<tampered@x.invalid>")).replace(
            b"exact post source", b"Exact post source")
        other = cls.author.carried(source_for("<other@x.invalid>"))
        a, p = "verified " + "55" * 32 + " keyring 1", "55" * 32
        cls.node = FakeNode(
            articles={
                "<good@x.invalid>": good,
                "<lie-verified@x.invalid>": tampered.replace(b"<tampered@", b"<lie-verified@"),
                "<tampered@x.invalid>": tampered,
                "<unsigned@x.invalid>": source_for("<unsigned@x.invalid>"),
                "<lie-absent@x.invalid>": cls.author.carried(source_for("<lie-absent@x.invalid>")),
                "<wrong-principal@x.invalid>": cls.author.carried(source_for("<wrong-principal@x.invalid>")),
                "<swapped@x.invalid>": other,
                "<unpinned@x.invalid>": cls.stranger.carried(source_for("<unpinned@x.invalid>")),
                "<impostor@x.invalid>": impostor.carried(source_for("<impostor@x.invalid>")),
                "<no-hdr@x.invalid>": good,
                "<garbled@x.invalid>": good,
                "<carried@x.invalid>": cls.author.carried(source_for("<carried@x.invalid>")),
                "<carried-unpinned@x.invalid>": cls.stranger.carried(
                    source_for("<carried-unpinned@x.invalid>")),
                "<v1-60k@x.invalid>": cls.author.carried(
                    source_for("<v1-60k@x.invalid>", body=big_body(60 * 1024))),
                "<v2-200k@x.invalid>": cls.author.carried(
                    source_for("<v2-200k@x.invalid>", body=big_body(200 * 1024))),
                "<v2-tampered@x.invalid>": cls.author.carried(
                    source_for("<v2-tampered@x.invalid>", body=big_body(200 * 1024))
                ).replace(b"line 00100 ", b"LINE 00100 "),
                "<v2-says-v1@x.invalid>": cls.author.carried(
                    source_for("<v2-says-v1@x.invalid>", body=big_body(200 * 1024)),
                    claim_version=1),
                "<v1-says-v2@x.invalid>": cls.author.carried(
                    source_for("<v1-says-v2@x.invalid>"), claim_version=2),
            },
            verdicts={
                "<good@x.invalid>": a,
                "<lie-verified@x.invalid>": a,
                "<tampered@x.invalid>": "unverified signature keyring 1",
                "<unsigned@x.invalid>": "absent no-record",
                "<lie-absent@x.invalid>": "absent no-record",
                "<wrong-principal@x.invalid>": "verified " + "77" * 32 + " keyring 1",
                "<swapped@x.invalid>": a,
                "<unpinned@x.invalid>": "verified " + "66" * 32 + " keyring 1",
                "<impostor@x.invalid>": a,
                "<garbled@x.invalid>": "maybe",
                "<carried@x.invalid>": "carried " + "55" * 32,
                "<carried-unpinned@x.invalid>": "carried " + "66" * 32,
                "<v1-60k@x.invalid>": a,
                "<v2-200k@x.invalid>": a,
                "<v2-tampered@x.invalid>": "unverified signature keyring 1",
                "<v2-says-v1@x.invalid>": "unverified carrier keyring 1",
                "<v1-says-v2@x.invalid>": a,
            })
        cls.principal = p

    @classmethod
    def tearDownClass(cls):
        cls.node.close()
        cls.temp.cleanup()

    def verify(self, msgid):
        return run_verifier(msgid, "--node", "127.0.0.1:{}".format(self.node.port),
                            "--plain", "--keyring", self.keyring)

    def test_agreement_on_a_valid_signature_is_0(self):
        code, report = self.verify("<good@x.invalid>")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["independent"]["principal"], self.principal)
        used = report["independent"]["implementations"]
        self.assertIn("pyca/cryptography Ed25519", used)
        self.assertIn("dilithium-py ML-DSA-65 (pure Python FIPS 204)", used)

    def test_agreement_that_a_tampered_or_unsigned_article_is_unverified_is_1(self):
        code, report = self.verify("<tampered@x.invalid>")
        self.assertEqual((code, report["independent"]["reason"]), (1, "signature"), report)
        code, report = self.verify("<unsigned@x.invalid>")
        self.assertEqual((code, report["independent"]["reason"]), (1, "no-carrier"), report)

    def test_a_lying_node_is_2(self):
        for msgid, reason in (("<lie-verified@x.invalid>", "signature"),
                              ("<lie-absent@x.invalid>", None),
                              ("<wrong-principal@x.invalid>", None),
                              ("<swapped@x.invalid>", "message-id"),
                              ("<impostor@x.invalid>", "key-not-pinned")):
            code, report = self.verify(msgid)
            self.assertEqual(code, 2, (msgid, report))
            if reason:
                self.assertEqual(report["independent"]["reason"], reason, msgid)

    def test_what_cannot_be_decided_is_3(self):
        for msgid in ("<unpinned@x.invalid>", "<absent@x.invalid>",
                      "<no-hdr@x.invalid>", "<garbled@x.invalid>"):
            code, report = self.verify(msgid)
            self.assertEqual(code, 3, (msgid, report))
        code, _ = run_verifier("<good@x.invalid>", "--node", "127.0.0.1:1", "--plain",
                               "--keyring", self.keyring)
        self.assertEqual(code, 3)

    def test_a_carried_article_is_undecided_3_never_0_or_1(self):
        # D23: a relay that carries without an enrollment says `carried P'.
        # Even when the signature verifies under the pinned keys, the node
        # claimed nothing, so the tool neither agrees nor disagrees.
        for msgid, check in (("<carried@x.invalid>", "verified"),
                             ("<carried-unpinned@x.invalid>", None)):
            code, report = self.verify(msgid)
            self.assertEqual(code, 3, (msgid, report))
            self.assertIn("carried this article", report["detail"])
            self.assertEqual(report["node"]["outcome"], "carried")
            if check:
                self.assertEqual(report["independent"]["outcome"], check)

    def test_carrier_v1_now_carries_up_to_65535_octets(self):
        # Bounds P4 step one: 60 KiB was over the old 32768 bound; the u16
        # already carried it, so it is a v1 carrier and verifies.
        code, report = self.verify("<v1-60k@x.invalid>")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["independent"]["carrier-version"], 1)
        self.assertGreater(report["independent"]["source-octets"], 32768)

    def test_carrier_v2_valid_is_0(self):
        code, report = self.verify("<v2-200k@x.invalid>")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["independent"]["carrier-version"], 2)
        self.assertGreater(report["independent"]["source-octets"], 65535)

    def test_carrier_v2_tampered_is_1(self):
        code, report = self.verify("<v2-tampered@x.invalid>")
        self.assertEqual((code, report["independent"]["reason"]), (1, "signature"), report)
        self.assertEqual(report["independent"]["carrier-version"], 2)

    def test_carrier_wrong_version_byte_is_refused(self):
        # A v2 signature whose item 1 says 1: the source is too long for v1.
        code, report = self.verify("<v2-says-v1@x.invalid>")
        self.assertEqual((code, report["independent"]["reason"]), (1, "carrier"), report)
        # A v1 signature whose item 1 says 2, under a node that claims
        # verified: the carrier is not fn's, so the node is contradicted.
        code, report = self.verify("<v1-says-v2@x.invalid>")
        self.assertEqual((code, report["independent"]["reason"]), (2, "carrier"), report)

    def test_the_versions_sign_disjoint_preimages(self):
        source = source_for("<disjoint@x.invalid>")
        v1 = fn_verify.signed_preimage(1, b"p" * 32, b"e" * 32, b"m" * 1952, source)
        v2 = fn_verify.signed_preimage(2, b"p" * 32, b"e" * 32, b"m" * 1952, source)
        self.assertEqual(v1[:29], v2[:29])
        self.assertNotEqual(v1[29], v2[29])
        self.assertEqual(len(v2) - len(v1), 2)

    def test_usage_error_never_reads_as_disagreement(self):
        code, _ = run_verifier("not-a-msgid", "--node", "x", "--plain",
                               "--keyring", self.keyring)
        self.assertEqual(code, fn_verify.EXIT_USAGE)

    def test_noncanonical_carrier_is_refused(self):
        with self.assertRaises(ValueError):
            fn_verify.decode_carrier(b"\x18\x01" + bytes(10))


# ---------------------------------------------------------------- spec tie

SPEC = ROOT / "specs" / "identity.md"
SECTION = "## The signed bytes"
# The book constants whose values the spec section, the verifier and the
# books must agree on, with the verifier's restatement of each.
WIDTHS = {
    "*fn-hsig-ed25519-public-key-octets*": fn_verify.ED_PK,
    "*fn-hsig-ed25519-signature-octets*": fn_verify.ED_SIG,
    "*fn-hsig-ml-dsa-65-public-key-octets*": fn_verify.ML_PK,
    "*fn-hsig-ml-dsa-65-signature-octets*": fn_verify.ML_SIG,
    "*fn-hsig-v1-max-source*": fn_verify.SOURCE_MAX_V1,
    "*fn-hsig-v2-max-source*": fn_verify.SOURCE_MAX_V2,
    "*fn-hsig-version*": 1,
    "*fn-hsig-v2-version*": 2,
    "*fn-hc-max-field-octets*": fn_verify.CARRIER_FIELD_MAX,
    "*fn-hc-max-binary-octets*": fn_verify.CARRIER_BINARY_MAX,
}
DROPPED = ("*fn-hc-name*", "*fn-hc-path-name*", "*fn-hc-xref-name*",
           "*fn-hc-injection-date-name*", "*fn-hc-injection-info-name*")


def spec_section(text):
    start = text.index(SECTION)
    end = text.find("\n## ", start + len(SECTION))
    return text[start:] if end < 0 else text[start:end]


def book_forms():
    """Every name a book defines, and each defconst's value text."""
    names, consts = set(), {}
    form = re.compile(r"^\((defun|defund|defthm|defconst|defmacro)\s+(\S+)\s*(.*)$")
    for path in sorted((ROOT / "books").glob("*.lisp")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            m = form.match(line)
            if not m:
                continue
            names.add(m.group(2))
            if m.group(1) == "defconst":
                consts[m.group(2)] = " ".join([m.group(3)] + lines[i + 1:i + 3])
    return names, consts


def const_value(consts, name):
    text = consts[name].split(";")[0]
    if text.lstrip().startswith("'("):
        body = text[text.index("(") + 1:text.index(")")]
        return bytes(int(n) for n in body.split())
    return int(re.match(r"\s*(\d+)", text).group(1))


def spec_book_problems(section, names, consts):
    """What the section says that the books or the verifier do not."""
    problems = []
    cited = set(re.findall(r"`(\*?fn-[a-z0-9-]+\*?)`", section))
    cited.discard(fn_verify.DOMAIN_TAG.decode("ascii"))  # a string, not a name
    cited.discard(fn_verify.DOMAIN_TAG_V2.decode("ascii"))
    cited -= {"fn-hybrid-v1", "fn-hybrid-v2"}             # evidence tags, likewise
    for name in sorted(cited - names):
        problems.append("the spec cites `{}`, which no book defines".format(name))
    for name, restated in (("*fn-hsig-domain-tag*", fn_verify.DOMAIN_TAG),
                           ("*fn-hsig-v2-domain-tag*", fn_verify.DOMAIN_TAG_V2)):
        tag = const_value(consts, name)
        if tag != restated or fn_verify.VERSIONS[
                1 if name == "*fn-hsig-domain-tag*" else 2][0] != tag:
            problems.append("the book's {} is not the verifier's".format(name))
        if tag.decode("ascii") not in section:
            problems.append("the spec does not state {}".format(name))
    for name, restated in (("*fn-hsig-profile-tag*", b"fn-hybrid-v1"),
                           ("*fn-stxe-profile-hybrid-v2*", b"fn-hybrid-v2")):
        if const_value(consts, name) != restated:
            problems.append("the book's {} is not {}".format(name, restated))
        if restated.decode("ascii") not in section:
            problems.append("the spec does not state the evidence tag {}".format(
                restated.decode("ascii")))
    for name, restated in WIDTHS.items():
        value = const_value(consts, name)
        if value != restated:
            problems.append("{} is {} in the book, {} in the verifier".format(
                name, value, restated))
        if not re.search(r"(?<![\d-]){}(?!\d)".format(value), section):
            problems.append("the spec does not state {} ({})".format(name, value))
    dropped = {const_value(consts, name) for name in DROPPED}
    if dropped != fn_verify.RELAY_FIELDS:
        problems.append("the book drops {}, the verifier {}".format(
            sorted(dropped), sorted(fn_verify.RELAY_FIELDS)))
    step = re.search(r"(?ms)^3\. Every physical line.*?(?=^\d\. )", section)
    stated = {m.lower().encode() for m in
              re.findall(r"`([A-Z][A-Za-z-]*)`", step.group(0))} if step else set()
    if stated != dropped:
        problems.append("the spec drops {}, the book {}".format(
            sorted(stated), sorted(dropped)))
    return problems


class SpecBookTieTests(unittest.TestCase):
    """specs/identity.md "The signed bytes" against the books and the verifier.

    Needs no ACL2 and no crypto library; `make check` runs it.  It checks
    names, tag bytes, widths and the dropped fields, not the layouts."""

    def setUp(self):
        self.section = spec_section(SPEC.read_text(encoding="utf-8"))
        self.names, self.consts = book_forms()

    def test_the_spec_the_books_and_the_verifier_agree(self):
        self.assertEqual(spec_book_problems(self.section, self.names, self.consts), [])

    def test_a_renamed_function_is_caught(self):
        drifted = self.section.replace("`fn-hc-authored-source`",
                                       "`fn-hc-authored-source-v0`")
        self.assertIn("the spec cites `fn-hc-authored-source-v0`, which no book defines",
                      spec_book_problems(drifted, self.names, self.consts))

    def test_a_changed_width_is_caught(self):
        consts = dict(self.consts)
        consts["*fn-hsig-ml-dsa-65-signature-octets*"] = "3293)"
        problems = spec_book_problems(self.section, self.names, consts)
        self.assertTrue(any("3293 in the book" in p for p in problems), problems)

    def test_a_changed_v2_tag_or_width_is_caught(self):
        consts = dict(self.consts)
        consts["*fn-hsig-v2-domain-tag*"] = consts["*fn-hsig-domain-tag*"]
        consts["*fn-hsig-v2-max-source*"] = "65535)"
        problems = " ".join(spec_book_problems(self.section, self.names, consts))
        self.assertIn("*fn-hsig-v2-domain-tag* is not the verifier's", problems)
        self.assertIn("65535 in the book, 4294967295 in the verifier", problems)
        drifted = self.section.replace("fn-authored-source-hybrid-v2", "fn-v2")
        self.assertIn("the spec does not state *fn-hsig-v2-domain-tag*", " ".join(
            spec_book_problems(drifted, self.names, self.consts)))

    def test_a_field_the_spec_forgets_to_drop_is_caught(self):
        drifted = self.section.replace("`Xref`,", "")
        self.assertIn("xref", " ".join(
            spec_book_problems(drifted, self.names, self.consts)))


# ---------------------------------------------------------------- native

IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host-developer"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
# `fn principal set-password` derives the verifier in ACL2 over
# books/auth-secret, so it runs from a tree whose certificates exist (a
# gate tree, read-only); by default this one.
AUTH_TREE = Path(os.environ.get("FN_VERIFY_AUTH_TREE", ROOT))
OLD_IMAGE = os.environ.get("FN_VERIFY_OLD_HOST")
LARGE = os.environ.get("FN_VERIFY_LARGE") == "1"


class LyingProxy:
    """A node that holds a real login upstream and rewrites what it says."""

    def __init__(self, upstream, rewrite_article=None, rewrite_hdr=None):
        self.upstream = upstream
        self.rewrite_article = rewrite_article or (lambda b: b)
        self.rewrite_hdr = rewrite_hdr or (lambda b: b)
        self.listener = socket.socket()
        self.listener.bind(("127.0.0.1", 0))
        self.listener.listen(4)
        self.port = self.listener.getsockname()[1]
        threading.Thread(target=self.serve, daemon=True).start()

    def serve(self):
        while True:
            try:
                conn, _ = self.listener.accept()
            except OSError:
                return
            threading.Thread(target=self.session, args=(conn,), daemon=True).start()

    def session(self, conn):
        node = self.upstream()
        with conn, conn.makefile("rwb", buffering=0) as stream:
            stream.write(b"200 proxy\r\n")
            for raw in stream:
                command = raw.decode().strip()
                if command == "QUIT":
                    stream.write(b"205 bye\r\n")
                    break
                status = node.command(command)
                if status.startswith(("220", "225")):
                    data = node.multiline()
                    data = (self.rewrite_article if status.startswith("220")
                            else self.rewrite_hdr)(data)
                    stream.write(status.encode() + b"\r\n" + dot_stuff(data) + b".\r\n")
                else:
                    stream.write(status.encode() + b"\r\n")
        node.close()

    def close(self):
        self.listener.close()


@unittest.skipUnless(os.environ.get("FN_RUN_VERIFY_E2E") == "1",
                     "set FN_RUN_VERIFY_E2E=1, FN_NATIVE_HOST, FN_ACL2, FN_TEST_OPENSSL")
@unittest.skipUnless(HAVE_LIBS, "pip install cryptography dilithium-py")
class NativeVerifyTests(unittest.TestCase):
    USER, PASSWORD = "verify-reader", "correct-horse-verify"

    @classmethod
    def invoke(cls, *args, timeout=180, image=IMAGE):
        result = subprocess.run([str(image), "--fn", *map(str, args)], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
        if result.returncode != 0:
            raise AssertionError("{} -> {}: {}".format(args[:2], result.returncode,
                                                       result.stderr.decode()[-2000:]))
        return result

    @classmethod
    def setUpClass(cls):
        from tests.native_process import stop_and_diagnostics, wait_for_announcement
        cls.temp = tempfile.TemporaryDirectory(prefix="fn-verify-native-")
        root = cls.root = Path(cls.temp.name)
        store, control, auth = root / "store", root / "control.sock", root / "auth.toml"
        cls.cert, key = root / "node-cert.pem", root / "node-key.pem"
        subprocess.run([OPENSSL, "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
                        "-out", str(cls.cert), "-sha256", "-days", "1", "-nodes",
                        "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=60, check=True)
        with socket.socket() as probe:
            probe.bind(("127.0.0.1", 0))
            cls.port = probe.getsockname()[1]
        cls.config = root / "fn.toml"
        cls.config.write_text(
            '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
            'tls_cert = "{}"\ntls_key = "{}"\n[control]\npath = "{}"\n'
            '[auth]\nrequired = true\nprotected_only = true\npath = "{}"\n'
            .format(store, cls.port, cls.cert, key, control, auth), encoding="ascii")
        # D27: the store's profile is the operator's.  FN_VERIFY_INIT_FLAGS
        # (e.g. "--max-article-octets 4194304") gives the large cases an
        # article bound that admits them.  `operator CFG init` is the verb
        # that reads profile fields; the developer `store ROOT init` takes
        # every word as a group name, so it made groups named
        # "--max-article-octets" and "4194304" and kept the 32,768 default.
        cls.invoke("operator", cls.config, "init",
                   *os.environ.get("FN_VERIFY_INIT_FLAGS", "").split(), "fn.test")
        # The store profile's article field, as `status' reports it (the
        # operator's default profile when no flag was given).  Read before
        # the owner holds the store lock.
        status = cls.invoke("operator", cls.config, "status").stdout.decode()
        cls.article_bound = int(re.search(r"max-article-octets=(\d+)", status).group(1))
        env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        env.pop("FN_HOST", None)
        enrolled = subprocess.run(
            [sys.executable, str(AUTH_TREE / "bin" / "fn"), "--config", str(cls.config), "principal",
             "set-password", cls.USER, "--password", cls.PASSWORD, "--posting"],
            cwd=AUTH_TREE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env,
            timeout=900, check=False)
        assert enrolled.returncode == 0, enrolled.stderr.decode()
        cls.creds = root / "creds"
        cls.creds.write_text("{} {}\n".format(cls.USER, cls.PASSWORD))
        os.chmod(cls.creds, 0o600)

        cls.principal = root / "principal.bin"
        cls.principal.write_bytes(bytes([0x55]) * 32)
        cls.ed_public, cls.ed_secret = root / "ed-public.bin", root / "ed-secret.bin"
        cls.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        cls.ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        cls.ml_private, cls.ml_public = root / "ml-private.pem", root / "ml-public.pem"
        subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                        str(cls.ml_private)], timeout=60, check=True)
        subprocess.run([OPENSSL, "pkey", "-in", str(cls.ml_private), "-pubout",
                        "-out", str(cls.ml_public)], timeout=60, check=True)
        entry = subprocess.run([sys.executable, str(TOOL), "keyring-entry", cls.principal,
                                cls.ed_public, cls.ml_public, "--generation", "1"],
                               stdout=subprocess.PIPE, timeout=60, check=True)
        cls.keyring = root / "keyring.json"
        cls.keyring.write_text(json.dumps({"format": "fn-verify-keyring-v1",
                                           "principals": [json.loads(entry.stdout)]}))

        cls.replies = {}
        if OLD_IMAGE:
            # A v1 record written by an image from before carrier v2.
            old = subprocess.Popen([OLD_IMAGE, "--fn", "operator", str(cls.config), "run"],
                                   cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                line = wait_for_announcement(old, b"LISTENING ")
                assert line.startswith(b"LISTENING "), line
                cls.invoke("hybrid-enroll", control, "1", cls.principal, cls.ed_public,
                           cls.ml_public, image=OLD_IMAGE)
                cls.replies["verify-old-v1"] = cls.post(
                    cls.sign("verify-old-v1", source_for("<verify-old-v1@example.invalid>"),
                             image=OLD_IMAGE))
            finally:
                stop_and_diagnostics(old, timeout=60)

        cls.owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(cls.config), "run"],
                                     cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            cls.start(control)
        except BaseException:
            # tearDownClass does not run after a failed setUpClass.  The
            # owner's stderr is the only record of why a POST got no reply.
            print("owner stderr:\n" + stop_and_diagnostics(cls.owner, timeout=60),
                  flush=True)
            cls.temp.cleanup()
            raise

    @classmethod
    def start(cls, control):
        from tests.native_process import wait_for_announcement
        line = wait_for_announcement(cls.owner, b"LISTENING ")
        assert line.startswith(b"LISTENING "), line
        if not OLD_IMAGE:
            cls.invoke("hybrid-enroll", control, "1", cls.principal, cls.ed_public,
                       cls.ml_public)

        cases = [("verify-signed", False, True, b"exact post source\r\n"),
                 ("verify-tampered", True, True, b"exact post source\r\n"),
                 ("verify-unsigned", False, False, b"exact post source\r\n")]
        if LARGE:
            cases += [("verify-unsigned-200k", False, False, big_body(200 * 1024)),
                      ("verify-v1-60k", False, True, big_body(60 * 1024)),
                      ("verify-v2-200k", False, True, big_body(200 * 1024)),
                      ("verify-v2-tampered", True, True, big_body(200 * 1024))]
        for stem, tamper, signed, body in cases:
            source = source_for("<{}@example.invalid>".format(stem), body=body)
            octets = cls.sign(stem, source) if signed else source
            if tamper:
                octets = octets.replace(b"exact post source", b"Exact post source", 1)
                octets = octets.replace(b"line 00100 ", b"LINE 00100 ", 1)
            print("POST", stem, len(octets), flush=True)
            cls.replies[stem] = cls.post(octets)
            print("  ->", cls.replies[stem][:80], flush=True)

    @classmethod
    def sign(cls, stem, source_octets, image=IMAGE):
        source, carried = cls.root / (stem + ".eml"), cls.root / (stem + "-carried.eml")
        source.write_bytes(source_octets)
        cls.invoke("hybrid-sign-carrier", cls.principal, cls.ed_public, cls.ed_secret,
                   cls.ml_public, cls.ml_private, source, carried, image=image)
        return carried.read_bytes()

    @classmethod
    def upstream(cls, timeout=30.0):
        return fn_verify.Node("127.0.0.1", cls.port, cafile=str(cls.cert),
                              credentials=(cls.USER, cls.PASSWORD), timeout=timeout)

    @classmethod
    def post(cls, octets):
        # A large POST's reply waits on the node reading the whole article;
        # the wait is printed, and bounded well above it.
        node = cls.upstream(timeout=600.0)
        started = time.monotonic()
        try:
            status = node.command("POST")
            assert status.startswith("340"), status
            node.sock.sendall(dot_stuff(octets) + b".\r\n")
            return node.line()
        finally:
            print("  POST wall {:.2f} s".format(time.monotonic() - started), flush=True)
            node.close()

    @classmethod
    def tearDownClass(cls):
        from tests.native_process import stop_and_diagnostics
        stop_and_diagnostics(cls.owner, timeout=60)
        cls.temp.cleanup()

    def verify(self, msgid, port=None):
        if port is None:
            return run_verifier(msgid, "--node", "127.0.0.1:{}".format(self.port),
                                "--cafile", self.cert, "--credentials", self.creds,
                                "--keyring", self.keyring)
        return run_verifier(msgid, "--node", "127.0.0.1:{}".format(port), "--plain",
                            "--keyring", self.keyring)

    def test_the_node_accepted_the_signed_and_unsigned_posts_and_refused_the_tampered(self):
        self.assertTrue(self.replies["verify-signed"].startswith("240"), self.replies)
        self.assertTrue(self.replies["verify-unsigned"].startswith("240"), self.replies)
        self.assertEqual(self.replies["verify-tampered"],
                         "441 posting failed; the author signature does not verify")

    def test_signed_post_verifies_independently_0(self):
        code, report = self.verify("<verify-signed@example.invalid>")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["node"]["principal"], "55" * 32)
        self.assertIn("> AUTHINFO PASS ****", report["transcript"])
        print("\nsigned:", json.dumps({k: report[k] for k in ("node-hdr", "detail")}))
        print("implementations:", report["independent"]["implementations"])

    def test_unsigned_post_both_say_unverified_1(self):
        code, report = self.verify("<verify-unsigned@example.invalid>")
        self.assertEqual(code, 1, report)
        self.assertEqual(report["node"]["outcome"], "absent")
        print("\nunsigned:", report["node-hdr"], "|", report["detail"])

    def test_an_article_past_the_profile_over_tls_is_a_441_and_the_owner_serves_on(self):
        # large-article, 2026-09-25: on a protected channel an article past
        # the profile's bound closes the wire mid-article (fn-wire-close ...
        # :body-overlimit, books/wire.lisp), so the step consumes a prefix of
        # the read.  The host faulted on that suffix ("protected owner read
        # left a TLS suffix") and stopped the process: the client saw a
        # closed socket, and so did every later client.  A refusal is a 441
        # naming its reason, and the listener stays.
        bound = self.article_bound
        body = big_body(bound + 1)
        octets = source_for("<verify-past-bound@example.invalid>", body=body)
        self.assertGreater(len(octets), bound)
        node = self.upstream()
        try:
            self.assertTrue(node.command("POST").startswith("340"))
            try:
                node.sock.sendall(dot_stuff(octets) + b".\r\n")
            except OSError:
                pass  # the refusal arrived while the body was still going out
            answer = node.line()
        finally:
            node.close()
        self.assertEqual(answer, "441 posting failed; the article exceeds the configured size")
        self.assertIsNone(self.owner.poll(), "the owner stopped on a refusal")
        again = self.upstream()
        try:
            self.assertTrue(again.command("DATE").startswith("111"))
        finally:
            again.close()

    def test_tampered_post_is_not_stored_so_nothing_is_decided_3(self):
        code, report = self.verify("<verify-tampered@example.invalid>")
        self.assertEqual(code, 3, report)
        self.assertIn("holds no article", report["detail"])

    def test_tampered_bytes_under_the_nodes_verified_line_are_2(self):
        proxy = LyingProxy(self.upstream, rewrite_article=lambda b: b.replace(
            b"exact post source", b"Exact post source"))
        try:
            code, report = self.verify("<verify-signed@example.invalid>", proxy.port)
        finally:
            proxy.close()
        self.assertEqual((code, report["independent"]["reason"]), (2, "signature"), report)
        print("\ntampered-in-flight:", report["node-hdr"], "|", report["detail"])

    @unittest.skipUnless(LARGE, "set FN_VERIFY_LARGE=1 on an image whose article bound admits 200 KiB")
    def test_large_signed_posts_verify_under_their_version_0(self):
        for stem, version, low in (("verify-v1-60k", 1, 32768), ("verify-v2-200k", 2, 65535)):
            self.assertTrue(self.replies[stem].startswith("240"), (stem, self.replies[stem]))
            code, report = self.verify("<{}@example.invalid>".format(stem))
            self.assertEqual(code, 0, report)
            self.assertEqual(report["node"]["outcome"], "verified", report)
            self.assertEqual(report["independent"]["carrier-version"], version)
            self.assertGreater(report["independent"]["source-octets"], low)
            print("\n{}: {} | source-octets {} carrier-version {}".format(
                stem, report["node-hdr"], report["independent"]["source-octets"], version))

    @unittest.skipUnless(LARGE, "set FN_VERIFY_LARGE=1 on an image whose article bound admits 200 KiB")
    def test_tampered_v2_post_is_refused_and_not_stored_3(self):
        self.assertEqual(self.replies["verify-v2-tampered"],
                         "441 posting failed; the author signature does not verify")
        code, report = self.verify("<verify-v2-tampered@example.invalid>")
        self.assertEqual(code, 3, report)

    @unittest.skipUnless(OLD_IMAGE, "set FN_VERIFY_OLD_HOST to an image from before carrier v2")
    def test_a_v1_record_from_before_v2_is_still_verified_0(self):
        self.assertTrue(self.replies["verify-old-v1"].startswith("240"), self.replies)
        code, report = self.verify("<verify-old-v1@example.invalid>")
        self.assertEqual(code, 0, report)
        self.assertEqual(report["node"]["outcome"], "verified", report)
        self.assertEqual(report["independent"]["carrier-version"], 1)
        print("\nold v1 record:", report["node-hdr"])

    def test_fabricated_hdr_answers_are_2(self):
        forged = b"0 verified " + b"55" * 32 + b" keyring 1\r\n"
        proxy = LyingProxy(self.upstream, rewrite_hdr=lambda b: forged)
        try:
            code, report = self.verify("<verify-unsigned@example.invalid>", proxy.port)
        finally:
            proxy.close()
        self.assertEqual(code, 2, report)
        print("\nforged verified:", report["node-hdr"], "|", report["detail"])
        proxy = LyingProxy(self.upstream, rewrite_hdr=lambda b: b"0 absent no-record\r\n")
        try:
            code, report = self.verify("<verify-signed@example.invalid>", proxy.port)
        finally:
            proxy.close()
        self.assertEqual(code, 2, report)
        print("forged absent:", report["node-hdr"], "|", report["detail"])


if __name__ == "__main__":
    unittest.main()
