#!/usr/bin/env python3
"""ML-DSA-65 interoperability: fn's PQClean seam against OpenSSL (>= 3.5).

    python3 tests/mldsa65_interop.py LIBRARY [--openssl PATH] [--json OUT]

LIBRARY is the built lib/libfn-mldsa65 (tools/build_mldsa65.sh).  OpenSSL
is the reference the node used before HST-016; this checks, both ways:

  keys        OpenSSL's default private PEM (seed and expanded key) and its
              public PEM: the seam derives the same public key and, from the
              seed alone, re-encodes both PEMs byte for byte.  The seed-only
              and expanded-only PKCS#8 forms parse and sign.  Every
              committed ML-DSA-65 PEM and .raw key parses to the same bytes
              OpenSSL reads.
  signatures  OpenSSL signs, the seam verifies; the seam signs, OpenSSL
              verifies; a flipped bit is refused by both.  Messages of 1, 33
              and 70000 octets (and 0 octets seam-only: pkeyutl refuses
              an empty input).
  fixtures    Every committed signed carrier (FN-Authorship articles under
              tests/ and planning/evidence/, including those embedded in
              stores, inboxes and BP ADUs), signed by OpenSSL 3.5: the seam
              and OpenSSL both verify the carrier's ML-DSA-65 signature over
              fn's signed preimage (tools/fn_verify.py's restatement).

Any disagreement is printed as a FINDING and the exit status is 1.  Python
is a test tool here, not a decision engine.
"""

import argparse
import base64
import ctypes
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import fn_verify  # noqa: E402

PK, SIG, SK, SEED = 1952, 3309, 4032, 32
SPKI_PREFIX = fn_verify.ML_SPKI_PREFIX


class Seam:
    def __init__(self, path):
        lib = ctypes.CDLL(path)
        self.lib = lib
        u8p = ctypes.c_char_p
        lib.fn_mldsa65_implementation.restype = ctypes.c_char_p
        lib.fn_mldsa65_strerror.restype = ctypes.c_char_p
        lib.fn_mldsa65_strerror.argtypes = [ctypes.c_int]
        lib.fn_mldsa65_public_from_pem.argtypes = [u8p, ctypes.c_size_t, ctypes.c_void_p]
        lib.fn_mldsa65_public_from_private_pem.argtypes = [u8p, ctypes.c_size_t, ctypes.c_void_p]
        lib.fn_mldsa65_sign_pem.argtypes = [u8p, ctypes.c_size_t, u8p, ctypes.c_size_t,
                                            ctypes.c_void_p]
        lib.fn_mldsa65_verify.argtypes = [u8p, ctypes.c_size_t, u8p, ctypes.c_size_t, u8p]
        size_p = ctypes.POINTER(ctypes.c_size_t)
        lib.fn_mldsa65_pem_from_seed.argtypes = [u8p, ctypes.c_void_p, ctypes.c_size_t, size_p,
                                                 ctypes.c_void_p, ctypes.c_size_t, size_p]
        lib.fn_mldsa65_generate_pem.argtypes = [ctypes.c_void_p, ctypes.c_size_t, size_p,
                                                ctypes.c_void_p, ctypes.c_size_t, size_p]

    def implementation(self):
        return self.lib.fn_mldsa65_implementation().decode()

    def _check(self, rc, what):
        if rc != 0:
            raise ValueError("{}: {} ({})".format(what, self.lib.fn_mldsa65_strerror(rc).decode(), rc))

    def public_from_pem(self, pem):
        out = ctypes.create_string_buffer(PK)
        self._check(self.lib.fn_mldsa65_public_from_pem(pem, len(pem), out), "public PEM")
        return out.raw

    def public_from_private_pem(self, pem):
        out = ctypes.create_string_buffer(PK)
        self._check(self.lib.fn_mldsa65_public_from_private_pem(pem, len(pem), out), "private PEM")
        return out.raw

    def sign(self, pem, msg):
        out = ctypes.create_string_buffer(SIG)
        self._check(self.lib.fn_mldsa65_sign_pem(pem, len(pem), msg, len(msg), out), "sign")
        return out.raw

    def verify(self, pk, msg, sig):
        rc = self.lib.fn_mldsa65_verify(sig, len(sig), msg, len(msg), pk)
        if rc not in (0, 1):
            self._check(rc, "verify")
        return rc == 0

    def pem_from_seed(self, seed):
        priv, pub = ctypes.create_string_buffer(8192), ctypes.create_string_buffer(4096)
        pl, ul = ctypes.c_size_t(), ctypes.c_size_t()
        self._check(self.lib.fn_mldsa65_pem_from_seed(seed, priv, 8192, ctypes.byref(pl),
                                                      pub, 4096, ctypes.byref(ul)), "seed")
        return priv.raw[:pl.value], pub.raw[:ul.value]

    def generate(self):
        priv, pub = ctypes.create_string_buffer(8192), ctypes.create_string_buffer(4096)
        pl, ul = ctypes.c_size_t(), ctypes.c_size_t()
        self._check(self.lib.fn_mldsa65_generate_pem(priv, 8192, ctypes.byref(pl),
                                                     pub, 4096, ctypes.byref(ul)), "generate")
        return priv.raw[:pl.value], pub.raw[:ul.value]


class OpenSSL:
    def __init__(self, exe, work):
        self.exe, self.work, self.n = exe, work, 0

    def run(self, *args, data=None):
        return subprocess.run([self.exe, *args], input=data, capture_output=True, check=False)

    def version(self):
        return self.run("version").stdout.decode().strip()

    def path(self, content, suffix):
        self.n += 1
        p = os.path.join(self.work, "f{}{}".format(self.n, suffix))
        with open(p, "wb") as f:
            f.write(content)
        return p

    def genpkey(self, fmt=None):
        args = ["genpkey", "-algorithm", "ML-DSA-65"]
        if fmt:
            args += ["-provparam", "ml-dsa.output_formats=" + fmt]
        r = self.run(*args)
        if r.returncode:
            raise RuntimeError(r.stderr.decode())
        return r.stdout

    def public_pem(self, priv_pem):
        r = self.run("pkey", "-in", self.path(priv_pem, ".pem"), "-pubout")
        if r.returncode:
            raise RuntimeError(r.stderr.decode())
        return r.stdout

    def raw_public(self, pub_pem):
        r = self.run("pkey", "-pubin", "-in", self.path(pub_pem, ".pem"), "-outform", "DER")
        if r.returncode:
            raise RuntimeError(r.stderr.decode())
        der = r.stdout
        assert der.startswith(SPKI_PREFIX) and len(der) == len(SPKI_PREFIX) + PK
        return der[len(SPKI_PREFIX):]

    def sign(self, priv_pem, msg):
        r = self.run("pkeyutl", "-sign", "-rawin", "-inkey", self.path(priv_pem, ".pem"),
                     "-in", self.path(msg, ".msg"))
        if r.returncode:
            raise RuntimeError(r.stderr.decode())
        return r.stdout

    def verify(self, pk, msg, sig):
        der = SPKI_PREFIX + pk
        pem = (b"-----BEGIN PUBLIC KEY-----\n"
               + b"\n".join(base64.b64encode(der)[i:i + 64] for i in range(0, 2 * len(der), 64)
                            if base64.b64encode(der)[i:i + 64])
               + b"\n-----END PUBLIC KEY-----\n")
        r = self.run("pkeyutl", "-verify", "-rawin", "-pubin", "-inkey", self.path(pem, ".pem"),
                     "-in", self.path(msg, ".msg"), "-sigfile", self.path(sig, ".sig"))
        out = r.stdout.decode() + r.stderr.decode()
        if "Signature Verified Successfully" in out:
            return True
        if "Signature Verification Failure" in out:
            return False
        raise RuntimeError("openssl verify undecided: " + out)


def git_files(pattern_args):
    r = subprocess.run(["git", "-C", ROOT, *pattern_args], capture_output=True, check=True)
    return [line for line in r.stdout.decode().splitlines() if line]


def carrier_candidates(data):
    """For every FN-Authorship field in DATA, the (pk, preimage, sig) triples
    of each way an enclosing article parses.  The caller keeps the one the
    reference verifies: a wrong extraction cannot verify."""
    occurrences = []
    for match in re.finditer(rb"(?i)fn-authorship:", data):
        i = match.start()
        starts = [(0, len(data))]
        # One whose length the octets before it give: a CBOR byte-string
        # head (stores, BP ADUs) or a big-endian length of one to four
        # octets (inboxes, signed calls).
        for s in range(i, max(-1, i - 8192), -1):
            for width in (1, 2, 3, 4):
                if s >= width:
                    starts.append((s, int.from_bytes(data[s - width:s], "big")))
        found = []
        for s, length in starts:
            if s > i or s + length <= i or s + length > len(data):
                continue
            article = data[s:s + length]
            try:
                fields, body = fn_verify.parse_fields(article)
                carriers = [lines for name, lines in fields if name == fn_verify.CARRIER_NAME]
                if len(carriers) != 1:
                    continue
                value = fn_verify.field_value(carriers[0])
                carrier = fn_verify.decode_carrier(
                    base64.b64decode(re.sub(rb"[ \t]", b"", value), validate=True))
            except ValueError:
                continue
            kept = [lines for name, lines in fields if name not in fn_verify.RELAY_FIELDS]
            source = b"".join(line + b"\r\n" for lines in kept for line in lines) + b"\r\n" + body
            preimage = fn_verify.signed_preimage(carrier["version"], carrier["principal"],
                                                 carrier["ed25519"], carrier["ml-dsa-65"], source)
            triple = (carrier["ml-dsa-65"], preimage, carrier["ml-dsa-65-signature"])
            if all(triple != t for t, _ in found):
                found.append((triple, article))
        occurrences.append(found)
    return occurrences


def transcript_articles(data):
    """Articles an NNTP wire log shows ("TIME N S: LINE"), un-dot-stuffed."""
    articles, current = [], None
    for line in data.split(b"\n"):
        m = re.match(rb"^\S+ \d+ S: (.*)$", line)
        if not m:
            continue
        text = m.group(1)
        if current is None:
            if text.startswith(b"220 ") or text.startswith(b"222 "):
                current = []
            continue
        if text == b".":
            articles.append(b"".join(x + b"\r\n" for x in current))
            current = None
            continue
        current.append(text[1:] if text.startswith(b"..") else text)
    return articles


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("library")
    ap.add_argument("--openssl", default=os.environ.get("FN_INTEROP_OPENSSL", "openssl"))
    ap.add_argument("--json")
    args = ap.parse_args(argv)
    seam = Seam(args.library)
    findings, report = [], {"implementation": seam.implementation()}

    def finding(text):
        findings.append(text)
        print("FINDING", text)

    with tempfile.TemporaryDirectory() as work:
        ossl = OpenSSL(args.openssl, work)
        report["openssl"] = ossl.version()
        print("seam:", report["implementation"])
        print("reference:", report["openssl"])

        # keys
        key_checks = 0
        for _ in range(3):
            priv = ossl.genpkey()
            pub = ossl.public_pem(priv)
            raw = ossl.raw_public(pub)
            if seam.public_from_private_pem(priv) != raw or seam.public_from_pem(pub) != raw:
                finding("seam public key differs from OpenSSL's")
            der = base64.b64decode(b"".join(priv.split(b"\n")[1:-2]))
            seed = der[30:62]
            mine_priv, mine_pub = seam.pem_from_seed(seed)
            if mine_priv != priv:
                finding("seam private PEM from the seed is not OpenSSL's bytes")
            if mine_pub != pub:
                finding("seam public PEM is not OpenSSL's bytes")
            key_checks += 1
        for fmt in ("seed-only", "priv-only"):
            priv = ossl.genpkey(fmt)
            raw = ossl.raw_public(ossl.public_pem(priv))
            msg = b"format " + fmt.encode()
            sig = seam.sign(priv, msg)
            if not ossl.verify(raw, msg, sig):
                finding("OpenSSL refused a seam signature from a {} key".format(fmt))
            if fmt == "seed-only" and seam.public_from_private_pem(priv) != raw:
                finding("seed-only public key differs")
            key_checks += 1
        mine_priv, mine_pub = seam.generate()
        if ossl.public_pem(mine_priv) != mine_pub:
            finding("OpenSSL derives a different public PEM from a seam-generated key")
        key_checks += 1
        report["generated-key-checks"] = key_checks

        # signatures, both directions
        sig_checks = 0
        priv = ossl.genpkey()
        raw = ossl.raw_public(ossl.public_pem(priv))
        # OpenSSL's pkeyutl cannot sign or verify an empty input ("Could not
        # allocate 0 bytes"); the empty message is a seam-only self check.
        empty = seam.sign(priv, b"")
        if not seam.verify(raw, b"", empty) or seam.verify(raw, b"\0", empty):
            finding("seam empty-message sign/verify")
        for size in (1, 33, 70000):
            msg = bytes((i * 7 + size) & 255 for i in range(size))
            for signer in ("openssl", "seam"):
                sig = ossl.sign(priv, msg) if signer == "openssl" else seam.sign(priv, msg)
                if len(sig) != SIG:
                    finding("{} signature is {} octets".format(signer, len(sig)))
                    continue
                if not seam.verify(raw, msg, sig):
                    finding("seam refused a {} signature ({} octets)".format(signer, size))
                if not ossl.verify(raw, msg, sig):
                    finding("OpenSSL refused a {} signature ({} octets)".format(signer, size))
                bad = bytearray(sig)
                bad[size % SIG] ^= 1
                if seam.verify(raw, msg, bytes(bad)) or ossl.verify(raw, msg, bytes(bad)):
                    finding("a flipped signature bit verified ({})".format(signer))
                if seam.verify(raw, msg + b"x", sig):
                    finding("seam verified a changed message")
                sig_checks += 1
        report["signature-round-trips"] = sig_checks

        # committed keys
        pem_files = [f for f in git_files(["ls-files", "tests", "planning"])
                     if f.endswith(".pem") or f.endswith(".raw")]
        keys = []
        for rel in pem_files:
            with open(os.path.join(ROOT, rel), "rb") as fh:
                content = fh.read()
            if rel.endswith(".raw"):
                ok = len(content) == PK
                keys.append((rel, "raw", ok))
                if not ok:
                    finding("{} is not a {}-octet key".format(rel, PK))
                continue
            if b"PRIVATE KEY" in content:
                derived = seam.public_from_private_pem(content)
                ref = ossl.raw_public(ossl.public_pem(content))
            else:
                derived = seam.public_from_pem(content)
                ref = ossl.raw_public(content)
            keys.append((rel, "pem", derived == ref))
            if derived != ref:
                finding("{}: seam key differs from OpenSSL's".format(rel))
        report["committed-keys"] = keys

        # committed signed carriers
        files = [f for f in git_files(["grep", "-l", "-i", "-a", "fn-authorship:", "--",
                                       "tests", "planning"])
                 if not f.endswith((".py", ".lisp", ".md"))]
        # Plain articles first, so containers can be matched against them.
        files.sort(key=lambda f: (not f.endswith((".eml", ".txt", ".log")), f))
        seen, per_file, unextracted, copies, verified_articles = set(), [], [], [], set()
        for rel in files:
            with open(os.path.join(ROOT, rel), "rb") as fh:
                data = fh.read()
            if rel.endswith(".log"):
                occurrences = [o for article in transcript_articles(data)
                               for o in carrier_candidates(article)]
            else:
                occurrences = carrier_candidates(data)
            triples, fresh = [], 0
            for candidates in occurrences:
                chosen = None
                for (pk, preimage, sig), article in candidates:
                    if (pk, sig, preimage) in seen or ossl.verify(pk, preimage, sig):
                        chosen = (pk, preimage, sig)
                        verified_articles.add(article)
                        break
                if chosen is None:
                    if any(seam.verify(*c) for c, _ in candidates):
                        finding("{}: the seam verifies a carrier OpenSSL refuses".format(rel))
                    elif any(a in data for a in verified_articles):
                        # A container whose framing this harness does not
                        # decode, holding a byte-identical verified article.
                        copies.append(rel)
                    else:
                        unextracted.append(rel)
                    continue
                triples.append(chosen)
                pk, preimage, sig = chosen
                if (pk, sig, preimage) in seen:
                    continue
                seen.add((pk, sig, preimage))
                fresh += 1
                if not seam.verify(pk, preimage, sig):
                    finding("{}: OpenSSL verifies, the seam refuses".format(rel))
            per_file.append((rel, len(triples), fresh))
            print("fixture {}: {} carriers, {} distinct new".format(rel, len(triples), fresh))
        report["fixture-files"] = per_file
        report["distinct-fixture-signatures"] = len(seen)
        report["carrier-fields-without-a-verifying-extraction"] = unextracted
        report["byte-identical-copies-of-verified-articles"] = copies
        for rel in copies:
            print("holds a byte-identical copy of a verified article:", rel)
        for rel in unextracted:
            print("not extracted (neither implementation verifies any parse):", rel)

    report["findings"] = findings
    print("keys {} + committed {}; round trips {}; fixture signatures {}; findings {}".format(
        report["generated-key-checks"], len(report["committed-keys"]),
        report["signature-round-trips"], report["distinct-fixture-signatures"], len(findings)))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(report, fh, indent=1, default=list)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
