#!/usr/bin/env python3
"""The AUTHINFO credential bridge: ACL2 derives the verifier, Python stores it.

`books/auth-secret.lisp` owns the scheme (specs/nntp.md, "The stored AUTHINFO
credential"): the stored value is
``(:fn-authsec-v2 salt digest stored-key server-key)`` (the digest
``(fn-digest-tagged "fn-authinfo-v1" (append salt secret))``, the keys
SCRAM-SHA-256's under 4096 iterations)
and `fn-authsec-checkp` is the comparison the served path runs.  This module
calls `fn-authsec-enrol` in an ACL2 session and reads the two octet strings
back.  It computes NOTHING: there is no `hashlib` here and there must never
be one, because AGENTS.md's one-owner rule forbids Python from computing a
value ACL2 compares.

The salt is the one input this side supplies, and it is entropy rather than a
derivation: `os.urandom(16)`.  The scheme fixes its length at 16 octets
(`*fn-authsec-salt-octets*`), which is what makes the preimage unambiguous
(`fn-authsec-preimage-injective`).

Cost, measured on this laptop (ACL2 8.7, SBCL, 2026-09-20): the session start
(`include-book "books/auth-secret"`, which pulls the attached SHA-256 of
`books/sha256.lisp`) dominates; one `fn-authsec-enrol` over a 16-octet salt
and a secret of at most 256 octets is a single SHA-256 of at most 272 octets,
which is five compression blocks.  `fn principal set-password` starts one
session and makes one call.
"""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from tools.run_store import (  # noqa: E402
    StoreError, acl2_result, decimal_list, read_prompt,
)

SALT_OCTETS = 16
DIGEST_OCTETS = 32
MAX_NAME_OCTETS = 64
MAX_SECRET_OCTETS = 256


def octet_form(data):
    """An ACL2 quoted list literal of the octets."""
    return "'(" + " ".join(str(byte) for byte in data) + ")"


class AuthSecretSession:
    """One ACL2 session over books/auth-secret, with the digest attached."""

    BOOKS = ('(include-book "books/auth-secret")',)

    def __init__(self):
        import subprocess  # noqa: PLC0415 (only this path starts a process)
        from tools import acl2_slots  # noqa: PLC0415
        # The machine's ACL2 pool and heap cap, as every fn launcher (PKT-162).
        self.proc = acl2_slots.popen(
            [os.environ.get("FN_ACL2", "acl2")], "auth-secret session", cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        read_prompt(self.proc, 300.0)
        for form in self.BOOKS:
            self.call(form, timeout=600.0)

    def call(self, form, timeout=120.0):
        self.proc.stdin.write((form + "\n").encode("ascii"))
        self.proc.stdin.flush()
        output = read_prompt(self.proc, timeout)
        upper = output.upper()
        if b"ACL2 ERROR" in upper or b"HARD ACL2 ERROR" in upper:
            raise StoreError(output.decode("utf-8", "replace"))
        return output

    def octets(self, form):
        body = acl2_result(self.call(form))
        if body == b"NIL":
            return b""
        values = decimal_list(body)
        if values is None or any(value > 255 for value in values):
            raise StoreError("ACL2 returned a non-octet result: {!r}".format(body))
        return bytes(values)

    def enrol(self, salt, secret):
        """(salt, digest, stored_key, server_key) for this secret, all derived
        by ACL2 (verifier v2: the fast digest USER/PASS and PLAIN check, and
        SCRAM-SHA-256's StoredKey and ServerKey, books/scram.lisp).

        The salt goes in and comes back out of `fn-authsec-enrol`'s own
        coercion, so what is stored is what `fn-authsec-checkp` will read.
        """
        if len(salt) != SALT_OCTETS:
            raise StoreError("a salt is exactly {} octets".format(SALT_OCTETS))
        stored_salt = self.octets(
            "(fn-authsec-ver-salt (fn-authsec-enrol {} {}))"
            .format(octet_form(salt), octet_form(secret)))
        digest = self.octets(
            "(fn-authsec-ver-digest (fn-authsec-enrol {} {}))"
            .format(octet_form(salt), octet_form(secret)))
        stored_key = self.octets(
            "(fn-authsec-ver-stored-key (fn-authsec-enrol {} {}))"
            .format(octet_form(salt), octet_form(secret)))
        server_key = self.octets(
            "(fn-authsec-ver-server-key (fn-authsec-enrol {} {}))"
            .format(octet_form(salt), octet_form(secret)))
        if (len(stored_salt) != SALT_OCTETS or len(digest) != DIGEST_OCTETS
                or len(stored_key) != DIGEST_OCTETS
                or len(server_key) != DIGEST_OCTETS):
            raise StoreError("ACL2 returned a verifier of the wrong shape")
        return stored_salt, digest, stored_key, server_key

    def checkp(self, salt, digest, stored_key, server_key, supplied):
        """What the served path would answer.  Used by the tests, not by `fn`."""
        body = acl2_result(self.call(
            "(fn-authsec-checkp (fn-authsec-verifier {} {} {} {}) {})"
            .format(octet_form(salt), octet_form(digest), octet_form(stored_key),
                    octet_form(server_key), octet_form(supplied))))
        return body.strip().upper() == b"T"

    def close(self):
        if self.proc is not None:
            from tools import acl2_slots  # noqa: PLC0415
            try:
                try:
                    self.proc.stdin.close()
                except OSError:
                    pass
                self.proc.wait(timeout=30)
            finally:
                self.proc = None
                acl2_slots.release_tree_slot()


def enrol(secret, salt=None):
    """(salt, digest, stored_key, server_key) as hex, for one credential.
    One session, one call."""
    if salt is None:
        salt = os.urandom(SALT_OCTETS)
    session = AuthSecretSession()
    try:
        fields = session.enrol(salt, secret)
    finally:
        session.close()
    return tuple(field.hex() for field in fields)
