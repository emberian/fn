"""The host's one Ed25519 entry point.

No other Python module in this tree imports `cryptography`.  Signature
verification is a host service, not a decision: ACL2 owns what the octets
mean, `books/anchor.lisp` constrains `fn-anchor-sig-verify` to a boolean over
a 32-octet key and a 64-octet signature, and this module supplies the verdict
for the octets ACL2 produced.  Nothing here claims Ed25519 is unforgeable.

`cryptography` is an optional dependency.  When it is absent every entry point
raises `CryptoUnavailable`; no path returns `True`, and no caller may read an
exception as an accepted signature.  The laptop's system Python does not have
it; a virtual environment or hbox's python3 does.
"""

from __future__ import annotations

ED25519_PUBLIC_KEY_OCTETS = 32
ED25519_SIGNATURE_OCTETS = 64


class CryptoUnavailable(RuntimeError):
    """Ed25519 is not available in this interpreter.  Not a verdict."""


try:  # pragma: no cover - import-time branch, exercised by both environments
    from cryptography.exceptions import InvalidSignature as _InvalidSignature
    from cryptography.hazmat.primitives.asymmetric.ed25519 import (
        Ed25519PrivateKey as _Ed25519PrivateKey,
        Ed25519PublicKey as _Ed25519PublicKey,
    )
    from cryptography.hazmat.primitives.serialization import (
        Encoding as _Encoding, NoEncryption as _NoEncryption,
        PrivateFormat as _PrivateFormat, PublicFormat as _PublicFormat,
    )
    _IMPORT_ERROR = None
except ImportError as error:  # pragma: no cover - depends on the environment
    _Ed25519PrivateKey = _Ed25519PublicKey = None
    _InvalidSignature = ()
    _IMPORT_ERROR = error


def available():
    """True when Ed25519 can be computed here.  Never a signature verdict."""
    return _Ed25519PublicKey is not None


def unavailable_reason():
    """Why Ed25519 is unavailable, for a test skip message or an operator."""
    if available():
        return None
    return "python `cryptography` is not installed: {}".format(_IMPORT_ERROR)


def _require():
    if not available():
        raise CryptoUnavailable(unavailable_reason())


def verify(public_key, message, signature):
    """Ed25519 verify.  True, False, or CryptoUnavailable -- never a silent True."""
    _require()
    if not isinstance(public_key, (bytes, bytearray)) or len(public_key) != ED25519_PUBLIC_KEY_OCTETS:
        return False
    if not isinstance(signature, (bytes, bytearray)) or len(signature) != ED25519_SIGNATURE_OCTETS:
        return False
    try:
        _Ed25519PublicKey.from_public_bytes(bytes(public_key)).verify(
            bytes(signature), bytes(message))
    except _InvalidSignature:
        return False
    except ValueError:
        return False
    return True


def sign(private_key, message):
    """Test-only: sign `message`.  fn never signs an anchor; servers do."""
    _require()
    return _Ed25519PrivateKey.from_private_bytes(bytes(private_key)).sign(bytes(message))


def generate_keypair():
    """Test-only: a fresh (private, public) Ed25519 pair as raw octets."""
    _require()
    private = _Ed25519PrivateKey.generate()
    return (private.private_bytes(_Encoding.Raw, _PrivateFormat.Raw, _NoEncryption()),
            private.public_key().public_bytes(_Encoding.Raw, _PublicFormat.Raw))
