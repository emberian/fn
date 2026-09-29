"""A SASL client for the native tests: PLAIN (RFC 4616) and SCRAM-SHA-256
(RFC 5802, RFC 7677) with the tls-exporter channel binding (RFC 9266), over
AUTHINFO SASL (RFC 4643 section 2.4).

This is the tests' independent check of the server: it is written from the
RFCs with hashlib and hmac, and shares no code or constant with the ACL2
mechanism (books/scram.lisp, books/sasl.lisp).  It never computes a stored
verifier; the node's operator verbs write those.
"""

import base64
import hashlib
import hmac
import os


def b64(octets):
    return base64.b64encode(octets).decode("ascii")


def unb64(text):
    if isinstance(text, bytes):
        text = text.decode("ascii")
    return base64.b64decode(text.strip(), validate=True)


def plain_response(login, password, authzid=b""):
    """RFC 4616 section 2: [authzid] NUL authcid NUL passwd, base64."""
    return b64(_octets(authzid) + b"\0" + _octets(login) + b"\0" + _octets(password))


def saslname(login):
    """RFC 5802 section 5.1: ',' and '=' escaped.  The tests' logins are
    ASCII, so SASLprep is the identity on them."""
    return _octets(login).replace(b"=", b"=3D").replace(b",", b"=2C")


def _octets(value):
    return value.encode("utf-8") if isinstance(value, str) else bytes(value)


def _hmac(key, message):
    return hmac.new(key, message, hashlib.sha256).digest()


def _attributes(message):
    """The a=value attributes of a SCRAM message, in order."""
    found = []
    for part in message.split(b","):
        if len(part) < 2 or part[1:2] != b"=":
            raise ValueError("malformed SCRAM attribute {!r}".format(part))
        found.append((part[:1], part[2:]))
    return found


class ScramSha256:
    """One SCRAM-SHA-256 exchange.  BINDING, when given, is the RFC 9266
    tls-exporter value and the exchange is SCRAM-SHA-256-PLUS
    (gs2 header "p=tls-exporter,,"); without it the header is "n,,"."""

    def __init__(self, login, password, *, cnonce=None, binding=None):
        self.login = _octets(login)
        self.password = _octets(password)
        self.cnonce = cnonce or b64(os.urandom(18)).encode("ascii")
        self.binding = binding
        self.gs2 = b"p=tls-exporter,," if binding is not None else b"n,,"
        self.bare = b"n=" + saslname(self.login) + b",r=" + self.cnonce
        self.server_signature = None
        self.salt = None
        self.iterations = None
        self.nonce = None

    @property
    def mechanism(self):
        return "SCRAM-SHA-256-PLUS" if self.binding is not None else "SCRAM-SHA-256"

    def client_first(self):
        return self.gs2 + self.bare

    def client_final(self, server_first):
        """The client-final-message for SERVER_FIRST (octets), after checking
        that the server nonce extends ours."""
        fields = dict(_attributes(server_first))
        if b"m" in fields:
            raise ValueError("server-first carries a mandatory extension")
        self.nonce, self.salt = fields[b"r"], unb64(fields[b"s"])
        self.iterations = int(fields[b"i"])
        if not (self.nonce.startswith(self.cnonce) and len(self.nonce) > len(self.cnonce)):
            raise ValueError("the server nonce does not extend the client nonce")
        cbind = self.gs2 + (self.binding or b"")
        without_proof = b"c=" + b64(cbind).encode("ascii") + b",r=" + self.nonce
        auth_message = self.bare + b"," + server_first + b"," + without_proof
        salted = hashlib.pbkdf2_hmac("sha256", self.password, self.salt, self.iterations)
        client_key = _hmac(salted, b"Client Key")
        stored_key = hashlib.sha256(client_key).digest()
        signature = _hmac(stored_key, auth_message)
        proof = bytes(a ^ b for a, b in zip(client_key, signature))
        self.server_signature = _hmac(_hmac(salted, b"Server Key"), auth_message)
        return without_proof + b",p=" + b64(proof).encode("ascii")

    def server_final_ok(self, server_final):
        """True when SERVER_FINAL is v= the expected ServerSignature."""
        fields = _attributes(server_final)
        if not fields or fields[0][0] != b"v":
            return False
        return hmac.compare_digest(unb64(fields[0][1]), self.server_signature)


def status_data(line):
    """(status, decoded data or None) of a 383/283 line: the base64 after the
    status code, '=' being the empty challenge (RFC 4643 section 2.4.1)."""
    text = line.decode("ascii", "replace").rstrip("\r\n")
    status, _, rest = text.partition(" ")
    rest = rest.strip()
    if status not in ("383", "283") or not rest:
        return status, None
    return status, (b"" if rest == "=" else unb64(rest))


def scram_login(command, send_line, login, password, *, binding=None, cnonce=None):
    """Run SCRAM over an NNTP session: COMMAND(text) sends a command line and
    answers its status line; SEND_LINE(text) sends a bare continuation line
    and answers the next status line.  Returns (final status line, the
    exchange, the client-final line sent or None)."""
    scram = ScramSha256(login, password, binding=binding, cnonce=cnonce)
    first = command("AUTHINFO SASL {} {}".format(scram.mechanism, b64(scram.client_first())))
    status, server_first = status_data(first)
    if status != "383" or server_first is None:
        return first, scram, None
    final_line = b64(scram.client_final(server_first))
    return send_line(final_line), scram, final_line
