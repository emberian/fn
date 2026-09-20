"""The Python side of the ACL2-owned frame, identity, group and charge rules.

Nothing here decides anything.  ACL2 owns the frame grammar, the field
grammar, every bound, the Message-ID grammar, the group table, the charge
policy and the content-identity derivation.  This module marshals octets to
and from a live ACL2 session and computes SHA-256 over byte strings it does
not interpret, which is A-CRYPTO: `books/frame.lisp` constrains
`fn-frame-digest` to 32 octets and nothing else, and the host supplies them.

Every session-level constant Python still holds for slicing (`run_store.MAGIC`,
`TRAILER_BYTES`, the journal record caps) is checked against the ACL2
constants when a session opens, so a divergence is a startup failure rather
than a silent second grammar.
"""

from __future__ import annotations

import hashlib
import re
import threading

_TOKEN = re.compile(rb"\(|\)|[0-9]+|:[A-Za-z0-9\-]+|NIL|T")
_ANY = re.compile(rb"\s*(?:\(|\)|[0-9]+|:[A-Za-z0-9\-]+|NIL|T)\s*")


class BridgeError(RuntimeError):
    """The ACL2 side refused, or answered something this module cannot read."""


class Keyword(str):
    """An ACL2 keyword, lowercased and without its colon."""

    __slots__ = ()


def _tokenize(body: bytes) -> list[bytes]:
    tokens, position = [], 0
    while position < len(body):
        match = _ANY.match(body, position)
        if match is None:
            raise BridgeError("ACL2 returned an unreadable form")
        tokens.append(_TOKEN.search(match.group(0)).group(0))
        position = match.end()
    return tokens


def _parse(tokens: list[bytes], index: int):
    token = tokens[index]
    if token == b"(":
        items, index = [], index + 1
        while tokens[index] != b")":
            item, index = _parse(tokens, index)
            items.append(item)
        return items, index + 1
    if token == b")":
        raise BridgeError("ACL2 returned an unbalanced form")
    if token == b"NIL":
        return [], index + 1
    if token == b"T":
        return True, index + 1
    if token.startswith(b":"):
        return Keyword(token[1:].decode("ascii").lower()), index + 1
    return int(token), index + 1


def read_form(output: bytes):
    """Parse one ACL2 result: nested lists of naturals, keywords, NIL and T."""
    from tools.run_store import acl2_result

    tokens = _tokenize(acl2_result(output))
    if not tokens:
        raise BridgeError("ACL2 returned no form")
    value, index = _parse(tokens, 0)
    if index != len(tokens):
        raise BridgeError("ACL2 returned more than one form")
    return value


def _octets(data: bytes) -> str:
    return "'(" + " ".join(str(byte) for byte in data) + ")"


def _as_bytes(value) -> bytes:
    if not isinstance(value, list) or any(
            not isinstance(item, int) or not 0 <= item <= 255 for item in value):
        raise BridgeError("ACL2 returned a non-octet list")
    return bytes(value)


class FrameSession:
    """An ACL2 session loaded with the host wrappers over the frame books."""

    def __init__(self, store=None):
        from tools.run_store import Acl2Store

        self.owned = store is None
        self.store = Acl2Store() if self.owned else store
        self.constants = self._constants()
        self._check_host_constants()
        self._schemas: dict[tuple[str, str], tuple] = {}

    def call(self, form: str):
        return read_form(self.store.call(form))

    def close(self):
        if self.owned:
            self.store.close()

    def _constants(self) -> dict[str, int]:
        values = self.call("(fn-store-frame-constants)")
        names = ("header", "trailer", "overhead", "max_store", "max_workflow",
                 "max_receipt", "max_inbound", "max_text", "max_blob",
                 "max_identity")
        if not isinstance(values, list) or len(values) != len(names):
            raise BridgeError("ACL2 returned an unexpected constant vector")
        return dict(zip(names, values))

    def _check_host_constants(self) -> None:
        """Fail at startup if a host slice constant left the ACL2 grammar."""
        from tools import receipt_journal, run_store, workflow_journal

        checks = (
            ("store trailer", run_store.TRAILER_BYTES, self.constants["trailer"]),
            ("store header", len(run_store.MAGIC) + 4, self.constants["header"]),
            ("workflow record cap", workflow_journal.MAX_RECORD,
             self.constants["max_workflow"] + self.constants["overhead"]),
            ("workflow text cap", workflow_journal.MAX_TEXT,
             self.constants["max_text"]),
            ("receipt record cap", receipt_journal.MAX_RECORD,
             self.constants["max_receipt"] + self.constants["overhead"]),
            ("receipt text cap", receipt_journal.MAX_TEXT,
             self.constants["max_text"]),
            ("receipt blob cap", receipt_journal.MAX_BLOB,
             self.constants["max_blob"]),
            ("inbound bundle cap", workflow_journal.MAX_INBOUND_BUNDLE,
             self.constants["max_inbound"]),
            ("inbound identity cap", workflow_journal.MAX_IDENTITY,
             self.constants["max_identity"]),
        )
        for name, host, model in checks:
            if host != model:
                raise BridgeError(
                    "host {} is {} but the model says {}".format(name, host, model))

    # -- framing ------------------------------------------------------------

    def seal(self, prefix: bytes) -> bytes:
        """Append the integrity trailer over the prefix ACL2 produced."""
        return prefix + hashlib.sha256(prefix).digest()

    def digest_of(self, framed: bytes) -> bytes:
        """The digest a decoder must be given for these stored octets."""
        trailer = self.constants["trailer"]
        if len(framed) < trailer:
            return b""
        return hashlib.sha256(framed[:-trailer]).digest()

    def _prefix(self, form: str) -> bytes:
        value = self.call(form)
        if isinstance(value, Keyword):
            raise BridgeError("ACL2 refused to frame: {}".format(value))
        return _as_bytes(value)

    def _decoded(self, form: str):
        value = self.call(form)
        if not isinstance(value, list) or not value:
            raise BridgeError("ACL2 returned an unexpected frame result")
        if value[0] != "ok":
            reason = value[1] if len(value) > 1 else "unknown"
            raise BridgeError("frame refused: {}".format(reason))
        return value[1:]

    def store_frame(self, record: bytes) -> bytes:
        return self.seal(self._prefix(
            "(fn-store-frame-store-protected " + _octets(record) + ")"))

    def store_unframe(self, framed: bytes) -> bytes:
        payload, = self._decoded(
            "(fn-store-frame-store-decode " + _octets(framed) + " "
            + _octets(self.digest_of(framed)) + ")")
        return _as_bytes(payload)

    # -- journal records ----------------------------------------------------

    def schema(self, schema_name: str, kind: str):
        key = (schema_name, kind)
        if key not in self._schemas:
            value = self.call("(fn-store-frame-{}-schema :{})".format(
                schema_name, kind))
            if not isinstance(value, list) or not value or value[0] != "ok":
                raise BridgeError("unknown {} record kind: {}".format(
                    schema_name, kind))
            names = [_as_bytes(name).decode("utf-8") for name in value[1]]
            specs = value[2]
            if len(names) != len(specs):
                raise BridgeError("ACL2 schema name/specification mismatch")
            self._schemas[key] = (tuple(names), tuple(specs))
        return self._schemas[key]

    def kinds(self, schema_name: str) -> tuple[str, ...]:
        return tuple(self.call(
            "(fn-store-frame-{}-kinds)".format(schema_name)))

    @staticmethod
    def _to_acl2(spec, value) -> str:
        if spec == "text":
            if not isinstance(value, str):
                raise BridgeError("text field is not a string")
            return _octets(value.encode("utf-8", "strict"))
        if spec == "blob":
            if not isinstance(value, (bytes, bytearray)):
                raise BridgeError("blob field is not bytes")
            return _octets(bytes(value))
        if spec == "nat":
            if not isinstance(value, int) or isinstance(value, bool):
                raise BridgeError("natural field is not an integer")
            if value < 0:
                raise BridgeError("natural field is negative")
            return str(value)
        # An enumeration.  A single-member table is the boundary spelling of a
        # Python True; every other table is spelled by its member's name.
        keys = spec[1:]
        if len(keys) == 1:
            if value is not True:
                raise BridgeError("single-valued enumeration is not True")
            return ":" + keys[0]
        if not isinstance(value, str) or value not in keys:
            raise BridgeError("unknown enumeration member: {!r}".format(value))
        return ":" + value

    @staticmethod
    def _from_acl2(spec, value):
        if spec == "text":
            return _as_bytes(value).decode("utf-8", "strict")
        if spec == "blob":
            return _as_bytes(value)
        if spec == "nat":
            if not isinstance(value, int) or isinstance(value, bool):
                raise BridgeError("ACL2 returned a non-natural field")
            return value
        keys = spec[1:]
        if not isinstance(value, Keyword) or value not in keys:
            raise BridgeError("ACL2 returned an unknown enumeration member")
        return True if len(keys) == 1 else str(value)

    def record_frame(self, schema_name: str, kind: str, values: dict) -> bytes:
        names, specs = self.schema(schema_name, kind)
        if set(values) != set(names):
            raise BridgeError("record fields do not match the ACL2 schema")
        arguments = " ".join(
            self._to_acl2(spec, values[name]) for name, spec in zip(names, specs))
        return self.seal(self._prefix(
            "(fn-store-frame-{}-protected :{} (list {}))".format(
                schema_name, kind, arguments)))

    def record_unframe(self, schema_name: str, framed: bytes):
        kind, raw = self._decoded(
            "(fn-store-frame-{}-decode {} {})".format(
                schema_name, _octets(framed), _octets(self.digest_of(framed))))
        names, specs = self.schema(schema_name, str(kind))
        if len(raw) != len(names):
            raise BridgeError("ACL2 returned the wrong number of fields")
        return str(kind), {name: self._from_acl2(spec, value)
                           for name, spec, value in zip(names, specs, raw)}

    # -- inbound bundles ----------------------------------------------------

    def _inbound_head(self) -> int:
        return (self.constants["header"] + 2 + self.constants["max_text"]
                + 4 + self.constants["max_identity"])

    def inbound_frame(self, bid: str, identity: bytes, payload: bytes) -> bytes:
        """Frame one staged bundle under its BID *and* its ACL2 identity.

        The identity is the octet string ACL2 derived from the bundle's own
        primary block.  It is not optional: a frame carrying only the agent's
        BID cannot be opened, so nothing downstream can fall back to keying on
        transport metadata.
        """
        if not isinstance(identity, (bytes, bytearray)) or not identity:
            raise BridgeError("inbound identity is not present")
        prefix = self._prefix(
            "(fn-store-frame-inbound-prefix {} {} {})".format(
                _octets(bid.encode("utf-8", "strict")), _octets(bytes(identity)),
                len(payload)))
        return self.seal(prefix + payload)

    def inbound_unframe(self, framed: bytes) -> tuple[str, bytes, bytes]:
        head = self._inbound_head()
        trailer = self.constants["trailer"]
        if len(framed) < trailer:
            raise BridgeError("frame refused: truncated")
        bid, identity, length = self._decoded(
            "(fn-store-frame-inbound-open {} {} {} {})".format(
                _octets(framed[:head]), len(framed),
                _octets(framed[-trailer:]), _octets(self.digest_of(framed))))
        bid = _as_bytes(bid).decode("utf-8", "strict")
        identity = _as_bytes(identity)
        start = len(framed) - trailer - length
        return bid, identity, framed[start:len(framed) - trailer]

    # -- identity, charge, groups, Message-ID -------------------------------

    def subject_id(self, payload: bytes) -> bytes:
        """The canonical subject-v1 identity octets for an article payload.

        ACL2 owns the preimage.  It hands back the fixed head
        (`"fn/subject/v1" || 0x00 || uint32-be(len)`) and the host appends the
        payload and hashes, exactly as with the inbound frame prefix, so a
        32 KiB article never crosses the bridge.
        """
        prefix = _as_bytes(self.call(
            "(fn-store-subject-prefix {})".format(len(payload))))
        digest = hashlib.sha256(prefix + payload).digest()
        return _as_bytes(self.call(
            "(fn-store-subject-id " + _octets(digest) + ")"))

    def obligation_id(self, msgid: bytes, subject: bytes) -> bytes:
        """The canonical obligation-v1 identity octets.

        `subject` is the canonical subject identity octets, not its text.
        """
        preimage = _as_bytes(self.call(
            "(fn-store-obligation-preimage " + _octets(msgid) + " "
            + _octets(subject) + ")"))
        digest = hashlib.sha256(preimage).digest()
        return _as_bytes(self.call(
            "(fn-store-obligation-id " + _octets(digest) + ")"))

    def post_boundary(self, msgid: bytes, payload_length: int,
                      group_count: int, charge: int) -> str:
        """The whole POST admission boundary, decided once in ACL2."""
        value = self.call(
            "(fn-store-post-boundary {} {} {} {})".format(
                _octets(msgid), int(payload_length), int(group_count),
                int(charge)))
        if not isinstance(value, Keyword):
            raise BridgeError("ACL2 returned an unexpected boundary verdict")
        return str(value)

    def charge(self, length: int) -> int:
        value = self.call("(fn-store-charge {})".format(int(length)))
        if not isinstance(value, int) or value <= 0:
            raise BridgeError("ACL2 returned a non-positive charge")
        return value

    def message_id_valid(self, msgid: bytes) -> bool:
        return self.call(
            "(fn-store-msgid-validp " + _octets(msgid) + ")") is True

    def identity_text(self, identity: bytes) -> bytes:
        """The one rendering of a canonical identity where a string is forced.

        The store record metadata fields, the workflow journal JSON and the
        NNTP header value all carry text; ACL2 decides what that text is.
        """
        return _as_bytes(self.call(
            "(fn-store-identity-text " + _octets(identity) + ")"))

    def config_record_initial(self, names) -> bytes:
        """The initial configuration record for these group names, encoded
        and admitted by `books/config`/`books/node-config`."""
        forms = " ".join(_octets(name.encode("utf-8", "strict")) for name in names)
        value = self.call("(fn-cfg-host-initial-octets (list {}))".format(forms))
        if isinstance(value, Keyword):
            raise BridgeError("ACL2 refused the initial group table")
        return _as_bytes(value)

    def format_id(self) -> str:
        return _as_bytes(self.call("(fn-store-format-id)")).decode("utf-8")

    def group_codes(self, names, domain) -> list[int]:
        """Codes of `names` in `domain`, the allocation domain ACL2 handed the
        store at open; Python carries the domain back, never indexes it."""
        forms = " ".join(_octets(name.encode("utf-8", "strict"))
                         for name in names)
        table = " ".join(_octets(name.encode("utf-8", "strict"))
                         for name in domain)
        value = self.call("(fn-store-group-codes (list {}) (list {}))".format(forms, table))
        if isinstance(value, Keyword):
            raise BridgeError("unknown or duplicate configured group")
        if not isinstance(value, list) or len(value) != len(list(names)):
            raise BridgeError("ACL2 returned an unexpected group code list")
        return value


_LOCK = threading.Lock()
_SESSION: FrameSession | None = None


def adopt(store) -> FrameSession:
    """Use an already-open Acl2Store for framing instead of a second process."""
    global _SESSION
    with _LOCK:
        if _SESSION is not None and _SESSION.owned:
            _SESSION.close()
        _SESSION = FrameSession(store)
        return _SESSION


def session(bridge=None) -> FrameSession:
    """The process-wide framing session, opened on first use."""
    global _SESSION
    if isinstance(bridge, FrameSession):
        return bridge
    if bridge is not None:
        return adopt(bridge)
    with _LOCK:
        if _SESSION is None:
            _SESSION = FrameSession()
        return _SESSION


def close() -> None:
    global _SESSION
    with _LOCK:
        if _SESSION is not None:
            _SESSION.close()
            _SESSION = None
