"""The Python side of the ACL2-owned bundle identity and expiry decision.

Nothing here decides anything.  ACL2 owns the bundle frame check, the primary
block grammar, the identity projection and its canonical encoding, the DTN
epoch and unit conversions, and the expiry verdict.  This module marshals the
raw octets one BPA produced into a live ACL2 session, reads back a regex-checked
form, and computes SHA-256 over an octet string it does not interpret.

The agent's BID does not appear here at all.  It is a handle for `/download?`
and `/delete?` on the agent that issued it, and it is not evidence about the
bundle; the identity is what the bundle's own primary block says it is.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import time

from tools import frame_bridge, run_store

# The host's claimed half-width, in milliseconds, of the interval it is willing
# to certify contains the true DTN time.  This is configuration, not a
# measurement: it is what a local operator asserts about this node's clock, and
# `fn-clock-expiry-decision` answers `:uncertain` rather than guessing whenever
# the interval straddles the lifetime.  Two seconds is the laboratory value.
DEFAULT_WALL_ERROR_MS = 2_000

# `*fn-bpc-max-input*`; a longer prefix cannot be decoded by the profile, and
# the whole bundle is not sent -- only enough of it to cover the primary block.
MAX_BUNDLE_PREFIX_OCTETS = 65_536
# RFC 9171 4.1: a bundle is an indefinite-length array, so it ends in the
# break stop code.  fn-bpi-host-bundle-prefix returns the head and the primary
# block; a laboratory bundle carries no other block, so the break follows.
BREAK_STOP_CODE = b"\xff"


class BundleRefused(RuntimeError):
    """ACL2 refused the primary block.  Distinct from expired and uncertain."""

    def __init__(self, reason: str):
        super().__init__("ACL2 refused the primary block: {}".format(reason))
        self.reason = reason


@dataclass(frozen=True)
class BundleReport:
    """What ACL2 says about one bundle's primary block."""

    identity: bytes
    decision: str
    source: str
    creation_time: int
    sequence: int
    fragment_offset: int | None
    total_adu_length: int | None

    @property
    def key(self) -> str:
        """The staging and duplicate key: SHA-256 of the identity octets."""
        return hashlib.sha256(self.identity).hexdigest()

    @property
    def fragment(self) -> bool:
        return self.fragment_offset is not None


def observation(wall_error_ms: int = DEFAULT_WALL_ERROR_MS) -> tuple[int, int, int, bool]:
    """Two raw counters and one configured error bound.

    No epoch arithmetic and no unit conversion happens here; ACL2 does both, so
    that a host cannot quietly disagree with the model about what a DTN time is.
    """
    if not isinstance(wall_error_ms, int) or isinstance(wall_error_ms, bool) \
            or wall_error_ms < 0:
        raise BundleRefused("configured wall error bound is not a natural")
    return (time.monotonic_ns(), time.time_ns(), wall_error_ms, True)


def _eid_text(value) -> str:
    """Render ACL2's structured source endpoint ID as its RFC 9171 text form."""
    if not isinstance(value, list) or not value:
        raise frame_bridge.BridgeError("ACL2 returned an unexpected endpoint ID")
    scheme = value[0]
    if scheme == "dtn-none":
        return "dtn:none"
    if scheme == "dtn":
        octets = bytes(value[1:])
        return "dtn:" + octets.decode("ascii", "strict")
    if scheme == "ipn" and len(value) == 3:
        return "ipn:{}.{}".format(value[1], value[2])
    raise frame_bridge.BridgeError("ACL2 returned an unknown endpoint ID scheme")


def _optional(value) -> int | None:
    if value == []:
        return None
    if not isinstance(value, int) or isinstance(value, bool):
        raise frame_bridge.BridgeError("ACL2 returned a non-natural fragment field")
    return value


class BundleBridge:
    """An ACL2 session with the BP ingress host wrappers loaded.

    It shares the framing session's process: staging already needs one open, and
    a second ACL2 image would be a second opinion waiting to happen.
    """

    def __init__(self, session=None):
        self.session = frame_bridge.session(session)
        if not getattr(self.session, "bundle_host_loaded", False):
            self.session.store.call(
                '(ld "host/bp-ingress-host.lisp" :ld-error-action :return'
                ' :ld-error-triples t)')
            self.session.bundle_host_loaded = True

    def report(self, bundle: bytes,
               wall_error_ms: int = DEFAULT_WALL_ERROR_MS) -> BundleReport:
        """Identify one bundle and decide its expiry, or refuse it.

        `BundleRefused` is raised for a malformed, non-canonical, non-bundle or
        anonymously sourced primary block.  Expiry is *reported*, not raised:
        the three outcomes stay distinct and the caller decides what each means
        at its own boundary.
        """
        if not isinstance(bundle, (bytes, bytearray)) or not bundle:
            raise BundleRefused("not-a-bundle")
        prefix = bytes(bundle[:MAX_BUNDLE_PREFIX_OCTETS])
        monotonic_ns, wall_ns, error_ms, has_wall = observation(wall_error_ms)
        form = "(fn-bpi-host-bundle-report '({}) {} {} {} {})".format(
            " ".join(str(octet) for octet in prefix),
            monotonic_ns, wall_ns, error_ms, "t" if has_wall else "nil")
        value = frame_bridge.read_form(self.session.store.call(form))
        if not isinstance(value, list) or not value:
            raise frame_bridge.BridgeError("ACL2 returned an unexpected report")
        if value[0] == "refused":
            raise BundleRefused(str(value[1]) if len(value) > 1 else "unknown")
        if value[0] != "ok" or len(value) != 8:
            raise frame_bridge.BridgeError("ACL2 returned an unexpected report")
        identity = bytes(value[1])
        if not identity or any(not isinstance(o, int) or not 0 <= o <= 255
                               for o in value[1]):
            raise frame_bridge.BridgeError("ACL2 returned a non-octet identity")
        decision = str(value[2])
        if decision not in {"live", "expired", "uncertain"}:
            raise frame_bridge.BridgeError("ACL2 returned an unknown expiry verdict")
        return BundleReport(identity, decision, _eid_text(value[3]),
                            value[4], value[5],
                            _optional(value[6]), _optional(value[7]))


def ipn_eid(text: str) -> tuple:
    """`ipn:<node>.<service>` as the pair of naturals ACL2's EID holds.

    This is marshalling, not a decision: it is the exact inverse of the `ipn`
    branch of `_eid_text` above, which renders ACL2's structured EID back as
    RFC 9171 text.  Both directions are here so that neither is spelled twice,
    and neither of them decides anything -- `fn-bpp-eidp` is what says whether
    the result is an endpoint ID at all.
    """
    if not isinstance(text, str) or not text.startswith("ipn:"):
        raise BundleRefused("endpoint ID is not in the ipn scheme")
    node, _, service = text[len("ipn:"):].partition(".")
    if not node.isdigit() or not service.isdigit():
        raise BundleRefused("ipn endpoint ID is not <node>.<service>")
    return ("ipn", int(node), int(service))


def _eid_term(store, value) -> str:
    """One endpoint ID as the ACL2 term `fn-bpp-eidp` recognises.

    `bytes` is a `dtn` scheme-specific part; `("ipn", node, service)` is an
    `ipn` endpoint.  Nothing here spells a BPv7 field: these are the two
    constructor shapes of `books/bp-primary.lisp`'s EID, and the encoding of
    either is `fn-bpp-eid-value`'s.
    """
    if isinstance(value, (bytes, bytearray)):
        return "(cons :dtn '" + store.literal(bytes(value)) + ")"
    if (isinstance(value, tuple) and len(value) == 3 and value[0] == "ipn"
            and all(isinstance(part, int) and not isinstance(part, bool)
                    and part >= 0 for part in value[1:])):
        return "(list :ipn {} {})".format(value[1], value[2])
    raise BundleRefused("unsupported endpoint ID form")


def encode_primary(*, destination, source, report_to,
                   creation: int, sequence: int, lifetime: int, flags: int = 0,
                   offset=None, total=None, bridge=None) -> bytes:
    """One bundle's primary block, encoded by ACL2, for a laboratory transport.

    A stand-in transport that hands fn a bundle has to hand it a real one: the
    identity fn stages under is derived from these very octets, so octets
    Python invented would be an identity Python invented.  Nothing here spells
    a BPv7 field -- `fn-bpi-host-bundle-prefix` returns the indefinite-array
    head and the certified primary-block encoding, and the caller appends the
    break stop code standing in for the blocks a lab has none of.

    Each endpoint ID is either a `dtn` scheme-specific part as `bytes` or an
    `ipn` endpoint as `("ipn", node, service)`; `ipn_eid` parses the text form.
    """
    bridged = session(bridge)
    store = bridged.session.store

    def optional(value):
        return "nil" if value is None else str(value)

    form = ("(fn-bpi-host-bundle-prefix (fn-bpp-make-block {} 0 {} {} {} {} {} {} {} {}))"
            .format(flags, _eid_term(store, destination), _eid_term(store, source),
                    _eid_term(store, report_to), creation, sequence, lifetime,
                    optional(offset), optional(total)))
    return run_store.acl2_octets(store.call(form)) + BREAK_STOP_CODE


def session(bridge=None) -> BundleBridge:
    return bridge if isinstance(bridge, BundleBridge) else BundleBridge(bridge)
