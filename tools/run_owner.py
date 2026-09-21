#!/usr/bin/env python3
"""The mutable service owner: one process owns one store (C1-05, C1-06).

It holds the exclusive writer lock, accepts loopback NNTP connections (reads
and POST), and accepts a local Unix-socket control channel for the CLI post
path.  Every state decision is one call into the proved owner machine
(books/owner.lisp) through host/owner-host.lisp; this file moves bytes,
reports filesystem observations and clock readings, and maps outcomes to
exit codes and reply lines.

Readers observe a committed version pinned when their connection opened; a
post advances the committed version without touching any open reader; a
reader moves to the newest version only when the control channel advances it.
A served POST is a submission the book queued on the connection's read;
`drain' takes one at a time through the same durable path the control channel
uses and feeds the observed word back, and the book renders the 240 or 441.
"""
import argparse
import hashlib
import os
import selectors
import signal
import socket
import ssl
import tomllib
import sys
import time

from run_store import (ACL2_RECOVER_BASE_SECONDS, ACL2_RECOVER_PER_RECORD_SECONDS,
                       Acl2Store, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, Store,
                       StoreError, StoreFault, StoreIndeterminate, UsageParser,
                       acl2_nat, acl2_octets, acl2_result, acl2_symbol, conservative_charge,
                       durable_post, exit_code_for, group_codes, metadata,
                       post_article, validate_post_boundary)
from run_reader import acl2_boolean, acl2_octet_list
from run_feed import Journal, Session, TRAILER_BYTES  # the FNFD layout and the client half

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAX_READ = 512
MAX_OUTPUT_BACKLOG = 64 * 1024
MAX_CONTROL_LINE = 4096
DTN_EPOCH_NS = 946684800 * 1_000_000_000  # 2000-01-01T00:00:00Z


# The owner's typed words beyond the store's: each is the result of one
# fn-owner-* entry in host/owner-host.lisp.  acl2_symbol's set is the store's
# closed vocabulary and stays closed; this is the owner's.
# OBSERVE answers fn-own-observe-outcome's word and nothing else (D10-a):
# `observed`, `refused` (the host contradicted the clock it was reporting,
# and the owner has dropped it) or `invalid`.  The old `rejected` spelled
# the first and the second the same way and was computed here.
OWNER_WORDS = {b":OBSERVED", b":REFUSED", b":INVALID", b":DECLARED", b":BEGUN",
               b":CLOSED", b":OK", b":UNKNOWN", b":FED", b":TAKEN", b":IDLE"}


def acl2_owner_symbol(output):
    body = acl2_result(output).upper()
    if body in OWNER_WORDS:
        return body.decode("ascii").lower()[1:]
    return acl2_symbol(output)


def acl2_symbol_or_nat(output):
    """Owner ids come back as naturals; refusals as NIL."""
    body = output.strip()
    if not body.endswith(b"ACL2 !>"):
        raise StoreError("unexpected ACL2 owner result")
    body = body[:-len(b"ACL2 !>")].strip()
    if body == b"NIL":
        return None
    if body.isdigit():
        return int(body)
    raise StoreError("unexpected ACL2 owner result")


def acl2_octet_list_any(output):
    """A proper list of decimal naturals (not bounded to octets)."""
    body = output.strip()
    if not body.endswith(b"ACL2 !>"):
        raise StoreError("unexpected ACL2 list result")
    body = body[:-len(b"ACL2 !>")].strip()
    if body == b"NIL":
        return []
    if not (body.startswith(b"(") and body.endswith(b")")):
        raise StoreError("unexpected ACL2 list result")
    values = []
    for token in body[1:-1].split():
        if not token.isdigit():
            raise StoreError("unexpected ACL2 list result")
        values.append(int(token))
    return values


class Acl2Owner(Acl2Store):
    """The store bridge with the owner books loaded; every call is fn-owner-*."""

    def __init__(self, max_conns):
        super().__init__()
        self.max_conns = max_conns
        self.call('(include-book "books/owner")')
        self.call('(ld "host/owner-host.lisp" :ld-error-action :return :ld-error-triples t)')

    def _symbol(self, form, timeout=None):
        return acl2_owner_symbol(self.call(form, timeout=timeout))

    def _nat(self, form):
        return acl2_nat(self.call(form))

    # Store path (the same observations run_store.Store reports)
    def recover(self, records, frontier, config_records=()):
        literal = "(" + " ".join(self.literal(record) for record in records) + ")"
        config = "(" + " ".join(self.literal(record) for record in config_records) + ")"
        form = "(fn-owner-recover '{} {} '{} {} state)".format(
            literal, frontier, config, self.max_conns)
        timeout = max(ACL2_RECOVER_BASE_SECONDS + ACL2_RECOVER_PER_RECORD_SECONDS * len(records),
                      self.form_timeout(form))
        return self._symbol(form, timeout=timeout)

    def io(self, operation, result="ok"):
        return self._symbol("(fn-owner-io :{} :{} state)".format(operation, result))

    def prepare(self, msgid, payload, group_codes, obligation_id, subject, evidence, charge):
        form = "(fn-owner-prepare '" + self.literal(msgid) + " '" + self.literal(payload)
        form += " '" + self.numeric_list(group_codes) + " '" + self.literal(obligation_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " " + str(charge) + " state)"
        return self._symbol(form)

    def existing_action(self, msgid, payload, group_codes):
        form = "(fn-owner-existing-action '" + self.literal(msgid)
        form += " '" + self.literal(payload) + " '" + self.numeric_list(group_codes) + " state)"
        return self._symbol(form)

    def pending_record(self):
        return acl2_octets(self.call("(fn-owner-pending-octets state)"))

    def known_abort(self):
        return self._symbol("(fn-owner-known-abort state)")

    def refuse_reservation(self):
        return self._symbol("(fn-owner-refuse-reservation state)")

    def finish(self):
        return self._symbol("(fn-owner-finish state)")

    def config_domain(self):
        # Store.recover asks the bridge for the allocation domain; the store
        # bridge's entry reads fn-store-sn, which this image never sets.
        return self._names("(fn-owner-domain state)")

    def next_txid(self):
        return self._nat("(fn-owner-next-txid state)")

    def article_count(self):
        return self._nat("(fn-owner-article-count state)")

    # Connections
    def open(self):
        cid = acl2_symbol_or_nat(self.call("(fn-owner-open state)"))
        if cid is None:
            return None, b""
        return cid, bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

    def chunk(self, cid, octets):
        """One socket read, consumed whole by one certified call.

        `fn-own-read' (books/owner.lisp) is one fn-served-step over the
        connection's wire, session and pinned archive
        (fn-own-read-is-served-step-on-pinned-prefix).  The whole chunk is
        consumed, so there is no unconsumed suffix and no re-feeding loop
        here.  The third value says whether the read injected an article:
        the book queued the submission inside the owner, and `take' is how
        the writer moves it into the durable path.
        """
        literal = "(" + " ".join(str(byte) for byte in octets) + ")"
        outcome = self._symbol("(fn-owner-chunk {} '{} state)".format(cid, literal))
        if outcome != "ok":
            raise StoreError("owner does not know connection {}".format(cid))
        reply = bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))
        closing = acl2_boolean(self.call("(@ fn-owner-closep)"))
        submitted = acl2_boolean(self.call("(@ fn-owner-submittedp)"))
        return reply, closing, submitted

    def starttlsp(self):
        """Whether the last read asked the host for a TLS handshake.

        The decision is ACL2's: `fn-auth-starttls` (books/nntp-auth.lisp)
        emits `(:starttls)` only from the branch that also answered 382 and
        put the connection into the handshake, and it has already refused a
        second STARTTLS and one with no certificate.  This reads the answer
        off the same global the close is read from.
        """
        return acl2_boolean(self.call("(@ fn-owner-starttlsp)"))

    def set_auth(self, required, protected_only, tls_available, rows):
        """Hand ACL2 the operator's AUTHINFO policy, once, at start-up.

        `rows` are (name, principal, salt, digest, posting) with the four
        octet strings as bytes.  The host transports them; ACL2 builds the
        credential, the verifier and the configuration and owns every
        comparison made against them.
        """
        def octets(value):
            return "(" + " ".join(str(byte) for byte in value) + ")"
        literal = "(" + " ".join(
            "({} {} {} {} {})".format(octets(name), octets(principal),
                                      octets(salt), octets(digest),
                                      "t" if posting else "nil")
            for name, principal, salt, digest, posting in rows) + ")"
        outcome = self._symbol("(fn-owner-set-auth {} {} {} '{} state)".format(
            "t" if required else "nil",
            "t" if protected_only else "nil",
            "t" if tls_available else "nil", literal))
        if outcome != "ok":
            raise StoreError("the owner refused the AUTHINFO configuration; "
                             "a credential in the file is malformed")
        return outcome

    def tls_established(self, cid):
        """Re-enter the plaintext stream after the handshake (RFC 4642 2.2.2).

        A wire event, not octets: no client input can produce it, and
        `fn-auth-step` is the only reader.  It is what sets `tlsp`.
        """
        outcome = self._symbol("(fn-owner-tls-established {} state)".format(cid))
        if outcome != "ok":
            raise StoreError("owner does not know connection {}".format(cid))
        return bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

    def take(self):
        """The writer step: `taken', `taken-transit' or `idle'."""
        return self._symbol_any("(fn-owner-take state)")

    def inflight(self):
        """The submission in flight: (cid, msgid, octets, groups), all ACL2's."""
        cid = self._nat("(@ fn-owner-submit-id)")
        msgid = bytes(acl2_octet_list(self.call("(@ fn-owner-submit-msgid)")))
        octets = bytes(acl2_octet_list(self.call("(@ fn-owner-submit-octets)")))
        return cid, msgid, octets, self.submit_groups()

    def submit_groups(self):
        """The memberships ACL2 staged: the injection decision's for a POST,
        fn-peer-scope-groups' for a transit transfer, never Python's."""
        count = self._nat("(len (@ fn-owner-submit-groups))")
        if count > 64:
            raise StoreError("ACL2 reported an implausible group count")
        return [bytes(acl2_octet_list(self.call(
            "(fn-inj-nth {} (@ fn-owner-submit-groups))".format(index))))
            for index in range(count)]

    def peer_for_address(self, address):
        """The configured peer this address is, or None: ACL2 reads the record."""
        name = bytes(acl2_octet_list_any(self.call(
            "(fn-owner-peer-for-address '" + self.literal(address.encode("utf-8")) +
            " state)")) or b"")
        return name.decode("utf-8", "strict") if name else None

    def open_peer(self, peer):
        """Open a transit connection on the same listener (fn-own-open-peer)."""
        cid = acl2_symbol_or_nat(self.call(
            "(fn-owner-open-peer '" + self.literal(peer.encode("utf-8")) + " state)"))
        if cid is None:
            return None, b""
        return cid, bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

    def transit_decide(self, obligation, subject):
        """ACL2's transfer decision over the live node, and its memberships.

        Returns (kind, reason). Every check of specs/peering.md 2.2 --
        scope, loop, history, date, capacity -- is fn-peer-decide-transfer's;
        this reads its answer.
        """
        # `metadata` returns what `fn-store-identity-text` rendered, and
        # frame_bridge.identity_text is `(self, identity: bytes) -> bytes`:
        # both of these are already octets, exactly as `prepare` above passes
        # `obligation_id` straight to `literal`.  Encoding them again raised
        # AttributeError inside `drain`, which is not caught there, so the
        # OWNER PROCESS DIED on the first IHAVE any peer sent it.  Found by
        # tools/v0_matrix.py on persvati, 2026-09-20: the capability probe's
        # `IHAVE` killed both nodes and every later row became a connection
        # error (planning/evidence/v0-matrix-2026-09-20.md, node A's log).
        kind = self._symbol_any("(fn-owner-transit-decide '{} '{} state)".format(
            self.literal(obligation),
            self.literal(subject)))
        reason = self._symbol_any("(fn-owner-transit-reason state)")
        return kind, reason

    def transit_outcome(self, cid, kind, reason, word):
        form = "(fn-owner-transit-outcome {} :{} {} :{} state)".format(
            cid, kind, ":{}".format(reason) if reason != "nil" else "nil", word)
        if self._symbol_any(form) != "fed":
            raise StoreError("owner did not accept the transit outcome")
        return bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

    # -- the outbound feed (books/owner-feed.lisp) ------------------------
    #
    # Every decision below is the book's: which peers an article goes to,
    # when an offer may be sent, what the line is, what a reply code means
    # and what each journal record is.  This class marshals and nothing else.

    def feed_configure(self):
        """Rebuild the feed table from the live configuration; the peers."""
        return self._names("(fn-owner-feed-configure state)")

    def feed_peers(self):
        return self._names("(fn-owner-feed-peers state)")

    def feed_endpoint(self, peer):
        literal = "'" + self.literal(peer.encode("utf-8"))
        host = bytes(acl2_octet_list_any(self.call(
            "(fn-owner-feed-host {} state)".format(literal))) or b"")
        port = self._nat("(fn-owner-feed-port {} state)".format(literal))
        return (host.decode("utf-8", "strict") if host else None), port

    def feed_streamingp(self, peer):
        return acl2_boolean(self.call("(fn-owner-feed-streamingp '{} state)".format(
            self.literal(peer.encode("utf-8")))))

    def feed_queue_length(self, peer):
        return self._nat("(fn-owner-feed-queue-length '{} state)".format(
            self.literal(peer.encode("utf-8"))))

    def feed_connect(self, peer, conn):
        return self._symbol_any("(fn-owner-feed-connect '{} {} state)".format(
            self.literal(peer.encode("utf-8")),
            "nil" if conn is None else str(conn)))

    def feed_tick(self, peer, monotonic):
        return self._symbol_any("(fn-owner-feed-tick '{} {} state)".format(
            self.literal(peer.encode("utf-8")), monotonic))

    def feed_octets(self, peer, line, monotonic):
        return self._symbol_any("(fn-owner-feed-octets '{} '{} {} state)".format(
            self.literal(peer.encode("utf-8")), self.literal(line), monotonic))

    def feed_frames(self):
        """The FNFD frames the last feed call authorized, sealed here.

        `fn-feed-encode' takes the trailer as an argument and ACL2 built each
        frame with a zero one, so the host hashes the protected prefix and
        appends the real digest (A-CRYPTO).  Python chooses no field and no
        bound; it slices at a constant the book fixed.
        """
        count = self._nat("(len (@ fn-owner-feed-frames))")
        frames = []
        for index in range(count):
            frame = bytes(acl2_octet_list(self.call(
                "(fn-frame-item {} (@ fn-owner-feed-frames))".format(index))))
            protected = frame[:-TRAILER_BYTES]
            frames.append(protected + hashlib.sha256(protected).digest())
        return frames

    def feed_record_peers(self):
        return self._names("(fn-owner-feed-record-peers state)")

    def feed_command(self):
        return bytes(acl2_octet_list_any(self.call(
            "(fn-owner-feed-command state)")) or b"")

    def feed_replay_frame(self, peer, frame):
        digest = hashlib.sha256(frame[:-TRAILER_BYTES]).digest()
        return self._symbol_any("(fn-owner-feed-replay-frame '{} '{} '{} state)".format(
            self.literal(peer.encode("utf-8")), self.literal(frame),
            self.literal(digest)))

    def feed_restart(self):
        return self._nat("(fn-owner-feed-restart state)")

    def _symbol_any(self, form):
        body = acl2_result(self.call(form))
        text = body.decode("ascii", "replace").strip().lower()
        return text[1:] if text.startswith(":") else text

    def outcome(self, cid, word):
        """Feed the observed word back; the book renders the reply octets."""
        if self._symbol("(fn-owner-outcome {} :{} state)".format(cid, word)) != "fed":
            raise StoreError("owner did not accept the outcome")
        return bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

    def close_connection(self, cid):
        return self._symbol("(fn-owner-close {} state)".format(cid))

    def advance(self, cid):
        return acl2_symbol_or_nat(self.call("(fn-owner-advance {} state)".format(cid)))

    def begin(self, cid):
        return self._symbol("(fn-owner-begin {} state)".format(cid))

    def version(self):
        return self._nat("(fn-owner-version state)")

    def connections(self):
        flat = acl2_octet_list_any(self.call("(fn-owner-connections state)"))
        return list(zip(flat[0::2], flat[1::2]))

    def observe(self, monotonic_ms, wall_ms, error_ms, has_wall=True):
        return self._symbol("(fn-owner-observe {} {} {} {} state)".format(
            monotonic_ms, wall_ms, error_ms, "t" if has_wall else "nil"))

    def declare_group(self, name):
        return self._symbol("(fn-owner-declare-group '" + self.literal(name) + " state)")

    def group_facts(self):
        return self.call("(fn-owner-group-facts state)")


class Clock:
    """Host clock readings with a configured error bound, in the model's units."""

    def __init__(self, error_ms):
        self.error_ms = error_ms

    @staticmethod
    def milliseconds():
        """The monotonic reading the feed stamps its records and ticks with.

        The same reading fn-clock-observation takes in `observe`; the feed's
        contact window and its backoff deadline are both in these units
        (books/scheduler.lisp, fn-sched-contact-holdsp).
        """
        return time.monotonic_ns() // 1_000_000

    def observe(self, bridge):
        """Report a reading; the WORD is the owner's (fn-own-observe-outcome).

        A `refused` here is not a host error to raise on: the owner has
        dropped the clock it held, so the next decision it is asked for is
        refused for that reason and with its own text (`441 posting failed;
        this server has no usable clock reading`, DATE 503), and the next
        reading this method takes is accepted whatever it says.
        """
        monotonic_ms = time.monotonic_ns() // 1_000_000
        wall_ms = max(0, (time.time_ns() - DTN_EPOCH_NS) // 1_000_000)
        return bridge.observe(monotonic_ms, wall_ms, self.error_ms, True)


def load_credentials(path):
    """The operator's credential file, as rows of octets for ACL2.

    Format v2 (`fn principal set-password`): each `[login.NAME]` carries a
    principal id, a 16-octet salt and a 32-octet digest, all hex.  A v1
    entry -- one with `secret` in the clear -- is REFUSED by name; nothing
    here reads a password and nothing here hashes one.
    """
    if not path:
        return []
    with open(path, "rb") as handle:
        data = tomllib.load(handle)
    logins = data.get("login", {})
    if not isinstance(logins, dict):
        raise StoreError("{}: [login] is not a table".format(path))
    rows = []
    for name in sorted(logins):
        entry = logins[name]
        if not isinstance(entry, dict):
            raise StoreError("{}: [login.{}] is not a table".format(path, name))
        if "secret" in entry:
            raise StoreError(
                "cleartext-credential: {} [login.{}] stores `secret` in the "
                "clear (the format fn wrote before 2026-09-20); re-set it "
                "with `fn principal set-password {}`".format(path, name, name))
        try:
            principal = bytes.fromhex(str(entry["principal"]))
            salt = bytes.fromhex(str(entry["salt"]))
            digest = bytes.fromhex(str(entry["digest"]))
        except (KeyError, ValueError) as error:
            raise StoreError("{}: [login.{}] is malformed: {}"
                             .format(path, name, error)) from error
        if len(salt) != 16 or len(digest) != 32 or len(principal) != 32:
            raise StoreError("{}: [login.{}] has a field of the wrong length"
                             .format(path, name))
        rows.append((name.encode("ascii"), principal, salt, digest,
                     bool(entry.get("posting"))))
    return rows


class Connection:
    def __init__(self, sock, cid):
        self.sock = sock
        self.cid = cid
        self.outbuf = b""
        self.closing = False
        self.reading = True
        # RFC 4642 section 2.2.2: set when ACL2 emitted (:starttls); the
        # handshake runs once the 382 has left the socket.
        self.handshaking = False


def tls_context(cert, key):
    """The host's TLS facility (RFC 4642 section 2.3), and the whole of it.

    TLS is NOT in the model: books/nntp-auth.lisp sees plaintext octets on
    both sides of the handshake, and no theorem in this tree says anything
    about confidentiality, integrity or certificate validation.  This is the
    trusted part, named so it can be found: specs/nntp.md, "Transport
    security, and what is trusted".
    """
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    context.load_cert_chain(certfile=cert, keyfile=key)
    return context


class Feed:
    """One configured peer's outbound client connection and its FNFD journal.

    The feed machine is in ACL2 (books/peer-feed.lisp under
    books/owner-feed.lisp); this object holds the socket, the read buffer and
    the append-only journal file, and nothing else.  Three things here are
    the host's and are named because of the "one owner per decision" rule:
    opening the TCP connection, the RFC 3977 section 3.1.1 dot stuffing of an
    article block (`Session.send_block`), and the greeting plus `MODE STREAM`
    handshake, which is transport setup before the feed machine has a
    connection at all -- `fn-feed-observe` never sees a 200 or a 203.
    """

    def __init__(self, peer, journal):
        self.peer = peer
        self.journal = journal
        self.session = None
        self.conn_id = None
        self.pending_article = b""

    def close(self):
        if self.session is not None:
            self.session.close()
        self.session = None
        self.conn_id = None


class Owner:
    def __init__(self, store, bridge, records, clock, tls=None):
        self.store = store
        self.bridge = bridge
        self.records = len(records)
        self.clock = clock
        self.tls = tls
        # NNTPS: wrap before the greeting.  Off by default, so a configured
        # certificate is offered through RFC 4642 STARTTLS instead.
        self.implicit_tls = False
        self.selector = selectors.DefaultSelector()
        self.connections = {}
        self.feeds = {}
        self.feed_next_conn = 1
        self.stopping = False

    # -- NNTP connections -------------------------------------------------
    def accept_nntp(self, listener):
        try:
            sock, _ = listener.accept()
        except OSError:
            return
        if self.tls is not None and self.implicit_tls:
            # Implicit TLS (NNTPS): the handshake runs before any NNTP octet,
            # so the book sees a plaintext stream from the first byte and its
            # STARTTLS branch is never reached on this listener -- which is
            # why the owner is told the certificate is NOT available for
            # STARTTLS in that mode, and 580 is the honest answer there.
            try:
                sock = self.tls.wrap_socket(sock, server_side=True)
            except (ssl.SSLError, OSError):
                sock.close()
                return
        sock.setblocking(False)
        # One clock observation per connection, pinned into it at open: the
        # READER environment (DATE, NEWGROUPS).  The injection clock is taken
        # per read in serve(), not here.
        self.clock.observe(self.bridge)
        # The role of a connection is decided here, from the peer table, and
        # never from anything the client says (specs/peering.md 1.1): the
        # source address is matched against the configured records' auth
        # slots by ACL2, and a match opens a transit connection on this same
        # listener.  `(:principal id)` is reserved and matches nothing yet.
        peer = None
        try:
            peer = self.bridge.peer_for_address(sock.getpeername()[0])
        except (OSError, StoreError):
            peer = None
        cid, greeting = self.bridge.open_peer(peer) if peer else self.bridge.open()
        if cid is None:
            # The configured bound is reached; the owner installed nothing.
            sock.close()
            return
        conn = Connection(sock, cid)
        conn.outbuf = greeting
        self.connections[sock] = conn
        self.selector.register(sock, selectors.EVENT_READ | selectors.EVENT_WRITE, conn)

    def drop(self, conn):
        try:
            self.selector.unregister(conn.sock)
        except (KeyError, ValueError):
            pass
        self.connections.pop(conn.sock, None)
        try:
            conn.sock.close()
        finally:
            self.bridge.close_connection(conn.cid)

    def serve(self, conn, mask):
        if mask & selectors.EVENT_READ and conn.reading and not conn.closing:
            try:
                incoming = conn.sock.recv(MAX_READ)
            except (BlockingIOError, InterruptedError):
                incoming = None
            except OSError:
                self.drop(conn)
                return
            if incoming == b"":
                self.drop(conn)
                return
            if incoming:
                # The injection clock is per submission, not per connection
                # (RFC 5537 section 3.4; books/owner.lisp fn-own-read reads
                # the owner's CURRENT observation, and the connection's
                # pinned one stays the reader environment).  This is where
                # the host supplies it: one reading before the chunk that
                # may carry an article, so two posts on one connection get
                # two identities.
                self.clock.observe(self.bridge)
                # One read, one certified step: fn-own-read consumes the
                # whole chunk (books/served.lisp owns the framing loop and
                # fn-served-run-is-the-concatenated-step says the cut points
                # the network chose are invisible).
                reply, closing, submitted = self.bridge.chunk(conn.cid, list(incoming))
                conn.outbuf += reply
                if closing:
                    conn.closing = True
                # RFC 4642 section 2.2.2.  The book stopped framing at the
                # 382 (fn-served-tls-handshakingp, books/served.lisp), so
                # whatever else arrived in this read is handshake and the
                # host does not have to discard anything by itself.
                if self.bridge.starttlsp():
                    conn.handshaking = True
                    conn.reading = False
                if submitted:
                    self.drain()
        if mask & selectors.EVENT_WRITE and conn.outbuf:
            try:
                sent = conn.sock.send(conn.outbuf)
            except (BlockingIOError, InterruptedError):
                sent = 0
            except OSError:
                self.drop(conn)
                return
            conn.outbuf = conn.outbuf[sent:]
        if conn.handshaking and not conn.outbuf and not conn.closing:
            if not self.upgrade(conn):
                return
        # A peer that does not consume its output is stalled: stop taking its
        # input once the backlog reaches the bound.  It costs the owner one
        # bounded buffer and nothing else; every other connection and the
        # post path keep running.
        conn.reading = len(conn.outbuf) < MAX_OUTPUT_BACKLOG
        self.rearm(conn)

    def upgrade(self, conn):
        """The TLS handshake, and the whole of it (RFC 4642 section 2.2).

        This is the trust boundary: Python's `ssl` performs the handshake and
        no theorem in this tree says anything about it
        (docs/trust-boundary.md, specs/nntp.md).  What ACL2 decided is
        already decided -- that a handshake is owed, that the 382 was the
        right answer, that the connection served nothing behind it -- and
        what ACL2 is told afterwards is one wire event.  The socket goes
        blocking for the handshake and non-blocking again after it, because
        the framing below is a one-call-per-read loop and a partial
        handshake has no place to live in it.
        """
        conn.handshaking = False
        if self.tls is None:
            # The book advertises STARTTLS only when the host said a
            # certificate is configured, so this is unreachable unless the
            # two disagree; the connection is closed rather than served in
            # the clear after a 382.
            self.drop(conn)
            return False
        try:
            self.selector.unregister(conn.sock)
        except (KeyError, ValueError):
            pass
        try:
            conn.sock.setblocking(True)
            conn.sock = self.tls.wrap_socket(conn.sock, server_side=True)
            conn.sock.setblocking(False)
        except (ssl.SSLError, OSError):
            self.connections.pop(conn.sock, None)
            try:
                conn.sock.close()
            finally:
                self.bridge.close_connection(conn.cid)
            return False
        self.connections.pop(conn.sock, None)
        self.connections[conn.sock] = conn
        conn.reading = True
        self.bridge.tls_established(conn.cid)
        self.selector.register(conn.sock,
                               selectors.EVENT_READ | selectors.EVENT_WRITE, conn)
        return True

    def drain(self):
        """The served POST path: one submission at a time through the durable path.

        fn-own-take-submission (books/owner.lisp) moves one queued submission
        into the durable path only when nothing is in flight, no transaction
        is pending and the store is :ready; this loop is therefore serial by
        construction.  The submission's octets, Message-ID and groups are the
        injection decision's (books/injection.lisp), read back from the
        owner; the word this file observed goes back through fn-owner-outcome
        and the book renders the reply for that connection alone
        (fn-own-durable-reply-names-a-durable-record: 240 needs a consumed
        completion after the take).
        """
        while True:
            taken = self.bridge.take()
            if taken not in ("taken", "taken-transit"):
                break
            cid, msgid, payload, groups = self.bridge.inflight()
            if taken == "taken-transit":
                reply = self.transit(cid, msgid, payload)
            else:
                word = self.attempt(msgid, payload, groups)
                reply = self.bridge.outcome(cid, word)
            for conn in self.connections.values():
                if conn.cid == cid:
                    conn.outbuf += reply
                    self.rearm(conn)
                    break

    def attempt(self, msgid, payload, groups):
        """Carry ACL2's injected octets through the CLI's durable path.

        Returns the word ACL2 turns into 240 or 441.  Three outcomes stay
        distinct here and all the way out to the wire: `durable' only after
        fn-sn-finish (durable_post never invents it), `refused' for a typed
        refusal before anything was staged (a duplicate or conflicting
        Message-ID, an uncarried group, a bound), `uncertain' for an
        indeterminate commit and for a host fault, which is logged.
        """
        try:
            names = [group.decode("ascii") for group in groups]
            codes = group_codes(names, self.store)
            charge = conservative_charge(payload)
            validate_post_boundary(msgid, payload, codes, charge, self.store.config)
            existing = self.bridge.existing_action(msgid, payload, codes)
            if existing in ("duplicate", "conflict"):
                return "refused"
            if self.records >= self.store.config["max_transactions"]:
                return "refused"
            durable_post(self.store, self.bridge, self.records, msgid, payload, codes, charge)
            self.records += 1
            return "durable"
        except StoreIndeterminate as error:
            print("owner: uncertain post: {}".format(error), file=sys.stderr)
            return "uncertain"
        except UnicodeDecodeError:
            return "refused"
        except StoreError as error:
            word = self.outcome_word(error)
            if word == "fault":
                print("owner: post fault: {}".format(error), file=sys.stderr)
                return "uncertain"
            return word

    def transit(self, cid, msgid, payload):
        """One transit transfer: ACL2 decides, the store commits, ACL2 replies.

        The decision is fn-peer-decide-transfer over the LIVE node (the
        offer was advisory, RFC 4644 2.4.2); a decision that is not :want
        ends here with no attempt and the reply the decision names.  On
        :want the article goes through the SAME durable path a POST takes
        (fn-own-take-installs-the-queued-submission-whatever-it-carries),
        and the word observed there is fed back; three outcomes stay
        distinct on the wire as 235/239, 437/439 and 436-and-close.
        """
        obligation, subject, unused_evidence = metadata(msgid, payload)
        try:
            kind, reason = self.bridge.transit_decide(obligation, subject)
        except StoreError as error:
            print("owner: transit decision failed: {}".format(error), file=sys.stderr)
            return self.bridge.transit_outcome(cid, "defer", "busy", "uncertain")
        if kind != "want":
            return self.bridge.transit_outcome(cid, kind, reason, "refused")
        word = self.attempt(msgid, payload, self.bridge.submit_groups())
        return self.bridge.transit_outcome(cid, "want", "nil", word)

    def rearm(self, conn):
        events = 0
        if conn.reading and not conn.closing:
            events |= selectors.EVENT_READ
        if conn.outbuf or conn.closing:
            events |= selectors.EVENT_WRITE
        if events == 0:
            events = selectors.EVENT_READ
        try:
            self.selector.modify(conn.sock, events, conn)
        except (KeyError, ValueError):
            pass

    # -- the outbound feed --------------------------------------------------
    def feed_start(self):
        """Replay every peer's journal, fence it, then allow commands.

        specs/peering.md 3.3: the journal is folded through the feed machine
        FIRST, then one (:feed-restart peer) record is written and the feed
        is restarted, and only then may an offer go out.  A restart returns
        every in-flight entry to :queued with its attempt retired, so the
        next command for it is a CHECK or an IHAVE and never a blind
        TAKETHIS -- which is what lets the peer's own history (435/438)
        absorb the one retransmission a lost reply can cause.
        """
        peers = self.bridge.feed_configure()
        for peer in peers:
            journal = Journal(self.store.root, peer.encode("utf-8"))
            replayed = 0
            for frame in journal.records():
                if self.bridge.feed_replay_frame(peer, frame) == "ok":
                    replayed += 1
            self.feeds[peer] = Feed(peer, journal)
            print("FEED {} replayed {}".format(peer, replayed), flush=True)
        if peers:
            self.bridge.feed_restart()
            self.feed_flush()

    def feed_flush(self):
        """Durable before the effect: append what the last call authorized."""
        frames = self.bridge.feed_frames()
        if not frames:
            return
        peers = self.bridge.feed_record_peers()
        for peer, frame in zip(peers, frames):
            feed = self.feeds.get(peer)
            if feed is not None:
                feed.journal.append(frame)

    def feed_dial(self, feed):
        host, port = self.bridge.feed_endpoint(feed.peer)
        if not host or not port:
            return False
        try:
            session = Session(host, port, 5.0)
        except OSError:
            return False
        if self.bridge.feed_streamingp(feed.peer):
            session.send(b"MODE STREAM\r\n")
            session.line()
        feed.session = session
        feed.conn_id = self.feed_next_conn
        self.feed_next_conn += 1
        self.bridge.feed_connect(feed.peer, feed.conn_id)
        session.sock.setblocking(False)
        self.selector.register(session.sock, selectors.EVENT_READ,
                               ("feed", feed.peer))
        return True

    def feed_drop(self, feed):
        if feed.session is not None:
            try:
                self.selector.unregister(feed.session.sock)
            except (KeyError, ValueError):
                pass
        feed.close()
        self.bridge.feed_connect(feed.peer, None)

    def feed_write(self, feed, command):
        """The bytes one feed decision authorized, after its records."""
        if not command:
            return
        head, _, body = command.partition(b"\r\n")
        if head.startswith(b"TAKETHIS") or head.startswith(b"CHECK") \
                or head.startswith(b"IHAVE"):
            feed.session.send(head + b"\r\n")
            if body:
                feed.session.send_block(body)
        else:
            feed.session.send_block(command)

    def feed_poll(self):
        now = self.clock.milliseconds()
        for feed in list(self.feeds.values()):
            if feed.session is None:
                if self.bridge.feed_queue_length(feed.peer) > 0:
                    self.feed_dial(feed)
                continue
            try:
                if self.bridge.feed_tick(feed.peer, now) == "offer":
                    self.feed_flush()
                    self.feed_write(feed, self.bridge.feed_command())
            except OSError:
                self.feed_drop(feed)

    def feed_read(self, peer):
        feed = self.feeds.get(peer)
        if feed is None or feed.session is None:
            return
        try:
            chunk = feed.session.sock.recv(MAX_READ)
        except (BlockingIOError, InterruptedError):
            return
        except OSError:
            self.feed_drop(feed)
            return
        if not chunk:
            self.feed_drop(feed)
            return
        feed.session.buffer += chunk
        now = self.clock.milliseconds()
        while b"\r\n" in feed.session.buffer:
            line, feed.session.buffer = feed.session.buffer.split(b"\r\n", 1)
            try:
                self.bridge.feed_octets(peer, line, now)
                self.feed_flush()
                self.feed_write(feed, self.bridge.feed_command())
            except OSError:
                self.feed_drop(feed)
                return

    # -- control channel --------------------------------------------------
    def accept_control(self, listener):
        try:
            sock, _ = listener.accept()
        except OSError:
            return
        with sock:
            sock.settimeout(30)
            try:
                reply = self.control(sock)
            except (StoreError, OSError) as error:
                reply = ("{}: {}".format(self.outcome_word(error), error)).encode()
            try:
                sock.sendall(reply + b"\n")
            except OSError:
                pass

    @staticmethod
    def outcome_word(error):
        code = exit_code_for(error)
        return {EXIT_REFUSED: "refused", EXIT_UNCERTAIN: "uncertain"}.get(code, "fault")

    @staticmethod
    def read_line(sock):
        line = b""
        while not line.endswith(b"\n"):
            chunk = sock.recv(1)
            if not chunk:
                raise StoreError("control connection closed before a line")
            line += chunk
            if len(line) > MAX_CONTROL_LINE:
                raise StoreError("control line exceeds bound")
        return line[:-1]

    @staticmethod
    def read_exact(sock, length):
        data = b""
        while len(data) < length:
            chunk = sock.recv(min(65536, length - len(data)))
            if not chunk:
                raise StoreError("control payload truncated")
            data += chunk
        return data

    def control(self, sock):
        words = self.read_line(sock).split()
        if not words:
            raise StoreError("empty control line")
        command = words[0].upper()
        if command == b"POST":
            if len(words) != 5:
                raise StoreError("POST <message-id> <group,...> <charge|-> <length>")
            msgid = words[1]
            groups = [g.decode("ascii") for g in words[2].split(b",") if g]
            charge = None if words[3] == b"-" else int(words[3])
            length = int(words[4])
            if length > self.store.config["max_payload_bytes"]:
                raise StoreError("payload exceeds configured bound")
            payload = self.read_exact(sock, length)
            self.clock.observe(self.bridge)
            sequence, charge = post_article(self.store, self.bridge, self.records,
                                            msgid, payload, groups, charge)
            if sequence is None:
                return b"duplicate"
            self.records += 1
            return "committed sequence={} charge={}".format(sequence, charge).encode()
        if command == b"VERSION":
            return "version {}".format(self.bridge.version()).encode()
        if command == b"CONNECTIONS":
            pairs = self.bridge.connections()
            return ("connections " + " ".join("{}:{}".format(c, v) for c, v in pairs)).encode()
        if command == b"ADVANCE":
            if len(words) != 2:
                raise StoreError("ADVANCE <id>|ALL")
            targets = ([c for c, _ in self.bridge.connections()] if words[1].upper() == b"ALL"
                       else [int(words[1])])
            results = []
            for cid in targets:
                version = self.bridge.advance(cid)
                results.append("{}:{}".format(cid, "absent" if version is None else version))
            return ("advanced " + " ".join(results)).encode()
        if command == b"OBSERVE":
            return self.clock.observe(self.bridge).encode()
        if command == b"DECLARE-GROUP":
            if len(words) != 2:
                raise StoreError("DECLARE-GROUP <name>")
            self.clock.observe(self.bridge)
            return self.bridge.declare_group(words[1]).encode()
        if command == b"QUIT":
            self.stopping = True
            return b"stopping"
        raise StoreError("unknown control command")

    # -- loop ---------------------------------------------------------------
    def run(self, nntp_listener, control_listener):
        self.selector.register(nntp_listener, selectors.EVENT_READ, "nntp")
        self.selector.register(control_listener, selectors.EVENT_READ, "control")
        self.feed_start()
        while not self.stopping:
            for key, mask in self.selector.select(timeout=0.2):
                if key.data == "nntp":
                    self.accept_nntp(nntp_listener)
                elif key.data == "control":
                    self.accept_control(control_listener)
                elif isinstance(key.data, tuple) and key.data[0] == "feed":
                    self.feed_read(key.data[1])
                else:
                    if key.fileobj in self.connections:
                        self.serve(key.data, mask)
            self.feed_poll()
        for feed in list(self.feeds.values()):
            feed.close()
        return EXIT_OK


def terminate_on_signal(signum, unused_frame):
    raise SystemExit(128 + signum)


def main(argv=None):
    signal.signal(signal.SIGTERM, terminate_on_signal)
    parser = UsageParser(description=__doc__)
    parser.add_argument("--store", required=True)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--control", required=True, help="Unix socket path for the control channel")
    parser.add_argument("--tls-cert", help="PEM certificate; with --tls-key, STARTTLS is offered")
    parser.add_argument("--tls-key", help="PEM private key")
    parser.add_argument("--implicit-tls", action="store_true",
                        help="wrap every accepted socket before the greeting "
                             "(NNTPS); without it the certificate is offered "
                             "through RFC 4642 STARTTLS")
    parser.add_argument("--auth-file",
                        help="the credential file `fn principal set-password` "
                             "wrote (TOML); without it no login is configured")
    parser.add_argument("--auth-required", action="store_true",
                        help="RFC 4643: refuse state-changing commands with 480 "
                             "until the connection has authenticated")
    parser.add_argument("--auth-protected-only", action="store_true",
                        help="RFC 4643 section 2.3.2: answer AUTHINFO 483 until "
                             "a TLS layer is active")
    parser.add_argument("--max-connections", type=int, default=8)
    parser.add_argument("--clock-error-ms", type=int, default=1000)
    args = parser.parse_args(argv)
    if not 0 <= args.port <= 65535:
        parser.error("--port must be from 0 through 65535")
    if args.max_connections < 1:
        parser.error("--max-connections must be positive")
    if args.clock_error_ms < 0:
        parser.error("--clock-error-ms must not be negative")

    store = None
    bridge = None
    control = None
    try:
        store = Store(args.store, writable=True)
        store.acquire()
        bridge = Acl2Owner(args.max_connections)
        records = store.recover(bridge)
        clock = Clock(args.clock_error_ms)
        if clock.observe(bridge) != "observed":
            raise StoreFault("owner refused the first clock observation")
        try:
            os.unlink(args.control)
        except FileNotFoundError:
            pass
        control = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        control.bind(args.control)
        control.listen(8)
        control.setblocking(False)
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as listener:
            listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            listener.bind(("127.0.0.1", args.port))
            listener.listen(8)
            listener.setblocking(False)
            print("LISTENING {}".format(listener.getsockname()[1]), flush=True)
            print("CONTROL {}".format(args.control), flush=True)
            tls = None
            if bool(args.tls_cert) != bool(args.tls_key):
                raise StoreError("--tls-cert and --tls-key are both or neither")
            if args.tls_cert:
                tls = tls_context(args.tls_cert, args.tls_key)
            # The AUTHINFO policy reaches ACL2 once, here, and is pinned into
            # every connection at open (books/owner.lisp fn-own-open).
            bridge.set_auth(args.auth_required, args.auth_protected_only,
                            bool(args.tls_cert) and not args.implicit_tls,
                            load_credentials(args.auth_file))
            owner = Owner(store, bridge, records, clock, tls)
            owner.implicit_tls = bool(args.implicit_tls)
            return owner.run(listener, control)
    except (StoreError, OSError) as error:
        print("owner: {}".format(error), file=sys.stderr)
        return exit_code_for(error)
    finally:
        if control is not None:
            control.close()
            try:
                os.unlink(args.control)
            except OSError:
                pass
        if bridge is not None:
            bridge.close()
        if store is not None:
            store.close()


if __name__ == "__main__":
    sys.exit(main())
