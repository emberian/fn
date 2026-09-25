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
import os
import selectors
import signal
import socket
import ssl
import tomllib
import sys
import time
import traceback

from run_store import (ACL2_RECOVER_BASE_SECONDS, ACL2_RECOVER_PER_RECORD_SECONDS,
                       Acl2Store, EXIT_FAULT, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN,
                       NO_FAULTS, ScriptedFaults, Store,
                       StoreError, StoreFault, StoreIndeterminate, UsageParser,
                       acl2_keyword, acl2_nat, acl2_octets, acl2_result, acl2_symbol, conservative_charge,
                       durable_post, exit_code_for, group_codes, metadata,
                       validate_post_boundary)
from run_reader import acl2_boolean, acl2_octet_list
from tools import frame_bridge  # noqa: E402  (the profile's Lisp literal)
from feed_wire import Journal, Session, discover_journal_peers  # FNFD layout/client

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAX_READ = 512
MAX_OUTPUT_BACKLOG = 64 * 1024
MAX_CONTROL_LINE = 4096
# A fault the host cannot attribute -- one in `accept', or one raised by the
# fault handling itself -- abandons nothing, so it can repeat on every turn
# of the loop.  This many in a row and the owner stops, distinctly, instead
# of spinning.  An ATTRIBUTABLE fault is not counted: it costs its cause a
# connection or a feed, and the number of those is already bounded by
# --max-connections, so counting them would hand a peer a way to stop the
# service by faulting that many times -- which is the defect this whole
# boundary exists to remove.
MAX_UNATTRIBUTED_FAULTS = 16
DTN_EPOCH_NS = 946684800 * 1_000_000_000  # 2000-01-01T00:00:00Z


# The owner's typed words beyond the store's: each is the result of one
# fn-owner-* entry in host/owner-host.lisp.  acl2_symbol's set is the store's
# closed vocabulary and stays closed; this is the owner's.
# OBSERVE answers fn-own-observe-outcome's word and nothing else (D10-a):
# `observed`, `refused` (the host contradicted the clock it was reporting,
# and the owner has dropped it) or `invalid`.  The old `rejected` spelled
# the first and the second the same way and was computed here.
OWNER_WORDS = {b":OBSERVED", b":REFUSED", b":INVALID", b":DECLARED", b":BEGUN",
               b":CLOSED", b":OK", b":UNKNOWN", b":FED", b":TAKEN", b":IDLE",
               b":TAKEN-CONTROL", b":SUBMITTED", b":BUSY", b":ACCEPTED",
               b":DUPLICATE", b":UNCERTAIN", b":ABSENT", b":INSTALLED",
               # The fourth outcome (books/owner-fault.lisp): a host fault,
               # answered distinctly from accepted, refused and uncertain.
               b":FAULTED"}


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
        # books/owner-fault includes books/owner; `fn-own-fault' is what the
        # host-fault boundary in `Owner.guard' below calls.
        self.call('(include-book "books/owner-fault")')
        self.call('(include-book "books/codec-attach")')
        self.call('(ld "host/owner-host.lisp" :ld-error-action :return :ld-error-triples t)')
        self.call('(ld "host/feed-filename-host.lisp" :ld-error-action :return :ld-error-triples t)')

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

    def install_profile(self, config):
        # The store's persisted profile, handed back as the values ACL2
        # decoded at open; ACL2 derives the transaction budget from it.
        values = frame_bridge._lisp_literal(config["profile"])
        return self._symbol("(fn-owner-install-profile '{} state)".format(values))

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

    def config_generation(self):
        return self._nat("(fn-owner-config-generation state)")

    def config_served(self):
        return self._names("(fn-owner-config-served state)")

    def config_domain(self):
        # Store.recover asks the bridge for the allocation domain; the store
        # bridge's entry reads fn-store-sn, which this image never sets.
        return self._names("(fn-owner-domain state)")

    def reconfigure_group(self, cid, action, name):
        """Stage one ACL2-owned group configuration record for a live client.

        The caller carries a connection id, action and UTF-8 name.  The host
        builds the delta, checks its generation pin and exposes only the
        admitted record octets; it does not mutate the configuration yet.
        """
        kind = {"create": ":create-group", "retire": ":remove-group"}.get(action)
        if kind is None:
            raise StoreError("unknown group reconfiguration action")
        literal = self.literal(name.encode("utf-8", "strict"))
        status = self._symbol_any("(fn-owner-reconfigure {} {} '{} state)".format(
            int(cid), kind, literal))
        if status == "staged":
            record = bytes(acl2_octet_list(self.call(
                "(fn-owner-reconfigure-octets state)")))
            generation = self._nat("(fn-owner-config-generation state)") + 1
            return "staged", generation, record
        if status == "refused":
            return "refused", acl2_keyword(self.call(
                "(fn-owner-reconfigure-reason state)")), None
        raise StoreFault("unexpected owner reconfiguration outcome: {}".format(status))

    def complete_reconfigure(self, generation):
        outcome = self._symbol_any("(fn-owner-reconfigure-complete {} state)".format(
            int(generation)))
        if outcome != "durable":
            raise StoreFault("owner refused durable configuration completion")
        return outcome

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
        """The writer step: `taken', `taken-control', `taken-transit' or `idle'."""
        return self._symbol_any("(fn-owner-take state)")

    def control_submit(self, msgid, groups, payload):
        """One ACL2 control-submission event over exact authored octets."""
        group_literal = "(" + " ".join(
            "(" + " ".join(str(byte) for byte in group) + ")" for group in groups) + ")"
        form = "(fn-owner-control-submit '{} '{} '{} state)".format(
            self.literal(msgid), group_literal, self.literal(payload))
        return self._symbol_any(form)

    def submit_id(self):
        """The connection the submission in flight belongs to.

        Read on its own, before anything else about the submission, so that
        the fault boundary in `Owner.drain' always knows WHOSE fault it is:
        the rest of `inflight' is exactly where the 2026-09-20 crash was.
        """
        return self._nat("(@ fn-owner-submit-id)")

    def inflight(self):
        """The submission in flight: (cid, msgid, octets, groups), all ACL2's."""
        cid = self.submit_id()
        msgid = bytes(acl2_octet_list(self.call("(@ fn-owner-submit-msgid)")))
        octets = bytes(acl2_octet_list(self.call("(@ fn-owner-submit-octets)")))
        return cid, msgid, octets, self.submit_groups()

    def submit_groups(self):
        """The memberships ACL2 staged: the injection decision's for a POST,
        fn-peer-scope-groups' for a transit transfer, never Python's.

        ONE SHAPE: octets per group, on both paths.  The transit path staged
        strings here until 2026-09-21 and this call raised RuntimeError on
        the first transfer, inside `Owner.drain', which had no boundary --
        the owner process died.  host/owner-host.lisp `fn-owner-transit-decide`
        now renders them, and `Owner.guard` below means a shape this does not
        expect costs one connection instead of the service.
        """
        count = self._nat("(len (@ fn-owner-submit-groups))")
        if count > 64:
            raise StoreError("ACL2 reported an implausible group count")
        return [bytes(acl2_octet_list(self.call(
            "(fn-inj-nth {} (@ fn-owner-submit-groups))".format(index))))
            for index in range(count)]

    def fault(self, cid):
        """The host-fault boundary: `fn-own-fault' (books/owner-fault.lisp).

        The host has caught something it did not expect while serving `cid'.
        It decides nothing here: the reply line, the close and what the owner
        forgets are all the model's, and this reads them back the way every
        served read is read.  The word is `faulted' when there was a
        connection to answer and `unknown' when there was not.
        """
        word = self._symbol("(fn-owner-fault {} state)".format(cid))
        return word, bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

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

    def transit_evidence(self):
        return bytes(acl2_octet_list(self.call("(fn-owner-transit-evidence state)")))

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

    def feed_has_queued(self, peer):
        """Is there an entry the feed could OFFER: `fn-feed-head-queued`.

        Not the queue length: an entry in flight is in the queue, and
        dialling for one the feed cannot offer is what filled a peer's
        connection table after a lost reply."""
        return acl2_boolean(self.call("(fn-owner-feed-has-queued '{} state)".format(
            self.literal(peer.encode("utf-8")))))

    def feed_backoff_ms(self, peer):
        """The peer record's outbound backoff, which ACL2 reads, not Python."""
        return self._nat("(fn-owner-feed-backoff-ms '{} state)".format(
            self.literal(peer.encode("utf-8"))))

    def feed_lost(self, peer, monotonic):
        """The connection to one peer is gone; ACL2 decides what that means.

        `fn-own-feed-lost` applies `fn-feed-lost` to THAT PEER alone: the
        in-flight entry returns to :queued with one more attempt and a
        backoff, and the connection is forgotten.  The host reports the
        event and the time; it does not decide to requeue, and it never
        reaches for `fn-own-feed-restart-all`, whose per-table settle would
        resolve another peer's genuinely in-flight entry and cause the
        second transfer K5 forbids.
        """
        return self._symbol_any(
            "(fn-owner-feed-lost '" + self.literal(peer.encode("utf-8")) +
            " {} state)".format(int(monotonic)))

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

    def trailer(self, prefix):
        """The integrity trailer over a protected prefix, computed by ACL2.

        `fn-frame-trailer' (books/frame-trailer.lisp) is `fn-frame-digest',
        realised by `fn-sha256' through `books/crypto-attach.lisp'.  Until
        `w11/one-owner' this method did not exist and the two call sites
        below ran `hashlib.sha256', which made the FNFD trailer a third
        owner of one decision beside `tools/frame_bridge.py' and
        `host/native/io.lisp'.
        """
        octets = "'(" + " ".join(str(byte) for byte in prefix) + ")"
        return bytes(acl2_octet_list(self.call(
            "(fn-frame-trailer {})".format(octets))))

    def feed_frames(self):
        """ACL2 seals each authorized FNFD record, including prefix choice."""
        count = self._nat("(len (@ fn-owner-feed-frames))")
        return [bytes(acl2_octet_list(self.call(
            "(fn-owner-feed-sealed-frame {} state)".format(index))))
                for index in range(count)]

    def feed_record_peers(self):
        return self._names("(fn-owner-feed-record-peers state)")

    def feed_command(self):
        status = self._symbol_any("(fn-owner-feed-command-status state)")
        if status != "ok":
            raise StoreError("ACL2 refused outbound feed framing: {}".format(status))
        return bytes(acl2_octet_list_any(self.call(
            "(fn-owner-feed-command state)")) or b"")

    def feed_journal_prefix_size(self):
        return self._nat("*fn-feed-journal-prefix-size*")

    def feed_filename_components(self, peer):
        """ACL2's only peer-label to filesystem-component conversion."""
        octets = peer if isinstance(peer, bytes) else peer.encode("utf-8")
        literal = self.literal(octets)
        if not acl2_boolean(self.call("(fn-feed-filename-host-okp '{})".format(literal))):
            raise StoreFault("ACL2 refused FNFD peer filename")
        count = self._nat("(fn-feed-filename-host-count '{})".format(literal))
        if count < 1 or count > self._nat("(fn-feed-filename-host-max-components)"):
            raise StoreFault("ACL2 returned no FNFD filename components")
        return tuple(
            bytes(acl2_octet_list(self.call(
                "(fn-feed-filename-host-component '{} {} )".format(literal, index))))
            for index in range(count))

    def feed_filename_max_v1_chunks(self):
        return self._nat("(fn-feed-filename-host-max-v1-chunks)")

    def feed_filename_decode(self, components):
        literal = "(" + " ".join(self.literal(component) for component in components) + ")"
        result = self.call("(fn-feed-filename-host-decode '{})".format(literal))
        if acl2_owner_symbol(result) == "bad":
            raise StoreFault("ACL2 refused FNFD filename components")
        return bytes(acl2_octet_list(result))

    def feed_journal_prefix(self, prefix):
        result = self._symbol_any("(fn-feed-journal-prefix '{} )".format(
            self.literal(prefix)))
        return int(result) if result.isdigit() else result

    def feed_journal_begin(self):
        self.call("(f-put-global 'fn-owner-feed-safe-offset 0 state)")

    def feed_journal_scan(self, peer, prefix, frame):
        return self._symbol_any("(fn-owner-feed-journal-scan '{} '{} '{} state)".format(
            self.literal(peer), self.literal(prefix), self.literal(frame)))

    def feed_journal_offset(self):
        return self._nat("(@ fn-owner-feed-safe-offset)")

    def feed_journal_wrap(self, frame):
        return bytes(acl2_octet_list(self.call("(fn-feed-journal-wrap '{})".format(
            self.literal(frame)))))

    def feed_journal_step(self, phase, event):
        return self._symbol_any("(fn-feed-journal-phase-step :{} :{})".format(
            phase, event))

    def feed_restart(self):
        return self._nat("(fn-owner-feed-restart state)")

    def submission_intent(self, evidence, generation, txid):
        """ACL2's capacity verdict and exact pre-commit intent frames."""
        return self._symbol_any(
            "(fn-owner-submission-intent '{} {} {} state)".format(
                self.literal(evidence), generation, txid))

    def submission_resolution(self, word, evidence, generation, txid):
        """ACL2's exact commit/abort projection for the in-flight submit."""
        return self._symbol_any(
            "(fn-owner-submission-resolution :{} '{} {} {} state)".format(
                word, self.literal(evidence), generation, txid))

    def feed_reconcile_next(self):
        """Resolve one recovered intent from the authoritative owner node."""
        return self._symbol_any("(fn-owner-feed-reconcile-next state)")

    def feed_reconcile_apply(self):
        return self._symbol_any("(fn-owner-feed-reconcile-apply state)")

    def feed_journal_peer_valid(self, peer):
        return acl2_boolean(self.call(
            "(fn-owner-feed-journal-peer-validp '{} state)".format(
                self.literal(peer.encode("utf-8")))))

    def _symbol_any(self, form):
        body = acl2_result(self.call(form))
        text = body.decode("ascii", "replace").strip().lower()
        return text[1:] if text.startswith(":") else text

    def outcome(self, cid, word):
        """Feed the observed word back; the book renders the reply octets."""
        if self._symbol("(fn-owner-outcome {} :{} state)".format(cid, word)) != "fed":
            raise StoreError("owner did not accept the outcome")
        return bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))

    def control_outcome(self, word):
        """The ACL2 projection of accepted/refused/uncertain/duplicate."""
        return self._symbol_any("(fn-owner-control-outcome :{} state)".format(word))

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
    def __init__(self, sock, cid, peer=None):
        self.sock = sock
        self.cid = cid
        # The peer record this connection was resolved to at accept, or None
        # for a reader.  Recorded so the operator log can say which role the
        # owner gave the connection: it said `reader` for every connection,
        # including the ones ACL2 opened with fn-own-open-peer, and that is
        # part of why a peer-shaped reader went unnoticed for a wave.
        self.peer = peer
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
    opening the TCP connection and the greeting plus `MODE STREAM` handshake,
    which is transport setup before the feed machine has a
    connection at all -- `fn-feed-observe` never sees a 200 or a 203.
    """

    def __init__(self, peer, journal):
        self.peer = peer
        self.journal = journal
        self.session = None
        self.conn_id = None
        self.pending_article = b""
        # When the host may next open a socket for this peer. The interval
        # is the peer record's own outbound backoff (ACL2 reads it); only
        # the waiting is the host's. The feed machine's backoff cannot do
        # this job: it gates `fn-feed-selection`, which needs a connection
        # that a dial has not made yet.
        self.next_dial = 0.0

    def close(self):
        if self.session is not None:
            self.session.close()
        self.session = None
        self.conn_id = None


class Owner:
    def __init__(self, store, bridge, records, clock, tls=None, faults=NO_FAULTS):
        self.store = store
        self.bridge = bridge
        self.records = len(records)
        self.clock = clock
        self.tls = tls
        # The documented test-only injector (tools/run_store.py FaultPoints).
        # Production passes NO_FAULTS and no served path holds a branch.
        self.faults = faults
        # A fault the host could not attribute to a connection or a feed is
        # the only one that costs its cause nothing, so it is the only one
        # counted; see `take_fault'.
        self.unattributed_faults = 0
        self.exit_code = EXIT_OK
        # NNTPS: wrap before the greeting.  Off by default, so a configured
        # certificate is offered through RFC 4642 STARTTLS instead.
        self.implicit_tls = False
        self.selector = selectors.DefaultSelector()
        self.connections = {}
        self.feeds = {}
        self.feed_next_conn = 1
        self.feed_uncertain = False
        # A configuration record may have reached stable storage before its
        # write reports an error.  Its staged ACL2 transaction must never be
        # published speculatively; this process stops and recovers the actual
        # durable prefix instead.
        self.config_uncertain = False
        self.store_uncertain = False
        self.uncertain_reply_cid = None
        self.stopping = False

    # -- NNTP connections -------------------------------------------------
    def accept_nntp(self, listener):
        """One accepted connection, and never the end of the service.

        Everything below can raise: the bridge, the TLS handshake, the
        peer-table read. An unexpected error here used to unwind through
        `run` and the OWNER PROCESS EXITED at accept, which reaches the
        client as a closed connection and reaches every later client as
        `ConnectionRefusedError` -- one connection deciding the lifetime of
        a service that was serving readers.

        `w11/twonode-feed` contained that with a try/except of its own right
        here, printing `ACCEPT-FAULT` and the traceback. This function no
        longer catches, because `run` calls it under the ONE host-fault
        boundary below, which prints the same word with the same traceback
        and also counts it: an accept fault abandons nothing, so it is the
        one kind that can repeat on every turn of the loop, and the count is
        what bounds it. `ACCEPT-FAULT` is a defect signal, not an outcome.
        """
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
            # SAY SO.  This refusal writes no greeting and raises nothing, so
            # before this line a node whose table was full answered every
            # client with an immediate close and printed not one word: gate
            # `0ec08bb` recorded 180 of them over 90 s against a node that
            # was alive, with `ACCEPT-FAULT` absent and no tap session, and
            # the cause was diagnosed three runs later.  A server that
            # refuses everything has to be able to say why.
            print("ACCEPT-REFUSED {}: the owner holds {} of {} connections"
                  .format(peer or "reader", len(self.bridge.connections()),
                          self.bridge.max_conns),
                  file=sys.stderr, flush=True)
            sock.close()
            return
        conn = Connection(sock, cid, peer)
        conn.outbuf = greeting
        try:
            self.connections[sock] = conn
            self.selector.register(sock,
                                   selectors.EVENT_READ | selectors.EVENT_WRITE, conn)
        except BaseException:
            # The owner has already installed the connection.  A host that
            # gives up here without telling ACL2 leaks a slot out of
            # `fn-own-conns` for the lifetime of the process, and the bound
            # is what closes every later accept.
            self.connections.pop(sock, None)
            try:
                sock.close()
            finally:
                self.bridge.close_connection(cid)
            raise

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
        if self.feed_uncertain:
            return
        if self.store_uncertain and conn.cid != self.uncertain_reply_cid:
            return
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
                # The documented test-only injection point for the served
                # read.  Production passes NO_FAULTS, so there is no branch
                # here at all; tests/test_owner.py uses it to show that a
                # fault on one connection costs only that connection.
                self.faults.at("owner:served-read")
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
                    if self.feed_uncertain:
                        return
                    # `drain' may have faulted THIS connection (the
                    # submission it carried was this connection's), in which
                    # case the socket is closed and the owner has forgotten
                    # it; there is nothing left of it to write to or rearm.
                    if conn.sock not in self.connections:
                        return
        if mask & selectors.EVENT_WRITE and conn.outbuf:
            try:
                sent = conn.sock.send(conn.outbuf)
            except (BlockingIOError, InterruptedError):
                sent = 0
            except OSError:
                if (self.store_uncertain and
                        conn.cid == self.uncertain_reply_cid):
                    self.discard(conn, closed_by_model=True)
                    self.stopping = True
                    self.exit_code = EXIT_UNCERTAIN
                else:
                    self.drop(conn)
                return
            conn.outbuf = conn.outbuf[sent:]
        if (self.store_uncertain and
                conn.cid == self.uncertain_reply_cid and
                not conn.outbuf):
            # The uncertain outcome is the last logical owner mutation in
            # this image.  Close only the socket, then require recovery in a
            # fresh process instead of sending another event to ACL2.
            self.discard(conn, closed_by_model=True)
            self.stopping = True
            self.exit_code = EXIT_UNCERTAIN
            return
        if conn.handshaking and not conn.outbuf and not conn.closing:
            if not self.upgrade(conn):
                return
        # The book said this connection ENDS (`fn-served-closingp`: QUIT's
        # 205, a fatal 400, the transit 436-and-close), and the host has to
        # act on that once the reply has left the socket.  Before this, a
        # closing connection was armed for write, never read again and never
        # dropped: its socket stayed open, its slot stayed in `fn-own-conns`
        # for the lifetime of the process, and `--max-connections` QUITs
        # later `fn-own-open` answered NIL to every accept.  Measured on the
        # laptop at `--max-connections 4`: four QUITs, then every connection
        # closed at accept with no greeting and no log line.
        if conn.closing and not conn.outbuf:
            self.drop(conn)
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
        no theorem in this tree says anything about it (specs/nntp.md,
        "Transport security, and what is trusted"; the audit row is
        specs/nntp-audit.md section 2.3).  This line named
        docs/trust-boundary.md until 2026-09-21; no such file has ever
        existed, and the boundary it pointed at is the section named here.
        What ACL2 decided is
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

    # -- the host-fault boundary --------------------------------------------
    #
    # THE DEFECT.  Every exception raised anywhere under the serve loop used
    # to unwind through `serve' and `run' and out of `main': ONE PEER'S INPUT
    # ENDED THE SERVICE FOR EVERY CONNECTION.  It was not hypothetical.
    # tools/v0_matrix.py hit it twice on persvati on 2026-09-20, both inside
    # `drain', and node B's death is the single cause behind 22 transit rows,
    # 4 feed rows, 6 crash rows and 1 concurrency row of the 190-row matrix.
    #
    # WHERE THE BOUNDARY IS, AND WHY.  Per EVENT, in `run's dispatch, with a
    # second one per SUBMISSION inside `drain'.
    #
    #   * Per event and not per connection, because an accept, a feed read
    #     and a feed poll have no connection at all and a fault in one of
    #     them ended the process exactly as surely.  One selector event is
    #     also the granularity at which resuming is sound: between events the
    #     owner is quiescent, and each transition it just ran is proved to
    #     touch one connection (fn-own-read-touches-only-its-connection,
    #     fn-own-outcome's "no other connection is touched at all").
    #   * Per submission inside `drain', because the submission `drain' is
    #     carrying belongs to a DIFFERENT connection than the one whose read
    #     called it.  Faulting the reader for the poster's failure would
    #     close the wrong socket AND leave the poster's submission in flight,
    #     and `fn-own-take-submission' takes nothing while one is in flight
    #     -- so every OTHER connection would lose the post path too.
    #
    # WHAT THE HOST DECIDES HERE: whether it still trusts this socket.  That
    # is all.  The reply code, the fact that it is a fourth outcome and not a
    # refusal, and everything the owner forgets are `fn-own-fault'
    # (books/owner-fault.lisp), reached through `fn-owner-fault'.
    def guard(self, site, work, conn=None, feed=None):
        """Run one unit of the loop; a fault in it costs at most `conn'/`feed'."""
        if self.feed_uncertain:
            return
        try:
            work()
        except (SystemExit, KeyboardInterrupt):
            raise
        except BaseException as error:   # noqa: BLE001 -- the whole point
            self.take_fault(site, error, conn=conn, feed=feed)
        else:
            self.unattributed_faults = 0

    # The site's established log word.  `w11/twonode-feed` contained the
    # accept and the feed faults first and named them; its evidence, its
    # handoff, `tools/twonode_gate.py`'s log documentation and a live board
    # ASK all read for these two words, so the vocabulary is kept and only
    # the code path is folded into one.  A served read and a drained
    # submission are this lane's and are `FAULT`.
    FAULT_WORDS = {"accept": "ACCEPT-FAULT",
                   "feed-read": "FEED-FAULT", "feed-poll": "FEED-FAULT"}

    def take_fault(self, site, error, conn=None, feed=None, cid=None):
        """Record one fault distinctly and abandon exactly what caused it."""
        if self.feed_uncertain:
            # Preserve the persistence outcome even through a generic host
            # boundary. Do not precede it with a contradictory FAULT label.
            print("FEED-UNCERTAIN {}: recovery required".format(site),
                  file=sys.stderr, flush=True)
            traceback.print_exception(type(error), error, error.__traceback__,
                                      file=sys.stderr)
            self.stopping = True
            self.exit_code = EXIT_UNCERTAIN
            return
        named = "cid={}".format(conn.cid if conn is not None else cid) \
            if (conn is not None or cid is not None) \
            else (feed.peer if feed is not None else "-")
        # A fault word, never `refused' and never `uncertain': the three
        # outcomes are answers about an ARTICLE and this is not one.  A log
        # reader, like the wire, can tell the four apart.  The traceback goes
        # with it so the diagnosis survives in the server log.
        print("{} {} {} {}: {}".format(
            self.FAULT_WORDS.get(site, "FAULT"), site, named,
            type(error).__name__, error), file=sys.stderr, flush=True)
        traceback.print_exception(type(error), error, error.__traceback__,
                                  file=sys.stderr)
        sys.stderr.flush()
        if self.bridge.poisoned:
            # The ACL2 image IS the server: every decision the owner makes is
            # a call into it.  With the bridge lost there is nothing left to
            # serve with, so the owner stops -- distinctly, with the fault
            # code -- rather than answering anything out of Python.
            print("owner: the ACL2 bridge is unusable; stopping", file=sys.stderr)
            self.stopping = True
            self.exit_code = EXIT_FAULT
            return
        if conn is None and cid is not None:
            conn = next((c for c in self.connections.values() if c.cid == cid), None)
        if conn is not None:
            self.fault_connection(conn)
            self.unattributed_faults = 0
            return
        if cid is not None:
            # The poster has already gone, but the owner must still forget
            # the submission or the writer is wedged for everyone.
            self.ask_for_fault(cid)
            self.unattributed_faults = 0
            return
        if feed is not None:
            self.guard_drop_feed(feed)
            self.unattributed_faults = 0
            return
        self.unattributed_faults += 1
        if self.unattributed_faults >= MAX_UNATTRIBUTED_FAULTS:
            print("owner: {} faults with nothing to abandon; stopping".format(
                self.unattributed_faults), file=sys.stderr)
            self.stopping = True
            self.exit_code = EXIT_FAULT

    def ask_for_fault(self, cid):
        """`fn-own-fault' for one connection id; the reply octets, or none."""
        try:
            word, reply = self.bridge.fault(cid)
        except (SystemExit, KeyboardInterrupt):
            raise
        except BaseException as error:   # noqa: BLE001
            print("owner: no fault reply for cid={}: {}".format(cid, error),
                  file=sys.stderr, flush=True)
            return None
        return reply if word == "faulted" else b""

    def fault_connection(self, conn):
        """Abandon one connection on ACL2's terms; keep serving every other.

        One send attempt, not a flush loop: the reply is one short line, a
        socket that cannot take it is one whose reader has stopped, and a
        loop here would be unbounded work driven by the peer that faulted.
        """
        reply = self.ask_for_fault(conn.cid)
        if reply:
            try:
                conn.sock.send(reply)
            except OSError:
                pass
        self.discard(conn, closed_by_model=reply is not None)

    def discard(self, conn, closed_by_model):
        """Forget the socket.  `fn-own-fault' has already closed the
        connection in the owner, so the bridge is NOT asked to close it
        again; it is asked only when the fault reply could not be obtained
        and the owner may therefore still be holding it."""
        try:
            self.selector.unregister(conn.sock)
        except (KeyError, ValueError):
            pass
        self.connections.pop(conn.sock, None)
        try:
            conn.sock.close()
        except OSError:
            pass
        if not closed_by_model:
            try:
                self.bridge.close_connection(conn.cid)
            except (StoreError, OSError, RuntimeError):
                pass

    def guard_drop_feed(self, feed):
        """A feed that faulted is disconnected; its journal and its queue are
        untouched, so the next dial replays them (specs/peering.md 3.3)."""
        try:
            self.feed_drop(feed)
        except (SystemExit, KeyboardInterrupt):
            raise
        except BaseException:   # noqa: BLE001
            self.feeds.pop(feed.peer, None)

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
            # WHOSE submission, first and on its own: the rest of `inflight'
            # is exactly where the transit crash was, and a fault boundary
            # that does not know the connection cannot name one.
            cid = self.bridge.submit_id()
            try:
                self.faults.at("owner:drain")
                _, msgid, payload, groups = self.bridge.inflight()
                if taken == "taken-transit":
                    reply = self.transit(cid, msgid, payload)
                else:
                    intent = self.submission_intent(self.bridge.prov_post())
                    word = (self.attempt(msgid, payload, groups)
                            if intent is not None else "refused")
                    if intent is not None:
                        self.submission_resolution(word, intent)
                    reply = self.bridge.outcome(cid, word)
            except (SystemExit, KeyboardInterrupt):
                raise
            except BaseException as error:   # noqa: BLE001 -- the whole point
                # This connection's submission ends here, with the fourth
                # outcome.  `fn-own-fault' clears the in-flight slot, so the
                # next turn of this loop takes the NEXT connection's
                # submission: one peer's fault does not cost the others the
                # post path.  Bounded: each fault also closes a connection
                # and a closed connection's queued submissions go with it.
                self.take_fault("drain", error, cid=cid)
                if self.stopping:
                    return
                continue
            for conn in self.connections.values():
                if conn.cid == cid:
                    conn.outbuf += reply
                    if self.store_uncertain:
                        conn.reading = False
                        conn.closing = True
                        self.uncertain_reply_cid = cid
                    self.rearm(conn)
                    break
            else:
                if self.store_uncertain:
                    self.stopping = True
            if self.store_uncertain:
                return

    def submission_intent(self, evidence):
        """Make the exact acceptance intent durable before store mutation.

        ACL2 fixes the original target set, object identity and capacity
        verdict.  The transaction id distinguishes retries even when the
        configuration generation and clock observation are unchanged.
        """
        generation = self.bridge.config_generation()
        txid = self.bridge.next_txid()
        self.faults.at("owner:preintent")
        result = self.bridge.submission_intent(evidence, generation, txid)
        if result != "ready":
            if result in ("capacity", "refused"):
                return None
            raise StoreFault("unexpected feed intent result: {}".format(result))
        self.feed_flush()
        self.faults.at("owner:intent-barrier")
        return evidence, generation, txid

    def submission_resolution(self, word, intent):
        """Durably resolve this exact intent before queueing or replying."""
        evidence, generation, txid = intent
        kind = self.bridge.submission_resolution(word, evidence, generation, txid)
        if kind not in ("feed-commit", "feed-abort", "uncertain", "none"):
            raise StoreFault("unexpected feed intent resolution: {}".format(kind))
        if kind == "uncertain":
            # The durable intent deliberately remains unresolved. Recovery
            # compares it with the authoritative store before any new work.
            return kind
        self.feed_flush()
        self.faults.at("owner:{}-barrier".format(
            "commit" if kind == "feed-commit" else "abort"))
        return kind

    def attempt(self, msgid, payload, groups, charge=None, evidence=None):
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
            charge = charge if charge is not None else conservative_charge(payload)
            validate_post_boundary(msgid, payload, codes, charge, self.store.config)
            existing = self.bridge.existing_action(msgid, payload, codes)
            if existing == "duplicate":
                return "duplicate"
            if existing == "conflict":
                return "refused"
            if self.records >= self.store.config["max_transactions"]:
                return "refused"
            durable_post(self.store, self.bridge, self.records, msgid, payload,
                         codes, charge, evidence=evidence)
            self.records += 1
            return "durable"
        except StoreIndeterminate as error:
            print("owner: uncertain post: {}".format(error), file=sys.stderr)
            self.store_uncertain = True
            self.exit_code = EXIT_UNCERTAIN
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
        evidence = self.bridge.transit_evidence()
        # The intent and the store record bind the same ACL2-derived transit
        # provenance.  The host transports it and makes no provenance choice.
        intent = self.submission_intent(evidence)
        word = (self.attempt(msgid, payload, self.bridge.submit_groups(),
                             evidence=evidence)
                if intent is not None else "refused")
        if intent is not None:
            self.submission_resolution(word, intent)
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
        try:
            # Journal files are durable obligations, including for a peer
            # removed or disabled after acceptance.  Discover those files in
            # addition to current configuration; ACL2 validates each name and
            # every decoded record binds itself to that peer.  A dormant peer
            # remains journal-only until configuration supplies an endpoint
            # again, at which point the same file replays into its feed.
            journal_peers = list(peers)
            for peer in discover_journal_peers(self.store.root, self.bridge):
                if peer not in journal_peers:
                    journal_peers.append(peer)
            for peer in journal_peers:
                journal = Journal(self.store.root, peer.encode("utf-8"),
                                  self.bridge, faults=self.faults)
                self.feeds[peer] = Feed(peer, journal)
                state = "configured" if peer in peers else "dormant"
                print("FEED {} replayed {} {}".format(
                    peer, journal.replayed, state), flush=True)

            # The store was completely and authoritatively recovered before
            # feed_start.  Resolve every unmatched pre-commit intent against
            # its exact binding and retention evidence, append that resolution
            # durably to the original peer journal, then apply the same record
            # to the live feed fold.  Partial store evidence fences startup.
            while True:
                resolution = self.bridge.feed_reconcile_next()
                if resolution == "done":
                    break
                if resolution == "uncertain":
                    raise StoreIndeterminate(
                        "feed intent cannot be resolved from recovered store")
                if resolution not in ("feed-commit", "feed-abort"):
                    raise StoreFault("unexpected feed reconciliation: " + resolution)
                self.feed_flush()
                if self.bridge.feed_reconcile_apply() != "ok":
                    raise StoreFault("ACL2 refused recovered feed resolution")
            if peers:
                self.bridge.feed_restart()
                self.feed_flush()
        except StoreIndeterminate as error:
            self.feed_fence(error)
            raise

    def feed_fence(self, error):
        """An ambiguous journal write fences the entire current owner image.

        The logical feed may already have advanced. Only process restart,
        physical prefix recovery and its barriers may make it writable again.
        """
        self.feed_uncertain = True
        self.stopping = True
        self.exit_code = EXIT_UNCERTAIN
        print("FEED-UNCERTAIN recovery required: {}".format(error),
              file=sys.stderr, flush=True)

    def feed_flush(self):
        """Durable before the effect; failure forbids every later mutation."""
        if self.feed_uncertain:
            raise StoreIndeterminate("FNFD journal requires owner restart")
        if self.config_uncertain:
            raise StoreIndeterminate("configuration journal requires owner restart")
        try:
            frames = self.bridge.feed_frames()
            if not frames:
                return
            peers = self.bridge.feed_record_peers()
            if len(peers) != len(frames):
                raise StoreFault("FNFD frame/peer bridge result mismatch")
            for peer, frame in zip(peers, frames):
                feed = self.feeds.get(peer)
                if feed is None:
                    raise StoreFault("FNFD obligation has no open journal: " + peer)
                feed.journal.append(frame)
        except Exception as error:
            self.feed_fence(error)
            raise StoreIndeterminate("FNFD obligations uncertain; owner restart required") from error

    def feed_dial(self, feed):
        if self.feed_uncertain:
            return False
        host, port = self.bridge.feed_endpoint(feed.peer)
        if not host or not port:
            return False
        try:
            session = Session(host, port, 5.0)
        except OSError:
            return False
        if not session.greeting.startswith(b"20"):
            # RFC 3977 5.1.1: a server that does not greet has not given us a
            # session. Without this, a peer that closes at accept -- or
            # anything forwarding to a peer that is down -- looks like an open
            # connection, and the feed writes a `(:feed-offer ...)` record and
            # counts an attempt for an offer that can never be sent. Three of
            # those reach `*fn-own-feed-retry-bound*` and the entry is
            # dropped, so a peer that is merely down would cost an article.
            session.close()
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
        """Give up this peer's socket, and tell the model the connection is lost.

        `feed_connect(peer, None)` alone stops selection and resolves
        nothing: the entry that was in flight stays :sent, `fn-feed-selection`
        will not pick it, and only a process restart frees it -- so the feed
        made no further progress for that peer until the node was restarted
        (the blocker in front of K5, measured on gate `a5c6792`: node A
        reconnected every 5 s and offered nothing, seven times over).
        `fn-own-feed-lost` is the transition for exactly this, and it
        forgets the connection itself, so it subsumes the nil report.
        """
        if feed.session is not None:
            try:
                self.selector.unregister(feed.session.sock)
            except (KeyError, ValueError):
                pass
        feed.close()
        if self.feed_uncertain:
            return
        try:
            self.bridge.feed_lost(feed.peer, self.clock.milliseconds())
            self.feed_flush()
        except Exception as error:                   # noqa: BLE001
            if self.feed_uncertain:
                return  # feed_fence already reported the uncertain outcome.
            # `feed_drop` is itself the containment for a feed that went
            # wrong, so nothing here may raise out of it: an exception
            # escaping this method ends the node from inside the handler
            # that exists to keep it alive.  Say it once, by peer name.  A
            # journal append that failed leaves the entry in flight on
            # disk, which `fn-own-reopen` settles at the next start.
            print("FEED-LOST-FAULT {}: {}: {}".format(
                feed.peer, type(error).__name__, error),
                file=sys.stderr, flush=True)

    def feed_write(self, feed, command):
        """Write the one ACL2-rendered byte vector its records authorized."""
        if self.feed_uncertain or not command:
            return
        feed.session.send_block(command)

    def feed_poll(self):
        if self.feed_uncertain:
            return
        now = self.clock.milliseconds()
        for feed in list(self.feeds.values()):
            if self.feed_uncertain:
                return
            # A feed that cannot make progress must not end the node, and
            # the boundary is one guarded unit PER FEED and not one for the
            # sweep: a fault while talking to one peer costs that peer's
            # session and no other's. `take_fault` prints `FEED-FAULT <peer>`
            # with its traceback -- `w11/twonode-feed`'s vocabulary, kept --
            # and drops the feed; the entry stays queued and the next dial
            # retries it. `FEED-FAULT` is a defect signal, not an outcome.
            try:
                if feed.session is None:
                    if (now >= feed.next_dial
                            and self.bridge.feed_has_queued(feed.peer)):
                        if not self.feed_dial(feed):
                            feed.next_dial = now + self.bridge.feed_backoff_ms(
                                feed.peer)
                    continue
                if self.bridge.feed_tick(feed.peer, now) == "offer":
                    self.feed_flush()
                    self.feed_write(feed, self.bridge.feed_command())
            except OSError:
                self.feed_drop(feed)
            except (SystemExit, KeyboardInterrupt):
                raise
            except BaseException as error:               # noqa: BLE001
                self.take_fault("feed-poll", error, feed=feed)
                if self.stopping:
                    return

    def feed_read(self, peer):
        if self.feed_uncertain:
            return
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
        if self.store_uncertain:
            self.stopping = True
            self.exit_code = EXIT_UNCERTAIN

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
        if self.feed_uncertain:
            raise StoreIndeterminate("FNFD journal requires owner restart")
        if self.config_uncertain:
            raise StoreIndeterminate("configuration journal requires owner restart")
        if self.store_uncertain:
            raise StoreIndeterminate("store outcome requires owner restart")
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
            group_octets = [group.encode("ascii") for group in groups]
            submitted = self.bridge.control_submit(msgid, group_octets, payload)
            if submitted != "submitted":
                if submitted in ("refused", "busy"):
                    raise StoreError("ACL2 refused control submission: {}".format(submitted))
                raise StoreFault("unexpected control submission result: {}".format(submitted))
            if self.bridge.take() != "taken-control":
                raise StoreFault("ACL2 did not take the control submission")
            sequence = self.records
            selected_charge = charge if charge is not None else conservative_charge(payload)
            intent = self.submission_intent(self.bridge.prov_post())
            word = (self.attempt(msgid, payload, group_octets, charge=selected_charge)
                    if intent is not None else "refused")
            if intent is not None:
                self.submission_resolution(word, intent)
            result = self.bridge.control_outcome(word)
            self.faults.at("owner:response")
            if result == "duplicate":
                return b"duplicate"
            if result == "accepted":
                return "committed sequence={} charge={}".format(
                    sequence, selected_charge).encode()
            if result == "refused":
                raise StoreError("ACL2 refused control post")
            if result == "uncertain":
                raise StoreIndeterminate("ACL2 reported uncertain control post")
            raise StoreFault("unexpected control outcome: {}".format(result))
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
        if command == b"RECONFIGURE":
            if len(words) != 4 or words[2].lower() not in (b"create", b"retire"):
                raise StoreError("RECONFIGURE <connection-id> <create|retire> <group>")
            try:
                cid = int(words[1])
                action = words[2].decode("ascii")
                name = words[3].decode("utf-8", "strict")
            except (ValueError, UnicodeDecodeError) as error:
                raise StoreError("malformed reconfiguration request") from error
            self.clock.observe(self.bridge)
            status, detail, record = self.bridge.reconfigure_group(cid, action, name)
            if status == "refused":
                return "refused {}".format(detail).encode()
            try:
                self.store.write_config_record(detail, record)
            except StoreIndeterminate:
                self.config_uncertain = True
                self.stopping = True
                raise
            if self.bridge.complete_reconfigure(detail) != "durable":
                self.stopping = True
                raise StoreFault("owner did not publish durable configuration")
            return "configured generation={}".format(detail).encode()
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
                if self.store_uncertain:
                    conn = key.data if isinstance(key.data, Connection) else None
                    if conn is None or conn.cid != self.uncertain_reply_cid:
                        continue
                # Every branch below is one event under the host-fault
                # boundary, named by what a fault in it costs.
                if key.data == "nntp":
                    self.guard("accept", lambda: self.accept_nntp(nntp_listener))
                elif key.data == "control":
                    self.guard("control", lambda: self.accept_control(control_listener))
                elif isinstance(key.data, tuple) and key.data[0] == "feed":
                    peer = key.data[1]
                    self.guard("feed-read", lambda: self.feed_read(peer),
                               feed=self.feeds.get(peer))
                else:
                    if key.fileobj in self.connections:
                        conn = key.data
                        self.guard("served-read", lambda: self.serve(conn, mask),
                                   conn=conn)
                    else:
                        # A registration with no connection behind it is a
                        # leak that spins the loop at full speed for the
                        # lifetime of the process.  Forget it.  (w11/feed-k5:
                        # this is what the 90-second accept refusal was --
                        # QUIT connections were never dropped after their
                        # final reply and the owner's connection table
                        # filled.)
                        try:
                            self.selector.unregister(key.fileobj)
                        except (KeyError, ValueError):
                            pass
                if self.stopping:
                    break
            if not self.stopping and not self.store_uncertain:
                self.guard("feed-poll", self.feed_poll)
        for feed in list(self.feeds.values()):
            feed.close()
        return self.exit_code


def fault_once(error):
    """An injector action that raises `error` the FIRST time only.

    A host fault is meant to cost one connection, so a test that asserts the
    OTHER connection is still served needs the point to fire once and then
    stop -- otherwise the surviving connection would fault too and the test
    would pass for the wrong reason.
    """
    fired = []

    def action():
        if fired:
            return None
        fired.append(True)
        raise error
    return action


def process_cut_once(code):
    """Test-only hard process death at one modelled submission cut."""
    fired = []

    def action():
        if fired:
            return None
        fired.append(True)
        os._exit(code)  # noqa: PLW1510 - the process death is the test event
    return action


# Documented test-only hooks, the owner's own, beside tools/run_store.py's
# CLI_FAULTS.  Each names one point in the serve loop; production passes
# NO_FAULTS and the paths hold no injection branch.  The errors are
# deliberately NOT StoreError: the class of defect this boundary exists for
# is the UNEXPECTED exception, and the one that killed the owner twice was a
# RuntimeError out of the ACL2 result parser.
OWNER_FAULTS = {
    "served-read": lambda: ScriptedFaults(
        "owner:served-read",
        action=fault_once(RuntimeError("injected host fault in the served read"))),
    "drain": lambda: ScriptedFaults(
        "owner:drain",
        action=fault_once(RuntimeError("injected host fault carrying a submission"))),
    "preintent-cut": lambda: ScriptedFaults(
        "owner:preintent", action=process_cut_once(90)),
    "intent-barrier-cut": lambda: ScriptedFaults(
        "owner:intent-barrier", action=process_cut_once(91)),
    "commit-barrier-cut": lambda: ScriptedFaults(
        "owner:commit-barrier", action=process_cut_once(92)),
    "abort-barrier-cut": lambda: ScriptedFaults(
        "owner:abort-barrier", action=process_cut_once(93)),
    "response-cut": lambda: ScriptedFaults(
        "owner:response", action=process_cut_once(94)),
    "store-uncertain": lambda: ScriptedFaults(
        "record-attempted",
        StoreIndeterminate("injected ambiguous article publication")),
}


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
    parser.add_argument("--inject-fault", choices=tuple(OWNER_FAULTS),
                        help="TEST ONLY: raise one unexpected exception at the "
                             "named point in the serve loop, once")
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
    faults = NO_FAULTS if args.inject_fault is None else OWNER_FAULTS[args.inject_fault]()
    try:
        store = Store(args.store, writable=True, faults=faults)
        store.acquire()
        bridge = Acl2Owner(args.max_connections)
        records = store.recover(bridge)
        if bridge.install_profile(store.config) != "installed":
            raise StoreFault("owner refused the store profile")
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
            owner = Owner(store, bridge, records, clock, tls, faults=faults)
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
