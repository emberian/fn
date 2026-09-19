#!/usr/bin/env python3
"""The mutable service owner: one process owns one store (C1-05).

It holds the exclusive writer lock, accepts loopback NNTP connections, and
accepts a local Unix-socket control channel for the post path.  Every state
decision is one call into the proved owner machine (books/owner.lisp) through
host/owner-host.lisp; this file moves bytes, reports filesystem observations
and clock readings, and maps outcomes to exit codes and reply lines.

Readers observe a committed version pinned when their connection opened; a
post advances the committed version without touching any open reader; a
reader moves to the newest version only when the control channel advances it.
"""
import argparse
import os
import selectors
import signal
import socket
import sys
import time

from run_store import (ACL2_RECOVER_BASE_SECONDS, ACL2_RECOVER_PER_RECORD_SECONDS,
                       Acl2Store, EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, Store,
                       StoreError, StoreFault, UsageParser, acl2_nat, acl2_octets,
                       acl2_symbol, exit_code_for, post_article)
from run_reader import acl2_boolean, acl2_octet_list

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAX_READ = 512
MAX_OUTPUT_BACKLOG = 64 * 1024
MAX_CONTROL_LINE = 4096
DTN_EPOCH_NS = 946684800 * 1_000_000_000  # 2000-01-01T00:00:00Z


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
        return acl2_symbol(self.call(form, timeout=timeout))

    def _nat(self, form):
        return acl2_nat(self.call(form))

    # Store path (the same observations run_store.Store reports)
    def recover(self, records, frontier):
        literal = "(" + " ".join(self.literal(record) for record in records) + ")"
        form = "(fn-owner-recover '{} {} {} state)".format(literal, frontier, self.max_conns)
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
        here.  The third value is the submission the read produced, if any:
        None until w4/post's POST fold lands a submit effect in
        fn-nntp-effectp; the owner then runs the durable path for it and
        feeds the outcome back through `outcome'.
        """
        literal = "(" + " ".join(str(byte) for byte in octets) + ")"
        outcome = self._symbol("(fn-owner-chunk {} '{} state)".format(cid, literal))
        if outcome != "ok":
            raise StoreError("owner does not know connection {}".format(cid))
        reply = bytes(acl2_octet_list(self.call("(@ fn-owner-output)")))
        closing = acl2_boolean(self.call("(@ fn-owner-closep)"))
        return reply, closing, None

    def outcome(self, cid, word):
        """Feed a submission's durable outcome back through the book."""
        return self._symbol("(fn-owner-outcome {} :{} state)".format(cid, word))

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

    def observe(self, bridge):
        monotonic_ms = time.monotonic_ns() // 1_000_000
        wall_ms = max(0, (time.time_ns() - DTN_EPOCH_NS) // 1_000_000)
        return bridge.observe(monotonic_ms, wall_ms, self.error_ms, True)


class Connection:
    def __init__(self, sock, cid):
        self.sock = sock
        self.cid = cid
        self.outbuf = b""
        self.closing = False
        self.reading = True


class Owner:
    def __init__(self, store, bridge, records, clock):
        self.store = store
        self.bridge = bridge
        self.records = len(records)
        self.clock = clock
        self.selector = selectors.DefaultSelector()
        self.connections = {}
        self.stopping = False

    # -- NNTP connections -------------------------------------------------
    def accept_nntp(self, listener):
        try:
            sock, _ = listener.accept()
        except OSError:
            return
        sock.setblocking(False)
        cid, greeting = self.bridge.open()
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
                # One read, one certified step: fn-own-read consumes the
                # whole chunk (books/served.lisp owns the framing loop and
                # fn-served-run-is-the-concatenated-step says the cut points
                # the network chose are invisible).
                reply, closing, submission = self.bridge.chunk(conn.cid, list(incoming))
                conn.outbuf += reply
                if closing:
                    conn.closing = True
                if submission is not None:
                    conn.outbuf += self.submit(conn, submission)
        if mask & selectors.EVENT_WRITE and conn.outbuf:
            try:
                sent = conn.sock.send(conn.outbuf)
            except (BlockingIOError, InterruptedError):
                sent = 0
            except OSError:
                self.drop(conn)
                return
            conn.outbuf = conn.outbuf[sent:]
        if conn.closing and not conn.outbuf:
            self.drop(conn)
            return
        # A peer that does not consume its output is stalled: stop taking its
        # input once the backlog reaches the bound.  It costs the owner one
        # bounded buffer and nothing else; every other connection and the
        # post path keep running.
        conn.reading = len(conn.outbuf) < MAX_OUTPUT_BACKLOG
        self.rearm(conn)

    def submit(self, conn, submission):
        """The served POST path, shaped for w4/post's fold.

        A submission the served step produced runs the same durable path a
        control-channel POST runs, with this connection as the transaction
        owner, and its outcome is fed back through fn-owner-outcome so the
        book, not this file, decides the reply.  Until the fold lands the
        served step produces no submission and this is never reached.
        """
        msgid, payload, groups, charge = submission
        self.clock.observe(self.bridge)
        if self.bridge.begin(conn.cid) != "begun":
            self.bridge.outcome(conn.cid, "refused")
            return b""
        try:
            sequence, _charge = post_article(self.store, self.bridge, self.records,
                                             msgid, payload, groups, charge)
        except StoreError as error:
            self.bridge.outcome(conn.cid, self.outcome_word(error))
            return b""
        if sequence is not None:
            self.records += 1
        self.bridge.outcome(conn.cid, "duplicate" if sequence is None else "committed")
        return b""

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
        while not self.stopping:
            for key, mask in self.selector.select(timeout=1.0):
                if key.data == "nntp":
                    self.accept_nntp(nntp_listener)
                elif key.data == "control":
                    self.accept_control(control_listener)
                else:
                    if key.fileobj in self.connections:
                        self.serve(key.data, mask)
        return EXIT_OK


def terminate_on_signal(signum, unused_frame):
    raise SystemExit(128 + signum)


def main(argv=None):
    signal.signal(signal.SIGTERM, terminate_on_signal)
    parser = UsageParser(description=__doc__)
    parser.add_argument("--store", required=True)
    parser.add_argument("--port", type=int, default=0)
    parser.add_argument("--control", required=True, help="Unix socket path for the control channel")
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
            return Owner(store, bridge, records, clock).run(listener, control)
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
