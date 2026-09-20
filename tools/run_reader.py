#!/usr/bin/env python3
"""Experimental loopback-only ACL2 NNTP reader; never parses client Lisp."""
import argparse
import os
import re
import select
import signal
import socket
import subprocess
import sys
import time

from run_store import Acl2Store, EXIT_FAULT, EXIT_OK, Store, UsageParser, decimal_list

# DTN time (RFC 9171 section 4.2.6) is milliseconds since 2000-01-01T00:00:00Z.
DTN_EPOCH_OFFSET = 946684800

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROMPT = b"ACL2 !>"
MAX_READ = 512
MAX_ACL2_OUTPUT = 1024 * 1024


class ReaderBridgeFault(RuntimeError):
    """The ACL2 bridge lost correlation; this reader cannot keep serving."""


def read_prompt(proc, timeout=5):
    out = b""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        ready,_,_=select.select([proc.stdout],[],[],.1)
        if ready:
            chunk = os.read(proc.stdout.fileno(), 4096)
            if not chunk:
                raise RuntimeError("ACL2 exited before producing a prompt")
            out += chunk
            if len(out) > MAX_ACL2_OUTPUT:
                raise RuntimeError("ACL2 output exceeded bridge limit")
            if out.rstrip().endswith(PROMPT):
                return out
    raise RuntimeError("ACL2 prompt timeout")

def form(proc, text):
    proc.stdin.write((text+"\n").encode()); proc.stdin.flush()
    return read_prompt(proc)

def fail_on_acl2_error(output):
    if any(marker in output.upper() for marker in
           (b"ACL2 ERROR", b"HARD ACL2 ERROR", b"******** FAILED ********")):
        raise RuntimeError(output.decode("utf-8", "replace"))
    return output


def acl2_octet_list(output):
    """Accept only ACL2's printed NIL or a proper list of decimal octets.

    The scan is linear: a repeated-group regular expression backtracks
    exponentially on malformed bridge output.
    """
    trimmed = output.strip()
    if not trimmed.endswith(PROMPT):
        raise RuntimeError("unexpected ACL2 octet-list result")
    body = trimmed[:-len(PROMPT)].strip()
    if body == b"NIL":
        return []
    values = decimal_list(body)
    if values is None:
        raise RuntimeError("unexpected ACL2 octet-list result")
    if any(value > 255 for value in values):
        raise RuntimeError("ACL2 emitted a non-octet bridge result")
    return values


def acl2_natural(output):
    trimmed = output.strip()
    if not trimmed.endswith(PROMPT):
        raise RuntimeError("unexpected ACL2 natural result")
    body = trimmed[:-len(PROMPT)].strip()
    if not re.fullmatch(rb"[0-9]+", body):
        raise RuntimeError("unexpected ACL2 natural result")
    return int(body)


def acl2_boolean(output):
    if re.fullmatch(rb"T\s*ACL2 !>", output):
        return True
    if re.fullmatch(rb"NIL\s*ACL2 !>", output):
        return False
    raise RuntimeError("unexpected ACL2 boolean result")


def acl2_archive_action(output):
    match = re.fullmatch(rb"\s*:(READY|REFUSED)\s*ACL2 !>", output.upper())
    if not match:
        raise RuntimeError("unexpected ACL2 archive-selection result")
    return match.group(1).lower()


class Acl2Reader:
    """A fixed-call bridge: socket input reaches ACL2 only as octet literals."""

    def __init__(self, store_bridge=None):
        self.store_bridge = store_bridge
        self.owns_process = store_bridge is None
        self.proc = None
        self.own_poisoned = False
        env = os.environ.copy()
        env["ACL2_CUSTOMIZATION"] = "NONE"
        env["ACL2_BOOK_HASH_ALISTP"] = "NIL"  # content-hashed certificates: relocatable across worktrees and hosts
        try:
            if self.owns_process:
                self.proc = subprocess.Popen(
                    [env.get("FN_ACL2", "acl2")], cwd=ROOT,
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, env=env)
                read_prompt(self.proc, timeout=15)
            else:
                self.proc = store_bridge.proc
            self._load('(include-book "books/node")')
            self._load('(include-book "books/nntp")')
            self._load('(ld "host/reader-host.lisp" :ld-error-action :return :ld-error-triples t)')
            # This process is read-only: POST is answered 440 by the book
            # (fn-post-disallowed-posting-does-not-await).  The owner,
            # tools/run_owner.py, is the process that serves POST.
            self.call("(fn-reader-set-posting nil state)")
            selection = "(fn-reader-use-seed state)" if self.owns_process else "(fn-reader-use-store state)"
            if acl2_archive_action(self.call(selection)) != b"ready":
                raise RuntimeError("reader archive is not NNTP-projectable")
        except BaseException:
            self.close()
            raise

    @property
    def poisoned(self):
        """True once this reader's ACL2 pipe can no longer be correlated."""
        if self.store_bridge is not None:
            return self.store_bridge.poisoned
        return self.own_poisoned

    def _load(self, text):
        self.call(text)

    def call(self, text):
        if self.store_bridge is not None:
            return self.store_bridge.call(text)
        try:
            output = form(self.proc, text)
        except (RuntimeError, OSError):
            # A lost prompt leaves this pipe one reply behind for good.
            self.own_poisoned = True
            raise
        return fail_on_acl2_error(output)

    def reset(self):
        # One clock observation per connection.  books/clock.lisp says what
        # the host is asserting with it; books/injection.lisp is the only
        # thing that reads it.  A POST later in a long connection therefore
        # carries this connection's reading, which is why the Injection-Date
        # of two posts on one connection can be equal.
        self.observe_clock()
        self.call("(fn-reader-reset state)")
        return bytes(acl2_octet_list(self.call("(@ fn-reader-output)")))

    def observe_clock(self):
        now = time.time()
        wall = int((now - DTN_EPOCH_OFFSET) * 1000)
        if wall < 0:
            wall = 0
        monotonic = int(time.monotonic() * 1000)
        self.call("(fn-reader-observe-clock {} {} {} state)".format(
            monotonic, wall, 1000))

    def chunk(self, octets):
        """One socket read, consumed whole by one certified call.

        `fn-served-step' (books/served.lisp) is a fold of fn-wire-feed-byte
        with fn-nntp-post-step run on each framed event before the next byte,
        with the reply concatenation; article mode is inside it.  It
        consumes the entire chunk, so there is never an unconsumed suffix to
        hand back and no re-feeding loop here; the empty list is returned in
        that position for callers that still drain one.
        """
        if not octets:
            return b"", False, []
        literal = "(" + " ".join(str(byte) for byte in octets) + ")"
        self.call("(fn-reader-chunk '" + literal + " state)")
        reply = bytes(acl2_octet_list(self.call("(@ fn-reader-output)")))
        closing = acl2_boolean(self.call("(@ fn-reader-closep)"))
        return reply, closing, []

    def close(self):
        if self.proc is None or not self.owns_process:
            return
        try:
            if self.proc.poll() is None and self.proc.stdin and not self.proc.stdin.closed:
                try:
                    self.proc.stdin.write(b"(quit)\n")
                    self.proc.stdin.flush()
                except (BrokenPipeError, OSError):
                    pass
            if self.proc.poll() is None:
                try:
                    self.proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    self.proc.terminate()
                    try:
                        self.proc.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        self.proc.kill()
                        self.proc.wait(timeout=3)
        finally:
            for stream in (self.proc.stdin, self.proc.stdout):
                if stream and not stream.closed:
                    stream.close()


def graceful_close(client):
    """End a connection after its final reply without a reset.

    Closing a socket that still holds unread input makes Linux send RST
    instead of FIN, and the peer then loses the reply it was owed (the 501
    for an over-long command, for example).  Signal end of output first, then
    drain what the peer already sent for a bounded interval, then let the
    caller close.  The drain is bounded in time, not trusted to end.
    """
    try:
        client.shutdown(socket.SHUT_WR)
    except OSError:
        return
    deadline = time.monotonic() + 1.0
    try:
        while time.monotonic() < deadline:
            client.settimeout(max(0.05, deadline - time.monotonic()))
            if not client.recv(MAX_READ):
                return
    except (socket.timeout, OSError):
        return


def serve_client(reader, client):
    """Serve one connection; a broken peer cannot end the listener.

    A poisoned bridge is not a broken peer.  Once correlation is lost the
    reader can no longer tell one command's reply from another's, so it
    refuses to keep serving and the caller fails closed.
    """
    with client:
        try:
            client.settimeout(10)
            client.sendall(reader.reset())
            while True:
                try:
                    incoming = client.recv(MAX_READ)
                except socket.timeout:
                    return
                if not incoming:
                    return
                # One read, one certified step.  The loop that used to live
                # here re-fed an unconsumed suffix and so computed
                # fn-wire-drive in Python; books/served.lisp now owns that
                # loop, and fn-served-run-is-the-concatenated-step says the
                # cut points the network chose are invisible.  Article mode
                # is wire state inside the served connection, so a POST and
                # its article are the same one call per read.
                try:
                    reply, closing, unused_suffix = reader.chunk(list(incoming))
                except RuntimeError:
                    # An invalid bridge result is not a protocol reply.
                    # Do not retain this connection's input for reuse.
                    if reader.poisoned:
                        raise ReaderBridgeFault("ACL2 bridge poisoned")
                    return
                if reply:
                    client.sendall(reply)
                if closing:
                    graceful_close(client)
                    return
        except ReaderBridgeFault:
            raise
        except (RuntimeError, ConnectionError, OSError):
            if reader.poisoned:
                raise ReaderBridgeFault("ACL2 bridge poisoned")
            return


def terminate_on_signal(signum, unused_frame):
    raise SystemExit(128 + signum)

def main():
    signal.signal(signal.SIGTERM, terminate_on_signal)
    parser = UsageParser()
    parser.add_argument("--port", type=int, default=8119)
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--store", help="durable store snapshot to serve")
    args = parser.parse_args()
    if not 0 <= args.port <= 65535:
        parser.error("--port must be from 0 through 65535")

    reader = None
    store = None
    store_bridge = None
    try:
        if args.store:
            # A shared lock fixes a recovered snapshot for reading.  POST
            # needs the writer lock and the live owner: tools/run_owner.py.
            store = Store(args.store, writable=False)
            store.acquire()
            store_bridge = Acl2Store()
            store.recover(store_bridge)
            reader = Acl2Reader(store_bridge)
        else:
            reader = Acl2Reader()
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as listener:
            listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            listener.bind(("127.0.0.1", args.port))
            listener.listen(1)
            # The generation this reader pinned at open: its projection is a
            # snapshot, and a later reconfiguration is not seen until reopen.
            print("LISTENING {} generation={}".format(
                listener.getsockname()[1],
                store.config_generation if store is not None else 0), flush=True)
            while True:
                client, _ = listener.accept()
                try:
                    serve_client(reader, client)
                except ReaderBridgeFault as fault:
                    # Correlation is unrecoverable within this process.  Fail
                    # closed rather than answer the next client from a pipe
                    # whose replies can no longer be matched to its commands.
                    print("reader: {}".format(fault), file=sys.stderr)
                    return EXIT_FAULT
                if args.once:
                    break
        return EXIT_OK
    finally:
        if reader is not None:
            reader.close()
        if store_bridge is not None:
            store_bridge.close()
        if store is not None:
            store.close()
if __name__=='__main__': sys.exit(main())
