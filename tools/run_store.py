#!/usr/bin/env python3
"""Experimental local immutable-transaction store backed by interpreted ACL2.

This is a storage experiment, not a durable-service or power-failure claim.
ACL2 decodes records, frames and unframes transaction files, derives content
identity, applies every bound and owns the group table and the charge policy.
Python owns bounded filesystem I/O, POSIX barriers, and SHA-256 over byte
strings it does not interpret (A-CRYPTO).
"""
import argparse
import contextlib
import base64
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import select
import stat
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
# This module is imported both as `tools.run_store` and, with `tools/` on the
# path, as `run_store`.  Pin the framing bridge to one identity so its ACL2
# session is shared rather than opened once per spelling.
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import frame_bridge  # noqa: E402
from tools import acl2_slots, bridge_image  # noqa: E402

PROMPT = b"ACL2 !>"
MAX_ACL2_OUTPUT = 4 * 1024 * 1024
# Every profile value (format, payload bound, aggregate replay bound,
# transaction bound, frontier format) and every preset name is ACL2's: the
# native operator's `fn-nop-profile-preset-word` reads `init --profile WORD`,
# `fn-bs-config-for-profile` gives the preset, the FNSM frame carries it, and
# an open store's `Store.config` is `fn-bs-config-decode`'s reading of its own
# frame, admitted by `fn-bs-profile-admittedp` (format 8, D27).
# `profile_config` asks ACL2 for a preset's values; this module keeps no copy
# of any of them.
# The CLI's default `init --group` list: the two experimental groups every
# existing test posts into.  A default argument for an operator command, not
# a group table; the table a store serves is decided by the configuration
# records ACL2 admits and replays.
DEFAULT_GROUPS = ("fn.letters", "fn.test")
CONFIG_RECORD_BYTES = 65538
# `books/frame` owns the grammar.  These two are the slice arithmetic that
# `durable_records` and the corruption tests still do over a file they never
# interpret; `frame_bridge.FrameSession` checks both against the ACL2
# constants when a session opens, so a divergence fails at startup.
MAGIC = b"FNST\x01\x01"
# The FNAN anchor record: `books/anchor` bounds its payload at 1024 octets and
# `books/frame` adds the 42-octet header and trailer.  This is the read bound,
# not a second grammar; ACL2 refuses anything it does not recognize.
ANCHOR_RECORD_BYTES = 1024 + 42
TRAILER_BYTES = 32
MAX_STAGING_REPORT = 64

# Distinct CLI outcomes.  Uncertain, refused and accepted never share a code;
# specs/host.md carries the table and its reader contract.
EXIT_OK = 0
EXIT_REFUSED = 1
EXIT_UNCERTAIN = 3
EXIT_FAULT = 4
EXIT_USAGE = 5

# ACL2 bridge correlation and reply bounds.  Every call prints a fresh nonce
# marker first, so a reply is accepted only when this call's marker preceded
# it.  Timeouts are refutation bounds, not budgets: the base covers process
# scheduling plus book-resident work, and the per-KiB term covers marshaling
# the decimal-octet literal that carries external bytes.  The recorded
# maximum-profile reopen on this machine is 11.7 s for a 128-record form of
# roughly 34 MiB, about 0.35 s/MiB; 0.004 s/KiB is 4 s/MiB, an order of
# magnitude above that measurement, and the per-record recovery term bounds
# the same reopen at about 158 s rather than the fixed 20 s D2 found too close.
CALL_MARKER_PREFIX = b"FN_CALL_"
ACL2_START_TIMEOUT_SECONDS = 60.0
ACL2_CALL_BASE_SECONDS = 20.0
ACL2_CALL_PER_KIB_SECONDS = 0.004
ACL2_RECOVER_BASE_SECONDS = 30.0
ACL2_RECOVER_PER_RECORD_SECONDS = 1.0

# darwin's fsync(2) hands data to the drive and returns; F_FULLFSYNC asks the
# device to flush its own cache.  Every barrier the specifications call a
# durability barrier goes through durable_barrier below.
FULL_FSYNC = getattr(fcntl, "F_FULLFSYNC", None) if sys.platform == "darwin" else None
FULL_FSYNC_UNSUPPORTED = frozenset(
    value for value in (getattr(errno, name, None)
                        for name in ("ENOTTY", "ENOTSUP", "EOPNOTSUPP", "EINVAL", "EPERM"))
    if value is not None)


class StoreError(RuntimeError):
    pass


class StoreFault(StoreError):
    pass


class StoreIndeterminate(StoreError):
    pass


def exit_code_for(error, default=EXIT_FAULT):
    """Map one already-classified host outcome to its distinct CLI exit code."""
    if isinstance(error, StoreIndeterminate):
        return EXIT_UNCERTAIN
    if isinstance(error, StoreFault):
        return EXIT_FAULT
    if isinstance(error, StoreError):
        return EXIT_REFUSED
    if isinstance(error, UnicodeError):
        return EXIT_USAGE
    if isinstance(error, OSError):
        return EXIT_FAULT
    return default


class UsageParser(argparse.ArgumentParser):
    """argparse reports its own usage failures with the documented code."""
    def error(self, message):
        self.exit(EXIT_USAGE, "{}: error: {}\n".format(self.prog, message))


class FaultPoints:
    """Production fault points: every injection site calls `at` on this object.

    The production implementation does nothing, so no durable path carries an
    injection branch.  Tests and the documented `--inject-fault` test hook pass
    their own object with the same one-method protocol.
    """
    __slots__ = ()

    def at(self, point):
        return None


NO_FAULTS = FaultPoints()


class ScriptedFaults(FaultPoints):
    """Test-only injector for exactly one named point.

    Production code never constructs this.  It is the single place in the host
    where a deliberate failure or process death is produced, so the durable
    paths stay free of `os._exit` and of per-fault comparisons.
    """
    __slots__ = ("point", "error", "exit_code", "action")

    def __init__(self, point, error=None, exit_code=None, action=None):
        self.point = point
        self.error = error
        self.exit_code = exit_code
        self.action = action

    def at(self, point):
        if point != self.point:
            return None
        if self.action is not None:
            return self.action()
        if self.exit_code is not None:
            os._exit(self.exit_code)
        raise self.error


def check_regular(path):
    try:
        st = os.lstat(path)
    except FileNotFoundError:
        return False
    if not os.path.isfile(path) or os.path.islink(path):
        raise StoreFault("refusing non-regular path: {}".format(path))
    return st


def durable_barrier(fd):
    """Complete the strongest durability barrier this platform offers on `fd`.

    On darwin `fsync(2)` only hands the data to the drive, so every barrier the
    specifications call a durability barrier issues `F_FULLFSYNC`, which asks
    the device to flush its own cache.  A filesystem that rejects the request
    falls back to `fsync(2)` and then carries only the `fsync(2)` contract.
    Elsewhere this is `os.fsync`.  Neither is a power-loss qualification.
    """
    if FULL_FSYNC is not None:
        try:
            fcntl.fcntl(fd, FULL_FSYNC)
            return
        except OSError as error:
            if error.errno not in FULL_FSYNC_UNSUPPORTED:
                raise
    os.fsync(fd)


def fsync_dir(path):
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    fd = os.open(path, flags)
    try:
        durable_barrier(fd)
    finally:
        os.close(fd)


def fsync_file(fd):
    durable_barrier(fd)


def write_all(fd, data):
    offset = 0
    while offset < len(data):
        count = os.write(fd, data[offset:])
        if count <= 0:
            raise OSError("short store write")
        offset += count


def read_regular_bounded(path, maximum):
    """Read one regular, non-symlink file through a no-follow descriptor."""
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise StoreFault("refusing non-regular store file: {}".format(path))
        if info.st_size > maximum:
            raise StoreFault("store file exceeds bound: {}".format(path))
        chunks, remaining = [], maximum + 1
        while remaining:
            chunk = os.read(fd, min(65536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        data = b"".join(chunks)
        if len(data) > maximum:
            raise StoreFault("store file exceeds bound: {}".format(path))
        return data
    finally:
        os.close(fd)


def fsync_regular(path):
    """Barrier one verified regular file without following a replacement link."""
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise StoreFault("refusing non-regular store file: {}".format(path))
        durable_barrier(fd)
    finally:
        os.close(fd)


def frame(record, bridge=None):
    """ACL2 builds the frame; the host only appends the integrity trailer.

    `fn-frame-store-protected` returns the exact octets the trailer covers and
    `fn-frame-store-encode-is-protected-plus-digest` proves that appending 32
    digest octets to them is `fn-frame-encode`.  SHA-256 itself is A-CRYPTO.
    """
    try:
        return frame_bridge.session(bridge).store_frame(record)
    except frame_bridge.BridgeError as error:
        raise StoreFault("ACL2 refused to frame a transaction record") from error


def unframe(raw, bridge=None):
    """ACL2 parses the frame and compares the trailer with the host digest.

    The record bound is the model's, so there is no host bound to pass and
    none to disagree: `fn-frame-store-decode` applies
    `*fn-frame-max-store-payload*` itself.
    """
    session = frame_bridge.session(bridge)
    try:
        return session.store_unframe(raw)
    except frame_bridge.BridgeError as error:
        raise StoreFault(str(error)) from error


def read_prompt(proc, timeout=ACL2_CALL_BASE_SECONDS):
    output = b""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        ready, _, _ = select.select([proc.stdout], [], [], .1)
        if not ready:
            continue
        chunk = os.read(proc.stdout.fileno(), 4096)
        if not chunk:
            raise StoreError("ACL2 exited before producing a prompt")
        output += chunk
        if len(output) > MAX_ACL2_OUTPUT:
            raise StoreError("ACL2 bridge output exceeds bound")
        if output.rstrip().endswith(PROMPT):
            return output
    raise StoreError("ACL2 prompt timeout")


def acl2_result(output):
    data = output.strip()
    if not data.endswith(PROMPT):
        raise StoreError("unexpected ACL2 bridge result")
    return data[:-len(PROMPT)].strip()


def decimal_list(body):
    """Parse ACL2's printed proper list of decimal naturals in linear time.

    A regular expression over a repeated group backtracks exponentially on
    malformed bridge output, so the scan is an explicit split instead.
    """
    if len(body) < 2 or body[:1] != b"(" or body[-1:] != b")":
        return None
    values = []
    for token in body[1:-1].split():
        if not token.isdigit():
            return None
        values.append(int(token))
    return values


def acl2_octets(output):
    body = acl2_result(output)
    if body == b"NIL":
        return b""
    values = decimal_list(body)
    if values is None:
        raise StoreError("ACL2 returned a non-octet result")
    if any(value > 255 for value in values):
        raise StoreError("ACL2 returned a non-octet")
    return bytes(values)


def acl2_symbol(output):
    body = acl2_result(output).upper()
    if body not in {b":READY", b":PREPARED", b":DURABLE", b":ABORTED",
                    b":INDETERMINATE", b":DUPLICATE", b":CONFLICT", b":ABSENT", b":INVALID",
                    b":REFUSED", b":CLOCK-UNUSABLE", b":FAULT", b":RECOVERING",
                    b":FRONTIER-STAGED", b":FRONTIER-DATA-DURABLE", b":FRONTIER-ATTEMPTED",
                    b":RECORD-STAGED", b":RECORD-DATA-DURABLE", b":RECORD-ATTEMPTED",
                    b":RESERVED", b":ABORTING", b":COMPLETING", b":FENCED-FRONTIER", b":FENCED-RECORD",
                    b":FENCED-RECOVERY"}:
        raise StoreError("unexpected ACL2 action: {}".format(body.decode("ascii", "replace")))
    return body.decode("ascii").lower()[1:]


def acl2_keyword(output):
    """A keyword reply outside the store-action vocabulary: a configuration
    outcome (:ok/:refused) or an admissibility reason named by books/config."""
    body = acl2_result(output).upper()
    if not re.fullmatch(rb":[A-Z0-9-]+", body):
        raise StoreError("ACL2 returned a non-keyword: {}".format(body.decode("ascii", "replace")))
    return body.decode("ascii").lower()[1:]


def acl2_nat(output):
    body = acl2_result(output)
    if not re.fullmatch(rb"[0-9]+", body):
        raise StoreError("ACL2 returned a non-natural")
    return int(body)


def acl2_boolean(output):
    body = acl2_result(output).upper()
    if body == b"T":
        return True
    if body == b"NIL":
        return False
    raise StoreError("ACL2 returned a non-boolean")


def acl2_environment():
    """The environment every bridge ACL2 gets: the certification settings
    (`tools/acl2` and the runner use the same two) and the pool's heap cap."""
    env = os.environ.copy()
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env["ACL2_BOOK_HASH_ALISTP"] = "NIL"  # content-hashed certificates: relocatable across worktrees and hosts
    return acl2_slots.apply_heap_cap(env)


# One pool slot per process tree.  A process takes a slot for its first live
# bridge and returns it with its last, and publishes its pid in
# SLOT_HOLDER_VARIABLE while it holds it; a child it starts (the tests run
# `tools/run_store.py` as a subprocess while holding a bridge) inherits that
# slot instead of waiting for a second one, which would deadlock a full pool
# of parents each waiting on its child.  A tree therefore counts once against
# the pool however many bridges it nests.
SLOT_HOLDER_VARIABLE = "FN_ACL2_SLOT_HOLDER"
_SLOT_LOCK = threading.Lock()
_SLOT_STACK = None
_SLOT_USERS = 0


def _pid_alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _inherited_slot():
    holder = os.environ.get(SLOT_HOLDER_VARIABLE, "")
    return holder.isdigit() and _pid_alive(int(holder))


def _acquire_slot(label):
    global _SLOT_STACK, _SLOT_USERS
    with _SLOT_LOCK:
        if _SLOT_USERS == 0 and not _inherited_slot():
            stack = contextlib.ExitStack()
            stack.enter_context(acl2_slots.slot(label))
            _SLOT_STACK = stack
            os.environ[SLOT_HOLDER_VARIABLE] = str(os.getpid())
        _SLOT_USERS += 1


def _release_slot():
    global _SLOT_STACK, _SLOT_USERS
    with _SLOT_LOCK:
        _SLOT_USERS = max(0, _SLOT_USERS - 1)
        if _SLOT_USERS == 0 and _SLOT_STACK is not None:
            stack, _SLOT_STACK = _SLOT_STACK, None
            if os.environ.get(SLOT_HOLDER_VARIABLE) == str(os.getpid()):
                del os.environ[SLOT_HOLDER_VARIABLE]
            stack.close()


class Acl2Store:
    """Fixed ACL2 calls: all externally-derived values become decimal octets."""

    # Which boot this bridge is: `tools/bridge_image.KINDS` names its forms.
    BRIDGE_KIND = "store"

    def __init__(self, _forms=None, _use_image=True, _reset=True):
        env = acl2_environment()
        self.proc = None
        # A bridge whose correlation is lost cannot be repaired by reading
        # further: a new ACL2 process is the only recovery.
        self.poisoned = False
        # FrameSession may adopt this process instead of starting a second
        # ACL2.  An explicit close is the context boundary that lets its
        # process-wide cache discard that adoption on the next use.
        self.closed = False
        self._slot_held = False
        forms = bridge_image.KINDS[self.BRIDGE_KIND] if _forms is None else _forms
        try:
            # The machine-wide ACL2 pool (tools/acl2_slots.py) and its heap
            # cap, as every other fn tool that starts ACL2 (PKT-162).
            _acquire_slot("bridge " + self.BRIDGE_KIND)
            self._slot_held = True
            command = [str(bridge_image.resolve_acl2(env))]
            # True when the process already holds the boot's world.
            self.preloaded = False
            if _use_image and bridge_image.enabled():
                command = [str(bridge_image.ensure(self.BRIDGE_KIND, env))]
                self.preloaded = True
            self.proc = subprocess.Popen(command, cwd=ROOT,
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, env=env)
            read_prompt(self.proc, ACL2_START_TIMEOUT_SECONDS)
            if not self.preloaded:
                for form in forms:
                    self.call(form)
            if _reset:
                self.reset()
        except BaseException:
            self.close()
            raise

    def release_slot(self):
        if getattr(self, "_slot_held", False):
            self._slot_held = False
            _release_slot()

    @staticmethod
    def form_timeout(form):
        return ACL2_CALL_BASE_SECONDS + ACL2_CALL_PER_KIB_SECONDS * (len(form) / 1024.0)

    def _correlate(self):
        """Print a fresh per-call nonce and require it before this call's reply.

        The marker is read to its own prompt before the real form is written,
        so a reply that belongs to an earlier call cannot be mistaken for this
        one: either the marker arrives first or the bridge is poisoned.
        """
        marker = CALL_MARKER_PREFIX + os.urandom(16).hex().encode("ascii")
        self.proc.stdin.write(b'(cw "' + marker + b'~%")\n')
        self.proc.stdin.flush()
        output = read_prompt(self.proc, ACL2_CALL_BASE_SECONDS)
        if output.count(PROMPT) != 1 or marker not in output.split(PROMPT, 1)[0]:
            raise StoreError("ACL2 bridge call marker did not precede its prompt")

    def call(self, form, timeout=None):
        if getattr(self, "closed", False):
            raise StoreError("ACL2 bridge closed")
        if self.poisoned:
            raise StoreError("ACL2 bridge poisoned")
        try:
            self._correlate()
            self.proc.stdin.write((form + "\n").encode("ascii"))
            self.proc.stdin.flush()
            output = read_prompt(
                self.proc, self.form_timeout(form) if timeout is None else timeout)
        except StoreError:
            self.poisoned = True
            raise
        except OSError as error:
            self.poisoned = True
            raise StoreError("ACL2 bridge transport failed: {}".format(error)) from error
        upper = output.upper()
        if b"ACL2 ERROR" in upper or b"HARD ACL2 ERROR" in upper or b"FAILED" in upper:
            # A correlated reply that reports an ACL2 error leaves the pipe
            # synchronized; the refusal is the answer, not a lost result.
            raise StoreError(output.decode("utf-8", "replace"))
        return output

    @staticmethod
    def literal(octets):
        return "(" + " ".join(str(value) for value in octets) + ")"

    @staticmethod
    def numeric_list(values):
        return "(" + " ".join(str(value) for value in values) + ")"

    def reset(self):
        return acl2_symbol(self.call("(fn-store-sn-reset state)"))

    # The served statement query (decision D21).  ACL2 holds the index in the
    # store state; this sends the id and prints what the index answers.  No
    # part of the query is computed here: fn-sn-statement-lookup reads the
    # carried index, and fn-sn-statement-lookup-is-the-lace-lookup
    # (books/store-node-invariants) is what says that is the same answer as
    # the linear lace projection.
    def set_keyring(self, pairs):
        entries = " ".join(
            "(" + self.literal(ident) + " " + self.literal(key) + ")"
            for ident, key in pairs)
        return acl2_keyword(self.call(
            "(fn-store-sn-set-keyring '(" + entries + ") state)"))

    def keyring_size(self):
        return acl2_nat(self.call("(fn-store-sn-keyring-size state)"))

    def index_size(self):
        return acl2_nat(self.call("(fn-store-sn-index-size state)"))

    def statement(self, id_octets):
        return acl2_octets(self.call(
            "(fn-store-sn-statement '" + self.literal(id_octets) + " state)"))

    def equivocator(self, creator_octets, incarnation):
        return acl2_keyword(self.call(
            "(fn-store-sn-equivocator '" + self.literal(creator_octets) + " "
            + str(int(incarnation)) + " state)"))

    def record_sequence(self, record):
        return acl2_nat(self.call("(fn-store-record-sequence '" + self.literal(record) + ")"))

    def record_txid(self, record):
        return acl2_nat(self.call("(fn-store-record-txid '" + self.literal(record) + ")"))

    def transaction_name(self, sequence):
        """The ACL2-owned final name for an allocated record sequence."""
        if isinstance(sequence, bool) or not isinstance(sequence, int) or sequence < 0:
            raise StoreError("transaction sequence is not a natural")
        octets = acl2_octets(self.call("(fn-store-txn-name-octets {})".format(sequence)))
        try:
            return frame_bridge.path_component(list(octets))
        except (UnicodeDecodeError, frame_bridge.BridgeError) as error:
            raise StoreError("ACL2 returned an unusable transaction name") from error

    def recover(self, records, frontier, config_records=()):
        literal = "(" + " ".join(self.literal(record) for record in records) + ")"
        config = "(" + " ".join(self.literal(record) for record in config_records) + ")"
        form = ("(fn-store-sn-recover '" + literal + " " + str(frontier)
                + " '" + config + " state)")
        # Replay cost grows with the recovered history, so the bound does too.
        timeout = max(ACL2_RECOVER_BASE_SECONDS + ACL2_RECOVER_PER_RECORD_SECONDS * len(records),
                      self.form_timeout(form))
        return acl2_symbol(self.call(form, timeout=timeout))


    # -- the external freshness anchor ---------------------------------------
    # Every decision below is ACL2's: the anchor grammar, what the signature
    # covers, the ordering, the monotone rule and the three outcomes all live
    # in books/anchor.lisp.  Python moves octets and runs Ed25519.

    def _form(self, form, timeout=None):
        return frame_bridge.read_form(self.call(form, timeout=timeout))

    @classmethod
    def anchor_fields_form(cls, fields):
        if fields is None:
            return "nil"
        (key, delegate, mint, maxt, delegation_signature,
         midpoint, radius, nonce, signature, root) = fields
        return "(list '{} '{} {} {} '{} {} {} '{} '{} '{})".format(
            cls.literal(key), cls.literal(delegate), mint, maxt,
            cls.literal(delegation_signature), midpoint, radius,
            cls.literal(nonce), cls.literal(signature), cls.literal(root))

    @classmethod
    def anchor_pinned_form(cls, pinned):
        return "(list " + " ".join("'" + cls.literal(key) for key in pinned) + ")"

    def anchor_signed_octets(self, radius, midpoint, root):
        """The octets ACL2 says the server signed, for the host to verify."""
        value = self._form("(fn-anchor-host-signed-octets {} {} '{})".format(
            radius, midpoint, self.literal(root)))
        return bytes(value)

    def anchor_delegation_octets(self, fields):
        """The delegation octets ACL2 says the pinned key signed."""
        value = self._form("(fn-anchor-host-delegation-octets {})".format(
            self.anchor_fields_form(fields)))
        if not isinstance(value, list):
            raise StoreFault("ACL2 refused an anchor delegation")
        return bytes(value)

    def anchor_wellformed(self, fields):
        return self._form("(fn-anchor-host-wellformedp {})".format(
            self.anchor_fields_form(fields))) == 1

    def anchor_protected(self, incarnation, fields):
        value = self._form("(fn-anchor-host-protected {} {})".format(
            incarnation, self.anchor_fields_form(fields)))
        if not isinstance(value, list):
            raise StoreFault("ACL2 refused to frame an anchor record")
        return bytes(value)

    def anchor_decode(self, octets, digest):
        value = self._form("(fn-anchor-host-decode '{} '{})".format(
            self.literal(octets), self.literal(digest)))
        if not isinstance(value, list) or len(value) != 11:
            raise StoreFault("durable anchor record does not decode")
        return value

    # `verdict` and `one_nonce` are the two A-CRYPTO seam values ACL2 cannot
    # compute: `fn-anchor-signatures-okp` and `fn-anchor-one-nonce-p`.  They
    # are separate arguments because they have different answers -- a failed
    # signature is `:refused :unverified`, an unfoldable Merkle tree is
    # `:uncertain :unmodelled-tree`.
    def anchor_accept(self, pinned, latest, incarnation, fields, verdict,
                      one_nonce):
        status, reason = self._form(
            "(fn-anchor-host-accept {} {} {} {} {} {})".format(
                self.anchor_pinned_form(pinned), self.anchor_fields_form(latest),
                incarnation, self.anchor_fields_form(fields),
                "t" if verdict else "nil", "t" if one_nonce else "nil"))
        return str(status), (str(reason) if reason else None)

    def anchor_restore(self, pinned, incarnation, referenced, presented, verdict,
                       one_nonce):
        status, reason, next_incarnation = self._form(
            "(fn-anchor-host-restore {} {} {} {} {} {})".format(
                self.anchor_pinned_form(pinned), incarnation,
                self.anchor_fields_form(referenced),
                self.anchor_fields_form(presented),
                "t" if verdict else "nil", "t" if one_nonce else "nil"))
        return str(status), (str(reason) if reason else None), next_incarnation

    def io(self, operation, result="ok"):
        return acl2_symbol(self.call("(fn-store-sn-io :{} :{} state)".format(operation, result)))

    def prepare(self, msgid, payload, group_codes, obligation_id, subject, evidence, charge):
        # One environmental reading per prepare.  ACL2 alone derives the
        # acceptance stamp and decides whether this reading is usable.
        try:
            monotonic_ms = time.monotonic_ns() // 1_000_000
            wall_ms = (time.time_ns() - 946684800 * 1_000_000_000) // 1_000_000
            has_wall = monotonic_ms >= 0 and wall_ms >= 0
        except OSError:
            monotonic_ms, wall_ms, has_wall = 0, 0, False
        monotonic_ms = max(0, monotonic_ms)
        wall_ms = max(0, wall_ms)
        form = "(fn-store-sn-prepare '" + self.literal(msgid) + " '" + self.literal(payload)
        form += " '" + self.numeric_list(group_codes) + " '" + self.literal(obligation_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " {} (fn-clock-observation {} {} 1000 {}) state)".format(
            charge, monotonic_ms, wall_ms, "t" if has_wall else "nil")
        return acl2_symbol(self.call(form))

    def existing_action(self, msgid, payload, group_codes):
        form = "(fn-store-sn-existing-action '" + self.literal(msgid)
        form += " '" + self.literal(payload) + " '" + self.numeric_list(group_codes) + " state)"
        return acl2_symbol(self.call(form))

    def pending_record(self):
        return acl2_octets(self.call("(fn-store-sn-pending-octets state)"))

    def known_abort(self):
        return acl2_symbol(self.call("(fn-store-sn-known-abort state)"))

    def refuse_reservation(self):
        return acl2_symbol(self.call("(fn-store-sn-refuse-reservation state)"))

    def finish(self):
        return acl2_symbol(self.call("(fn-store-sn-finish state)"))

    def article_count(self):
        return acl2_nat(self.call("(fn-store-sn-article-count state)"))

    def next_txid(self):
        return acl2_nat(self.call("(fn-store-sn-next-txid state)"))

    def group_next(self, code):
        return acl2_nat(self.call("(fn-store-sn-group-next {} state)".format(code)))

    # -- the replayed configuration -------------------------------------------

    def config_generation(self):
        return acl2_nat(self.call("(fn-store-cfg-generation state)"))

    def _names(self, form):
        joined = bytes(acl2_octets(self.call(form)))
        return tuple(name.decode("utf-8") for name in joined.split(b"\n") if name)

    def config_served(self):
        return self._names("(fn-store-cfg-served state)")

    def config_domain(self):
        return self._names("(fn-store-cfg-domain state)")

    def sweep_staging(self, observed, held=()):
        """Which observed staging names may be unlinked (books/store-sweep.lisp).

        Python enumerates the directory and names what this process holds;
        the removal decision -- the staging namespace, the held set and the
        kernel gate -- is the book's.
        """
        form = "(fn-store-sn-sweep-staging '({}) '({}) state)".format(
            " ".join(self.literal(name) for name in observed),
            " ".join(self.literal(name) for name in held))
        return self._names(form)

    def reconfigure(self, kind, name, monotonic, wall, n=0):
        """One reconfiguration request.  Returns ("ok", octets) or ("refused", reason).

        The kind, the name and the number go in; the deltas, the admissibility
        and the record are the core's.  Python never decides whether a
        capacity is above the reservation total: books/config does, through
        fn-cnode-record-acceptablep against the live node.
        """
        form = "(fn-store-cfg-reconfigure {} '{} {} {} {} state)".format(
            kind, self.literal(name.encode("utf-8", "strict")), int(n),
            int(monotonic), int(wall))
        status = acl2_keyword(self.call(form))
        if status == "ok":
            return status, acl2_octets(self.call("(fn-store-cfg-last-octets state)"))
        if status != "refused":
            raise StoreFault("unexpected reconfiguration outcome: {}".format(status))
        return "refused", acl2_keyword(self.call("(fn-store-cfg-last-reason state)"))

    def set_peer(self, peer, monotonic, wall):
        """One `peer add': the record, the delta and the octets are ACL2's.

        `peer' is the operator's words (name, path identity, endpoint, port,
        the two halves, the auth slot); nothing here decides whether they
        denote a well-formed peer -- fn-store-cfg-set-peer builds the record
        with fn-cfg-peer-make and refuses `:peer-record' when
        `fn-cfg-peerp' is false.
        """
        form = ("(fn-store-cfg-set-peer '{name} '{path} '{host} {port} "
                "'{ing} {inmax} {inflight} '{outg} {stream} {maxq} {backoff} "
                ":{authkind} '{auth} '{carries} {monotonic} {wall} state)").format(
            carries="(" + " ".join(self.literal(c) for c in peer.get("carries", ())) + ")",
            name=self.literal(peer["name"]), path=self.literal(peer["path_identity"]),
            host=self.literal(peer["endpoint"]), port=int(peer["port"]),
            ing=self.literal(peer["inbound_groups"]),
            inmax=int(peer["inbound_max_octets"]), inflight=int(peer["inbound_max_inflight"]),
            outg=self.literal(peer["outbound_groups"]),
            stream="t" if peer["streaming"] else "nil",
            maxq=int(peer["max_queue"]), backoff=int(peer["backoff_ms"]),
            authkind=peer["auth_kind"], auth=self.literal(peer["auth_value"]),
            monotonic=int(monotonic), wall=int(wall))
        status = acl2_keyword(self.call(form))
        if status == "ok":
            return status, acl2_octets(self.call("(fn-store-cfg-last-octets state)"))
        if status != "refused":
            raise StoreFault("unexpected peer outcome: {}".format(status))
        return "refused", acl2_keyword(self.call("(fn-store-cfg-last-reason state)"))

    def set_policy(self, slot, value, monotonic, wall):
        """One `policy set': the delta, its admissibility and the octets are
        ACL2's (`fn-store-cfg-set-policy'). Nothing here decides a slot."""
        form = "(fn-store-cfg-set-policy '{} '{} {} {} state)".format(
            self.literal(slot), self.literal(value), int(monotonic), int(wall))
        status = acl2_keyword(self.call(form))
        if status == "ok":
            return status, acl2_octets(self.call("(fn-store-cfg-last-octets state)"))
        if status != "refused":
            raise StoreFault("unexpected policy outcome: {}".format(status))
        return "refused", acl2_keyword(self.call("(fn-store-cfg-last-reason state)"))

    def policy(self, slot):
        return acl2_octets(self.call("(fn-store-cfg-policy '{} state)".format(
            self.literal(slot))))

    def remove_peer(self, name, monotonic, wall):
        """One `peer remove': `:no-such-peer' is ACL2's refusal, not a lookup here."""
        form = "(fn-store-cfg-remove-peer '{} {} {} state)".format(
            self.literal(name), int(monotonic), int(wall))
        status = acl2_keyword(self.call(form))
        if status == "ok":
            return status, acl2_octets(self.call("(fn-store-cfg-last-octets state)"))
        if status != "refused":
            raise StoreFault("unexpected peer outcome: {}".format(status))
        return "refused", acl2_keyword(self.call("(fn-store-cfg-last-reason state)"))

    def config_publication(self, records, frontier, config_records, record,
                           lock_owned, observed_names, profile):
        """ACL2's publication authorization: (status, reason, generation, name).

        PROFILE is the store's decoded profile, opaque: ACL2 reads its
        max-config-generations (D27, PRF-102)."""
        form = "(fn-store-cfg-publication '{} {} '{} '{} {} '{} '{})".format(
            "(" + " ".join(self.literal(r) for r in records) + ")", int(frontier),
            "(" + " ".join(self.literal(r) for r in config_records) + ")",
            self.literal(record), "t" if lock_owned else "nil",
            "(" + " ".join(self.literal(n) for n in observed_names) + ")",
            frame_bridge._lisp_literal(profile))
        timeout = max(ACL2_RECOVER_BASE_SECONDS + ACL2_RECOVER_PER_RECORD_SECONDS * len(records),
                      self.form_timeout(form))
        value = frame_bridge.read_form(self.call(form, timeout=timeout))
        if not (isinstance(value, list) and len(value) == 4):
            raise StoreFault("ACL2 returned a malformed publication authorization")
        status, reason, generation, name = value
        if status == "accepted":
            if not (isinstance(generation, int) and name and isinstance(name, list)):
                raise StoreFault("ACL2 accepted a publication without a generation and name")
            name = frame_bridge.path_component(name)
        return str(status), (str(reason) if reason != [] else "none"), generation, name

    def peer_report(self):
        """The `peer list' report, rendered by ACL2 (`fn-native-admin-peer-report')."""
        return acl2_octets(self.call("(fn-store-cfg-peer-report state)"))

    def prov_post(self):
        """The provenance of a locally posted article, DECIDED IN ACL2.

        `fn-store-prov-post' reads the live configuration for the injecting
        principal and generation, builds `fn-prov-make-post', and answers
        the form the record grammar accepts.  Python neither names a
        provenance nor chooses between the wire and the legacy rendering.
        """
        return acl2_octets(self.call("(fn-store-prov-post state)"))

    def prov_describe(self, evidence):
        """The lossless provenance line for one stored evidence value."""
        return acl2_octets(self.call("(fn-store-prov-describe '{} state)".format(
            self.literal(evidence))))

    def prov_for_msgid(self, msgid):
        """The provenance the live node recorded for this Message-ID, or b''."""
        return acl2_octets(self.call("(fn-store-prov-for-msgid '{} state)".format(
            self.literal(msgid))))

    def pin_count(self):
        return acl2_nat(self.call("(fn-store-sn-pin-count state)"))

    def reserved(self):
        return acl2_nat(self.call("(fn-store-sn-reserved state)"))

    def lookup(self, msgid):
        return acl2_octets(self.call("(fn-store-sn-lookup '" + self.literal(msgid) + " state)"))

    def lookup_found(self, msgid):
        return acl2_boolean(self.call("(fn-store-sn-lookup-foundp '" + self.literal(msgid) + " state)"))

    def close(self):
        if getattr(self, "closed", False):
            return
        if self.proc is None:
            self.closed = True
            self.release_slot()
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
            try:
                for stream in (self.proc.stdin, self.proc.stdout):
                    if stream and not stream.closed:
                        stream.close()
            finally:
                self.closed = True
                self.release_slot()


class Store:
    def __init__(self, root, writable=False, faults=NO_FAULTS, profile=None):
        self.root = Path(root).absolute()
        self.writable = writable
        self.faults = faults
        # `init` may name a preset word (`--profile development|scale|default`,
        # read by ACL2 at `initialize`); None is the frame ACL2 writes when no
        # preset is named.  Opening an existing store decodes its durable
        # frame and does not consult this input.
        if profile is not None and not isinstance(profile, str):
            raise StoreError("store profile word is not text")
        self.profile = profile
        self.lock_fd = None
        self.config = None
        # The replayed configuration: generation, served table and allocation
        # domain, all as ACL2 returned them at the last recover.
        self.config_generation = None
        self.config_served = ()
        self.config_domain = ()
        self.frontier = None
        self.fenced = False
        # Staged names an interrupted publication left behind.  Recovery
        # reports them; they are never adopted as history nor deleted here.
        self.orphans = ()
        # This is a one-use host gate, not a second completion model.  It is
        # minted only after the ACL2 file kernel acknowledged the exact
        # record-directory -> :completing observation.  Any uncertainty means
        # recovered observation, rather than a retry against a stale core.
        self.completion_pending = False
        # The selected-checkpoint outcome of the last recovery (tools/checkpoint.py).
        self.checkpoint_outcome = ("none",)

    @property
    def config_path(self): return self.root / "config.json"
    @property
    def transactions(self): return self.root / "transactions"
    @property
    def staging(self): return self.root / "staging"
    @property
    def lock_path(self): return self.root / "writer.lock"
    @property
    def frontier_path(self): return self.root / "allocation-frontier.json"
    @property
    def anchor_path(self): return self.root / "anchor.fnan"

    def load_anchor(self, acl2):
        """The node's latest accepted anchor, or None if it holds none.

        The record is an FNAN frame; ACL2 decodes it and applies every bound.
        An unreadable or undecodable record is a fault: a store that once held
        a freshness anchor and now cannot show one is not a store with no
        anchor, and must never be silently treated as one.
        """
        if not check_regular(self.anchor_path):
            return (0, None)
        raw = read_regular_bounded(self.anchor_path, ANCHOR_RECORD_BYTES)
        digest = hashlib.sha256(raw[:-TRAILER_BYTES]).digest() if len(raw) > TRAILER_BYTES else b""
        values = acl2.anchor_decode(raw, digest)
        # The blob fields of the :incarnation spec, by position: key,
        # delegate, delegation-signature, nonce, signature and ROOT.
        octets = (1, 2, 5, 8, 9, 10)
        fields = tuple(bytes(value) if index in octets else value
                       for index, value in enumerate(values[1:], start=1))
        return (values[0], fields)

    def write_anchor(self, acl2, incarnation, fields):
        """Replace the durable anchor record with a newer accepted one.

        The monotone rule has already been applied by ACL2 when this runs.
        The bytes reach the final name through a staged write, a barrier and
        an atomic rename, so a crash leaves either the old record or the new
        one and never a truncated frame.
        """
        prefix = acl2.anchor_protected(incarnation, fields)
        contents = prefix + hashlib.sha256(prefix).digest()
        stage = self.staging / ".anchor-{}-{}".format(os.getpid(), os.urandom(12).hex())
        fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        try:
            write_all(fd, contents)
            durable_barrier(fd)
        finally:
            os.close(fd)
        try:
            os.replace(stage, self.anchor_path)
        except BaseException:
            try:
                os.unlink(stage)
            except OSError:
                pass
            raise
        fsync_dir(self.root)

    @property
    def config_dir(self): return self.root / "config"

    def config_record_path(self, generation, bridge=None):
        """The final path of a configuration generation; ACL2 names it."""
        return self.config_dir / frame_bridge.session(bridge).config_record_name(generation)

    def config_record_files(self):
        """The durable configuration records in generation order."""
        if not self.config_dir.is_dir():
            return ()
        names = sorted(entry.name for entry in os.scandir(self.config_dir)
                       if entry.name.endswith(".cfg"))
        return tuple(self.config_dir / name for name in names)

    def _open_lock(self, exclusive, create):
        flags = os.O_RDWR if exclusive else os.O_RDONLY
        if create:
            flags |= os.O_CREAT
        flags |= getattr(os, "O_NOFOLLOW", 0)
        # Opening the lock pathname and contending for the lock are distinct
        # outcomes.  Only a refused lock means another owner holds the store;
        # an absent or unusable lock pathname is an invalid store state.
        try:
            fd = os.open(self.lock_path, flags, 0o600)
        except OSError as error:
            if error.errno == errno.ELOOP:
                raise StoreFault("refusing writer-lock symlink") from error
            raise StoreFault("cannot open writer lock: {}".format(error)) from error
        try:
            if not stat.S_ISREG(os.fstat(fd).st_mode):
                raise StoreFault("refusing non-regular writer lock")
        except BaseException:
            os.close(fd)
            raise
        try:
            fcntl.flock(fd, (fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH) | fcntl.LOCK_NB)
        except OSError as error:
            os.close(fd)
            raise StoreError("store is already locked") from error
        return fd

    def _safe_directory(self, path, create=False):
        try:
            st = os.lstat(path)
        except FileNotFoundError:
            if not create:
                raise StoreFault("missing store directory: {}".format(path))
            path.mkdir(mode=0o700)
            fsync_dir(path.parent)
            st = os.lstat(path)
        if not stat.S_ISDIR(st.st_mode) or stat.S_ISLNK(st.st_mode):
            raise StoreFault("refusing non-directory store path: {}".format(path))
        return st

    def _publish_initial_file(self, final, contents):
        """Stage, barrier, link and barrier one initialization metadata file.

        A partial write to the final name leaves an unparseable store that no
        retry can repair, so the bytes become durable under a staged name and
        reach the final name through a non-overwriting link.  An existing final
        name is reported, never replaced.
        """
        stage = self.staging / (".init-{}-{}".format(os.getpid(), os.urandom(12).hex()))
        fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        try:
            write_all(fd, contents)
            fsync_file(fd)
        finally:
            os.close(fd)
        try:
            try:
                os.link(stage, final)
            except FileExistsError:
                return False
            fsync_dir(self.root)
            return True
        finally:
            try:
                os.unlink(stage)
            except OSError:
                pass

    def initialize(self, bridge=None, groups=DEFAULT_GROUPS):
        # One durable configuration record at generation 1, built and admitted
        # by the core from the operator's group names.
        self._safe_directory(self.root, create=True)
        self.faults.at("init-root-created")
        lock_fd = self._open_lock(exclusive=True, create=True)
        try:
            self._safe_directory(self.transactions, create=True)
            self.faults.at("init-transactions-created")
            self._safe_directory(self.staging, create=True)
            self.faults.at("init-staging-created")
            self._safe_directory(self.config_dir, create=True)
            session = frame_bridge.session(bridge)
            try:
                config = session.metadata_config_frame(self.profile)
            except frame_bridge.BridgeError as error:
                raise StoreError(str(error)) from error
            if self._publish_initial_file(self.config_path, config):
                self.config = self._config_from_metadata(session.metadata_config_decode(config), session)
            else:
                self._load_config(session)
            # A missing allocator alongside committed history would permit
            # reuse of an aborted ID.  It is a fault, never an implicit 0.
            if not self.config_record_files():
                try:
                    octets = frame_bridge.session(bridge).config_record_initial(groups)
                except frame_bridge.BridgeError as error:
                    raise StoreError("refused initial group table: {}".format(error)) from error
                self._publish_initial_file(self.config_record_path(1, bridge), octets)
                fsync_dir(self.config_dir)
            if not check_regular(self.frontier_path) and self.transaction_files():
                raise StoreFault("refusing missing allocator frontier with committed history")
            frontier = session.metadata_frontier_frame(0)
            if self._publish_initial_file(self.frontier_path, frontier):
                self.frontier = 0
            else:
                self._load_frontier(session)
            fsync_regular(self.config_path)
            self.faults.at("init-barrier")
            for path in self.config_record_files():
                fsync_regular(path)
            fsync_regular(self.frontier_path)
            self.faults.at("init-barrier")
            fsync_dir(self.transactions)
            self.faults.at("init-barrier")
            fsync_dir(self.root)
            self.faults.at("init-barrier")
            fsync_dir(self.root.parent)
            self.faults.at("init-barrier")
        finally:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)

    @staticmethod
    def _config_from_metadata(values, bridge=None):
        """The decoded profile, kept opaque as `profile`, and ACL2's reading
        of its fields (`fn-store-profile-summary`): no position is read here.
        `format` is the number ACL2 reports (8, or 7 for a store opened under
        its translation); Python compares it with nothing."""
        session = frame_bridge.session(bridge)
        if not session.profile_admitted(values):
            raise StoreFault("store was written under a profile ACL2 does not admit")
        fmt, max_transactions, _history, max_record, max_article = (
            session.profile_summary(values))
        return {"profile": values,
                "format": fmt,
                "max_payload_bytes": max_article,
                "max_record_octets": max_record,
                "max_transactions": max_transactions}

    def _load_config(self, bridge=None):
        check_regular(self.config_path)
        try:
            raw = read_regular_bounded(self.config_path, 16384)
        except OSError as error:
            raise StoreFault("invalid durable config: {}".format(error)) from error
        if raw.startswith(b"{"):
            raise StoreFault("legacy JSON metadata is retained in place; explicit offline migration is required")
        try:
            session = frame_bridge.session(bridge)
            config = self._config_from_metadata(
                session.metadata_config_decode(raw), session)
        except frame_bridge.BridgeError as error:
            raise StoreFault("invalid durable config frame") from error
        self.config = config

    def _load_frontier(self, bridge=None):
        check_regular(self.frontier_path)
        try:
            raw = read_regular_bounded(self.frontier_path, 4096)
        except OSError as error:
            raise StoreFault("invalid durable allocation frontier: {}".format(error)) from error
        if raw.startswith(b"{"):
            raise StoreFault("legacy JSON allocator is retained in place; explicit offline migration is required")
        try:
            next_txid = frame_bridge.session(bridge).metadata_frontier_decode(raw)
        except frame_bridge.BridgeError as error:
            raise StoreFault("invalid durable allocation frontier frame") from error
        self.frontier = next_txid

    def acquire(self, bridge=None):
        self._safe_directory(self.root)
        self._safe_directory(self.transactions)
        self._safe_directory(self.staging)
        try:
            self.lock_fd = self._open_lock(exclusive=self.writable, create=self.writable)
            # Frontiers are mutable writer-owned state.  Read them only after
            # the process-wide lock prevents a concurrent allocation update.
            self._load_config(bridge)
            self._load_frontier(bridge)
        except BaseException:
            # Metadata syscalls and interruption can fail outside StoreError.
            # Acquisition must not leak ownership when no Store is returned.
            self.close()
            raise

    def close(self):
        # Retire a completion opportunity with its owner.  A future owner must
        # reconstruct state through observed recovery before it can mutate.
        self.completion_pending = False
        if self.lock_fd is not None:
            fd, self.lock_fd = self.lock_fd, None
            try:
                fcntl.flock(fd, fcntl.LOCK_UN)
            finally:
                # A failed close may already have released/reused the number.
                # Retire it before the call so a retry cannot close another FD.
                os.close(fd)

    def transaction_files(self):
        files = []
        try:
            entries = os.scandir(self.transactions)
        except OSError as error:
            raise StoreFault("cannot enumerate transactions") from error
        # The physical read stops one past the profile's bound, so an
        # unbounded directory is never retained; the verdict on what was read
        # (the name grammar, the bound, the gap policy) is ACL2's
        # `fn-store-txn-observation-selected`, as the native host asks it.
        limit = self.config["max_transactions"]
        with entries:
            for entry in entries:
                files.append(entry.name.encode("utf-8", "surrogateescape"))
                if len(files) > limit:
                    break
        pairs = frame_bridge.session().txn_observation(sorted(files), limit)
        if pairs is None:
            raise StoreFault("ACL2 refused the transaction namespace observation")
        result = []
        for sequence, name in pairs:
            path = self.transactions / name
            if path.is_symlink() or not path.is_file():
                raise StoreFault("refusing transaction symlink or non-file")
            result.append((sequence, path))
        return result

    def staging_orphans(self, raw=False):
        """Enumerate staged names an interrupted publication left behind.

        Recovery never adopts one of these as history.  Which of them may be
        unlinked is decided by books/store-sweep.lisp, not here
        (Store.sweep_staging).  `raw' asks for the unabridged list the sweep
        needs; the default is the bounded operator report, whose truncation
        marker is not a name.
        """
        names = []
        try:
            entries = os.scandir(self.staging)
        except OSError as error:
            raise StoreFault("cannot enumerate staging") from error
        with entries:
            for entry in entries:
                if not raw and len(names) >= MAX_STAGING_REPORT:
                    names.append("...")
                    break
                names.append(entry.name)
        return tuple(sorted(names))

    def sweep_staging(self, acl2, held=()):
        """Unlink the staging names the book says no publication holds.

        The deploy gate of 2026-09-20 (finding 5) left one `.stage-' file
        behind across two recoveries because recovery reported orphans and
        collected none.  It collects them now, and `self.orphans' is what is
        left after the sweep, so a name the book refuses to remove is still
        reported rather than hidden.
        """
        observed = self.staging_orphans(raw=True)
        removals = ()
        if observed:
            removals = acl2.sweep_staging(
                [name.encode("utf-8", "surrogateescape") for name in observed],
                [name.encode("utf-8", "surrogateescape") for name in held])
            for name in removals:
                try:
                    (self.staging / name).unlink()
                except FileNotFoundError:
                    pass
                except OSError as error:
                    # An unlink that neither succeeded nor left the name
                    # absent is an uncertain observation, not a clean sweep.
                    raise StoreIndeterminate(
                        "cannot collect staging orphan {}: {}".format(name, error)) from error
        self.orphans = self.staging_orphans()
        return tuple(removals)

    def durable_records(self, acl2):
        records = []
        aggregate = 0
        # The bounded read is sized from the model's record bound, not from a
        # host copy of it.
        session = frame_bridge.session(acl2)
        constants = session.constants
        bound = constants["overhead"] + constants["max_store"]
        for sequence, path in self.transaction_files():
            check_regular(path)
            raw = read_regular_bounded(path, bound)
            record = unframe(raw)
            aggregate += len(record)
            # The replay bound every open checks per record, ACL2's
            # (`fn-profile-replay-within-boundp`, as the native open asks).
            if not session.replay_within_bound(self.config["profile"], aggregate):
                raise StoreFault("transaction recovery input exceeds configured bound")
            if acl2.record_sequence(record) != sequence:
                raise StoreFault("record sequence does not match immutable filename")
            records.append(record)
        return records

    def config_records(self):
        """The durable configuration record history, oldest first.

        A store with no configuration record is a refused store -- a distinct
        outcome from an uncertain persistence observation, and never a
        compiled-in default.  The core decides whether the records replay.
        """
        paths = self.config_record_files()
        if not paths:
            raise StoreFault("refusing store with no durable configuration record")
        records = []
        for path in paths:
            check_regular(path)
            records.append(read_regular_bounded(path, CONFIG_RECORD_BYTES))
        return records

    def publish_config_record(self, acl2, octets):
        """Make one admitted configuration record durable; return its generation.

        ACL2 authorizes the publication (`fn-store-cfg-publication`, i.e.
        `fn-native-admin-publication-authorize`): it allocates the
        generation, names the file, checks that this process holds the
        writer lock and that the name is unoccupied, and asks whether the
        store with the record appended reopens.  A refusal is printed with
        ACL2's reason and returns None (exit 1); an I/O failure after
        authorization is uncertain (exit 3), never either.
        """
        observed = tuple(entry.name.encode("utf-8")
                         for entry in os.scandir(self.config_dir))
        status, reason, generation, name = acl2.config_publication(
            self.durable_records(acl2), self.frontier, self.config_records(),
            bytes(octets), self.lock_fd is not None and self.writable, observed,
            self.config["profile"])
        if status != "accepted":
            print("store: refused configuration record: {}".format(reason),
                  file=sys.stderr)
            return None
        self._write_config_file(self.config_dir / name, generation, octets)
        return generation

    def write_config_record(self, generation, octets, bridge=None):
        """Durably write a record whose generation an ACL2 owner allocated.

        tools/run_owner.py's RECONFIGURE: the owner core admitted the record
        and chose GENERATION; ACL2 names the file (config_record_path)."""
        self._write_config_file(self.config_record_path(generation, bridge),
                                generation, octets)

    def _write_config_file(self, path, generation, octets):
        try:
            if not self._publish_initial_file(path, octets):
                raise StoreFault("configuration generation {} already exists".format(generation))
            fsync_regular(path)
            fsync_dir(self.config_dir)
        except OSError as error:
            raise StoreIndeterminate(
                "configuration record {} may not be durable: {}".format(generation, error)) from error

    def recover(self, acl2):
        # Recovery owns the mutation gate from the start of scanning through
        # the final barrier, including unexpected read/runtime failures.
        self.fenced = True
        self.completion_pending = False
        try:
            # A replacement may have become visible before its directory
            # barrier failed. Recover the observed frontier under the held
            # store lock, never a cached pre-error allocation value.
            self._load_frontier(acl2)
            config_records = self.config_records()
            records = self.durable_records(acl2)
            self.orphans = self.staging_orphans()
            if acl2.recover(records, self.frontier, config_records) != "recovering":
                raise StoreFault("ACL2 replay rejected committed transaction history or configuration history")
            self.config_generation = acl2.config_generation()
            self.config_served = acl2.config_served()
            self.config_domain = acl2.config_domain()
        except (StoreFault, StoreIndeterminate):
            self.fenced = True
            raise
        except StoreError as error:
            # Committed history the core cannot decode is an invalid store
            # state, not a clean refusal of a request: reopening will fail the
            # same way until an operator repairs or salvages the store.
            self.fenced = True
            raise StoreFault(
                "cannot reconstruct committed history: {}".format(error)) from error
        self.faults.at("recover-replayed")
        # A directory-barrier failure may have left an observed link in cache.
        # Validate and replay first, then establish the recovered namespace
        # frontier before treating it as a usable durable state.
        try:
            for barrier in (
                    lambda: fsync_regular(self.config_path),
                    lambda: fsync_regular(self.frontier_path),
                    lambda: fsync_dir(self.transactions),
                    lambda: fsync_dir(self.root),
                    lambda: fsync_dir(self.root.parent)):
                try:
                    barrier()
                except OSError:
                    # A failed barrier is an uncertain persistence observation;
                    # place that fact in the file kernel before fencing the host.
                    self._observe(acl2, "recovery-barrier", "uncertain")
                    raise
                phase = self._observe(acl2, "recovery-barrier", "ok")
                if phase not in {"recovering", "ready"}:
                    raise StoreFault("ACL2 rejected recovered barrier ordering")
                self.faults.at("recover-barrier")
            if phase != "ready":
                raise StoreFault("ACL2 did not complete all recovery barriers")
        except OSError as error:
            self.fenced = True
            raise StoreIndeterminate("cannot establish recovered namespace frontier") from error
        self.fenced = False
        # The barriers are done, so the file kernel is :ready and holds no
        # record candidate: books/store-sweep.lisp's gate is open and the
        # recovered process holds no staging name of its own.  What survives
        # the sweep is what `self.orphans' reports.
        self.sweep_staging(acl2)
        self.checkpoint_outcome = self._checkpoint_hook(acl2, records)
        return records

    def _checkpoint_hook(self, acl2, records):
        """C2-09: decode the selected checkpoint generation and replay only its suffix.

        The journal replayed above stays the authority.  The outcome is one of
        ("none",), ("ok", generation, sequence, differential) or ("corrupt",
        reason); a corrupt selected generation is reported, never replaced by
        an older one.  ACL2's differential mismatch is corruption on every
        open because the selected diagnostic image disagrees with full replay.
        """
        from tools import checkpoint
        try:
            outcome = checkpoint.restore_selected(self, acl2, records, self.frontier)
        except checkpoint.CheckpointCorrupt as error:
            return ("corrupt", str(error))
        return outcome

    def advance_frontier(self, acl2, current_txid):
        """Report each allocator observation to the file kernel in order."""
        self._require_writer()
        if self.fenced:
            raise StoreIndeterminate("store is fenced pending recovery")
        if current_txid != self.frontier:
            self.fenced = True
            raise StoreFault("ACL2 allocator and durable frontier disagree")
        try:
            metadata = frame_bridge.session(acl2)
            next_frontier = metadata.metadata_frontier_next(current_txid)
            if next_frontier is None:
                raise StoreError("ACL2 refused exhausted transaction-ID domain")
            contents = metadata.metadata_frontier_frame(next_frontier)
        except frame_bridge.BridgeError as error:
            raise StoreFault("ACL2 refused allocation frontier") from error
        stage = self.staging / (".allocation-{}-{}".format(os.getpid(), os.urandom(12).hex()))
        publication_attempted = False
        try:
            # A bridge reply is an observation boundary even before any
            # physical write.  A lost reply leaves logical state unknown and
            # must therefore fence this owner for observed recovery.
            if self._observe(acl2, "start-frontier") != "frontier-staged":
                self.fenced = True
                raise StoreFault("ACL2 rejected allocator start")
            fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            try:
                self.faults.at("frontier-created")
                write_all(fd, contents)
                self.faults.at("frontier-written")
                fsync_file(fd)
            finally:
                os.close(fd)
            # A real file barrier has happened.  If the bridge reply is lost,
            # do not continue as though its logical observation were known.
            self.fenced = True
            if self._observe(acl2, "frontier-file", "ok") != "frontier-data-durable":
                raise StoreFault("ACL2 rejected durable allocator file")
            self.faults.at("frontier-staged-durable")
            publication_attempted = True
            # Replacement is a namespace attempt; close the mutation gate
            # before both the syscall and its corresponding ACL2 observation.
            self.fenced = True
            try:
                os.replace(stage, self.frontier_path)
            except OSError:
                self._observe(acl2, "frontier-replace", "error")
                raise
            self.faults.at("frontier-replaced")
            if self._observe(acl2, "frontier-replace", "ok") != "frontier-attempted":
                # The replacement already reached the namespace; a core that
                # will not record it leaves the frontier unresolved.
                raise StoreIndeterminate(
                    "ACL2 rejected allocator replacement after the namespace attempt")
            self.faults.at("frontier-attempted")
            self.fenced = True
            try:
                fsync_dir(self.root)
            except OSError:
                self._observe(acl2, "frontier-directory", "error")
                raise
            self.faults.at("frontier-durable")
            if self._observe(acl2, "frontier-directory", "ok") != "reserved":
                raise StoreIndeterminate(
                    "ACL2 rejected durable allocator frontier after its barrier")
            # The exact file-kernel reservation is installed.  Preparation
            # remains the next ACL2 gate while the writer lock is still held.
            self.fenced = False
            self.frontier = next_frontier
            self.faults.at("frontier-reserved")
            return next_frontier
        except OSError as error:
            if publication_attempted:
                self.fenced = True
                raise StoreIndeterminate("allocation-frontier update is indeterminate") from error
            # Before final-name replacement, the staged file does not make a
            # reservation visible.  The kernel returns to :ready explicitly.
            self._observe(acl2, "frontier-file", "known-fail")
            raise StoreError("known pre-publication allocator failure: {}".format(error)) from error

    def publish(self, acl2, sequence, record):
        self._require_writer()
        if self.fenced:
            raise StoreIndeterminate("store is fenced pending recovery")
        name = acl2.transaction_name(sequence)
        final = self.transactions / name
        stage = self.staging / (".stage-{}-{}".format(os.getpid(), os.urandom(12).hex()))
        data = frame(record)
        publication_attempted = False
        try:
            fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            try:
                self.faults.at("record-created")
                write_all(fd, data)
                self.faults.at("record-written")
                fsync_file(fd)
            finally:
                os.close(fd)
            self.fenced = True
            if self._observe(acl2, "record-file", "ok") != "record-data-durable":
                raise StoreFault("ACL2 rejected durable record file")
            # The staged record is data durable and no final name has been
            # attempted.  This position is exactly known, so a failure here is
            # a known abort rather than an uncertain publication.
            self.fenced = False
            self.faults.at("record-staged-durable")
            publication_attempted = True
            self.fenced = True
            try:
                os.link(stage, final)
            except OSError:
                self._observe(acl2, "record-link", "error")
                raise
            self.faults.at("record-linked")
            if self._observe(acl2, "record-link", "ok") != "record-attempted":
                # The final-name attempt already reached the filesystem.  A
                # core that will not record it leaves publication unresolved,
                # which is recovery's question, not a host-known failure.
                self.fenced = True
                raise StoreIndeterminate(
                    "ACL2 rejected record publication after the final-name attempt")
            self.faults.at("record-attempted")
            try:
                fsync_dir(self.transactions)
            except OSError:
                self._observe(acl2, "record-directory", "error")
                raise
            self.faults.at("record-durable")
            if self._observe(acl2, "record-directory", "ok") != "completing":
                raise StoreIndeterminate(
                    "ACL2 rejected record directory barrier after publication")
            # The directory barrier and its ACL2 reply were both observed.
            # This sole opportunity is consumed before any finish call.
            self.completion_pending = True
            self.faults.at("record-completing")
            # Staging files are ignored by recovery.  Their best-effort cleanup
            # occurs only after the final namespace barrier succeeded.
            try:
                os.unlink(stage)
                self.faults.at("record-stage-unlinked")
                fsync_dir(self.staging)
            except OSError:
                pass
            self.faults.at("record-staging-cleaned")
            return "durable"
        except StoreIndeterminate:
            raise
        except OSError as error:
            # The link invocation itself can have reached the filesystem even
            # when no final name is observable afterward.  Absence is not a
            # proof of non-publication under this failure model.
            if publication_attempted:
                self.fenced = True
                raise StoreIndeterminate("transaction publication outcome is indeterminate") from error
            # No final namespace attempt occurred.  Do not first manufacture
            # an :aborting file event here: the proved fn-sn-known-abort
            # transition consumes the exact staged/data-durable candidate and
            # advances the matching live node through its real abort branch.
            raise StoreError("known pre-publication store failure: {}".format(error)) from error

    def finish(self, acl2):
        """Open the writer gate only after exact fn-sn durable completion."""
        self._require_writer()
        if not self.fenced or not self.completion_pending:
            raise StoreIndeterminate("durable completion was not pending")
        # Consume before the ACL2 call: a rejected or lost reply cannot be
        # retried on this owner, even if the core completed before its reply.
        self.completion_pending = False
        self.faults.at("finish-consumed")
        try:
            completion = acl2.finish()
        except (StoreError, OSError) as error:
            self.fenced = True
            raise StoreIndeterminate("ACL2 completion failed after publication") from error
        if completion != "durable":
            self.fenced = True
            raise StoreIndeterminate("ACL2 rejected durable completion after publication")
        self.fenced = False
        self.faults.at("finish-durable")
        return completion

    def _require_writer(self):
        if not self.writable or self.lock_fd is None:
            raise StoreError("mutation requires a live exclusive store owner")

    def _observe(self, acl2, operation, result="ok"):
        """Submit one already-observed filesystem result and keep failure fenced."""
        try:
            return acl2.io(operation, result)
        except (StoreError, OSError) as error:
            self.fenced = True
            self.completion_pending = False
            raise StoreIndeterminate(
                "ACL2 could not record {} observation".format(operation)) from error


def metadata(msgid, payload, bridge=None):
    """Content identity, derived in ACL2 by `books/identity`, v1 profile.

    The host hashes two byte strings it does not interpret; ACL2 decides the
    domain labels, the length prefixes, the version and algorithm octets, the
    order of each preimage and the rendering.  The obligation binds the
    CANONICAL subject identity octets; what comes back here is each identity's
    text, because a store record metadata field, a journal record and an NNTP
    header are all strings.

    The third element is the LEGACY provenance label and nothing asks for
    it any more on the POST path: `durable_post' takes its evidence from
    `fn-store-prov-post' (books/provenance), so ACL2 owns the decision.  It
    is still returned because the two BP drivers (tools/run_bp_ingress.py,
    tools/run_bp_receive.py) read it, and moving them onto
    `fn-prov-make-bp' is an open item of the w10/provenance lane, recorded
    in planning/lanes/HANDOFF-w10-provenance.md.
    """
    session = frame_bridge.session(bridge)
    try:
        subject = session.subject_id(payload)
        obligation = session.obligation_id(msgid, subject)
        return (session.identity_text(obligation),
                session.identity_text(subject),
                b"unsigned-legacy-v0")
    except frame_bridge.BridgeError as error:
        raise StoreError("ACL2 refused to derive content identity") from error


def group_codes(groups, store, bridge=None):
    """Codes in the allocation domain the core handed `store` at recover."""
    session = frame_bridge.session(bridge)
    if not groups:
        raise StoreError("provide one or more distinct configured groups")
    try:
        return session.group_codes(groups, store.config_domain)
    except frame_bridge.BridgeError as error:
        raise StoreError("unknown or duplicate configured group") from error


def conservative_charge(payload, bridge=None):
    """`fn-charge-for-payload`, proved positive and monotone in length."""
    return frame_bridge.session(bridge).charge(len(payload))


def profile_config(profile=None, bridge=None):
    """A preset's values (None: the profile `init` writes by default), as
    ACL2 frames and decodes them."""
    session = frame_bridge.session(bridge)
    return Store._config_from_metadata(
        session.metadata_config_decode(session.metadata_config_frame(profile)),
        session)


def validate_post_boundary(msgid, payload, groups, charge, config, bridge=None):
    """One call: `fn-sbud-post-boundary` applies every bound in the model.

    `config["profile"]` is the decoded profile ACL2 returned at open, handed
    back opaque (format 8, D27).  A refusal is relayed as ACL2's verdict word
    (`payload-bound`, `bad-message-id`, ...); Python keeps no text table of
    its own."""
    verdict = frame_bridge.session(bridge).post_boundary(
        config["profile"], msgid, len(payload), len(groups), charge)
    if verdict != "ok":
        raise StoreError("ACL2 refused the post boundary: {}".format(verdict))


def publication_admissible(store, bridge=None, kind="article"):
    """Whether the recovered Store may publish one more KIND record.

    `fn-sbud-verdict` under the store's persisted profile, through the ACL2
    session that recovered the Store (as the native `store post` asks)."""
    return frame_bridge.session(bridge).publication_verdict(
        store.config["profile"], kind) == "admissible"


def command_init(args):
    store = Store(args.store, writable=True, profile=args.profile)
    try:
        store.initialize(groups=tuple(args.group) if args.group else DEFAULT_GROUPS)
        store.acquire()
        print("initialized {}".format(store.root))
    finally:
        store.close()


def command_group(args):
    """`group create <name>` / `group retire <name>`: one configuration record.

    The core admits or refuses the request (exit 1 with the reason); an
    admitted record is made durable under its generation, and an I/O failure
    after admission is reported uncertain (exit 3), never as either.
    """
    import time
    kind = {"create": ":create-group", "retire": ":remove-group"}[args.action]
    store, bridge, unused_records = open_live_store(args.store, writable=True)
    try:
        status, payload = bridge.reconfigure(kind, args.name, time.monotonic(), time.time())
        if status != "ok":
            print("store: refused group {}: {}".format(args.action, payload), file=sys.stderr)
            return EXIT_REFUSED
        generation = store.publish_config_record(bridge, payload)
        if generation is None:
            return EXIT_REFUSED
        print("group {} name={} generation={}".format(
            "created" if args.action == "create" else "retired", args.name, generation))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def command_capacity(args):
    """`capacity <n>`: one configuration record that sets the retention capacity.

    Three outcomes stay distinct (D13).  The core refuses a capacity below the
    live reservation total (exit 1, with the reason on stderr).  Every
    configuration record is then gated, before anything becomes durable, by
    `fn-native-admin-publication-authorize` (Store.publish_config_record):
    configuration records live beside the journal rather than interleaved in
    it (specs/reconfiguration.md section 8 item 1), so a decrease admitted
    against today's reservation total would be applied by recovery BEFORE any
    article replays, and could brick a store that opens fine today.  ACL2's
    candidate-reopen predicate is the exact check; a refused candidate is
    exit 1 with the reason `candidate` and nothing is written.
    An I/O failure after admission is uncertain (exit 3), never either.
    """
    import time
    store, bridge, unused_records = open_live_store(args.store, writable=True)
    try:
        status, payload = bridge.reconfigure(
            ":set-capacity", "", time.monotonic(), time.time(), n=args.capacity)
        if status != "ok":
            print("store: refused capacity: {}".format(payload), file=sys.stderr)
            return EXIT_REFUSED
        generation = store.publish_config_record(bridge, payload)
        if generation is None:
            return EXIT_REFUSED
        print("capacity set n={} generation={}".format(args.capacity, generation))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def peer_listing(bridge):
    """One line per configured peer, as the native `peer list' prints it.

    ACL2 enumerates, selects and renders every field
    (`fn-native-admin-peer-report' through `fn-store-cfg-peer-report');
    this splits the octets into lines and formats nothing.
    """
    return [line.decode("utf-8", "replace")
            for line in bridge.peer_report().split(b"\n") if line]


def command_peer(args):
    """`peer add|remove|list': the peer table as configuration records.

    Three outcomes stay distinct: an admitted record that becomes durable is
    exit 0, a record the core refuses (malformed, unknown peer, a bound) is
    exit 1 with ACL2's named reason, and an I/O failure after admission is
    exit 3 -- the record may or may not be on disk and the next open decides.
    """
    import time
    writable = args.action != "list"
    store, bridge, unused_records = open_live_store(args.store, writable=writable)
    try:
        if args.action == "list":
            for line in peer_listing(bridge):
                print(line)
            return EXIT_OK
        if args.action == "add":
            status, payload = bridge.set_peer(peer_arguments(args), time.monotonic(), time.time())
        else:
            status, payload = bridge.remove_peer(
                args.name.encode("utf-8"), time.monotonic(), time.time())
        if status != "ok":
            print("store: refused peer {}: {}".format(args.action, payload), file=sys.stderr)
            return EXIT_REFUSED
        generation = store.publish_config_record(bridge, payload)
        if generation is None:
            return EXIT_REFUSED
        print("peer {} name={} generation={}".format(
            "added" if args.action == "add" else "removed", args.name, generation))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def peer_arguments(args):
    """The operator's words, typed but not interpreted: ACL2 decides the record."""
    host, _, port = (args.nntp or "").rpartition(":")
    return {
        "name": args.name.encode("utf-8"),
        "path_identity": (args.path_identity or args.name).encode("utf-8"),
        "endpoint": (host or args.bp or "").encode("utf-8"),
        "port": int(port) if port.isdigit() else 0,
        "inbound_groups": (args.inbound_groups or "").encode("utf-8"),
        "inbound_max_octets": args.inbound_max_octets,
        "inbound_max_inflight": args.inbound_max_inflight,
        "outbound_groups": (args.outbound_groups or "").encode("utf-8"),
        "streaming": bool(args.streaming),
        "max_queue": args.max_queue,
        "backoff_ms": args.backoff_ms,
        "auth_kind": "principal" if args.principal else "source-address",
        "auth_value": (args.principal or args.source_address or "").encode("utf-8"),
        # D23: principals this peer may carry to us, unverified here.
        "carries": [c.encode("utf-8") for c in (getattr(args, "carries", None) or ())],
    }


def command_policy(args):
    """`policy set|get <slot> [value]': the node's own configuration slots.

    `path-identity` is the one peering needs: `fn-peer-local-identity` reads
    it and RFC 5537 section 3.5 loop suppression cannot fire while it is
    unset. Three outcomes stay distinct exactly as `peer` keeps them.
    """
    import time
    writable = args.action == "set"
    store, bridge, unused_records = open_live_store(args.store, writable=writable)
    try:
        if args.action == "get":
            print("{}={}".format(
                args.slot, bridge.policy(args.slot.encode("utf-8")).decode(
                    "utf-8", "replace")))
            return EXIT_OK
        status, payload = bridge.set_policy(
            args.slot.encode("utf-8"), (args.value or "").encode("utf-8"),
            time.monotonic(), time.time())
        if status != "ok":
            print("store: refused policy set: {}".format(payload), file=sys.stderr)
            return EXIT_REFUSED
        generation = store.publish_config_record(bridge, payload)
        if generation is None:
            return EXIT_REFUSED
        print("policy set {}={} generation={}".format(
            args.slot, args.value, generation))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def command_config(args):
    """Print the replayed configuration: generation, served table, domain."""
    store, bridge, unused_records = open_live_store(args.store, writable=False)
    try:
        print("generation={} served={} domain={}".format(
            store.config_generation, ",".join(store.config_served),
            ",".join(store.config_domain)))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def open_live_store(path, writable, faults=NO_FAULTS):
    # The bridge first, and the Store's metadata decoded on it: acquiring
    # without one opens a second, process-wide framing ACL2 only to decode
    # two small frames, which the recovery bridge then replaces.
    bridge = Acl2Store()
    store = Store(path, writable=writable, faults=faults)
    try:
        store.acquire(bridge)
    except BaseException:
        bridge.close()
        raise
    try:
        records = store.recover(bridge)
        return store, bridge, records
    except BaseException:
        if bridge is not None:
            bridge.close()
        store.close()
        raise


CLI_FAULTS = {
    # Documented test-only hooks.  The publication path holds no injection
    # branch; each name selects one point for the scripted injector.
    "prepublish": lambda: ScriptedFaults(
        "record-staged-durable", StoreError("injected known abort before publication")),
    "postpublish": lambda: ScriptedFaults(
        "record-attempted",
        StoreIndeterminate("indeterminate injected failure after final publication")),
}


def durable_post(store, bridge, records_count, msgid, payload, codes, charge,
                 evidence=None):
    """The durable acceptance path, shared by the CLI and the served POST.

    ACL2 decides: `bridge.prepare` is fn-node-prepare and `store.finish` is the
    exact fn-sn durable completion.  This function performs I/O around those
    decisions and reports the sequence it committed.  It never invents a
    durable status.
    """
    current_txid = bridge.next_txid()
    next_frontier = store.advance_frontier(bridge, current_txid)
    obligation, subject, unused_legacy_evidence = metadata(msgid, payload)
    # Transit supplies the exact ACL2-derived peer evidence its acceptance
    # decision used.  Local POST leaves this unset and uses ACL2's local
    # provenance as before.
    evidence = bridge.prov_post() if evidence is None else evidence
    action = bridge.prepare(msgid, payload, codes, obligation,
                            subject, evidence, charge)
    if action != "prepared":
        # The allocator reservation is durable even for a synchronous
        # semantic refusal.  The file kernel consumes it; Python only
        # reports the already-observed allocator sequence.
        store.fenced = True
        if bridge.refuse_reservation() != "refused":
            raise StoreIndeterminate("ACL2 could not consume refused reservation")
        raise StoreError("ACL2 refused post: {}".format(action))
    record = bridge.pending_record()
    try:
        store.publish(bridge, records_count, record)
    except StoreIndeterminate:
        raise
    except StoreError:
        # A pre-publication staging failure has no final-name event.  Its
        # exact candidate is resolved through fn-sf/fn-node; a bridge
        # inconsistency stays fenced for observed replay.
        if not store.fenced:
            store.fenced = True
            if bridge.known_abort() != "aborted":
                raise StoreIndeterminate("ACL2 rejected known pre-publication abort")
        raise
    # Final-name publication and its directory barrier have put the file
    # kernel in :completing.  Only fn-sn-finish performs the exact actual
    # node durable completion; there is no host durable-status string.
    store.fenced = True
    store.finish(bridge)
    return records_count


def post_article(store, bridge, records_count, msgid, payload, groups, charge):
    """Post one article through an open writable store and its bridge.

    Returns (sequence, charge) for a durable commit and (None, charge) for a
    duplicate.  Every refusal, uncertainty and fault is raised as the store
    error that names it, so the CLI and the owner map one outcome to one code.
    """
    codes = group_codes(groups, store)
    charge = charge if charge is not None else conservative_charge(payload)
    validate_post_boundary(msgid, payload, codes, charge, store.config)
    existing = bridge.existing_action(msgid, payload, codes)
    if existing == "duplicate":
        return None, charge
    if existing == "conflict":
        raise StoreError("conflicting immutable Message-ID")
    if not publication_admissible(store, bridge):
        raise StoreError("transaction count has reached configured bound")
    return (durable_post(store, bridge, records_count, msgid, payload, codes, charge),
            charge)


def post_via_owner(control, msgid, payload, groups, charge):
    """Thin client of tools/run_owner.py: one request line, one reply line."""
    import socket
    line = "POST {} {} {} {}\n".format(msgid.decode("ascii"), ",".join(groups),
                                       "-" if charge is None else charge, len(payload))
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as sock:
        sock.settimeout(ACL2_RECOVER_BASE_SECONDS + 60)
        sock.connect(control)
        sock.sendall(line.encode("ascii") + payload)
        reply = b""
        while not reply.endswith(b"\n"):
            chunk = sock.recv(4096)
            if not chunk:
                break
            reply += chunk
    reply = reply.strip().decode("utf-8", "replace")
    if reply.startswith("committed ") or reply == "duplicate":
        print(reply)
        return EXIT_OK
    print("store: {}".format(reply), file=sys.stderr)
    if reply.startswith("refused"):
        return EXIT_REFUSED
    if reply.startswith("uncertain"):
        return EXIT_UNCERTAIN
    return EXIT_FAULT


def command_post(args, faults=NO_FAULTS):
    """Post one article.  `faults` is the test-only injector; the CLI hook wins."""
    msgid = args.message_id.encode("ascii")
    # A work bound on the read, not the admission bound: the store record
    # ceiling ACL2 reports (`*fn-frame-max-store-payload*`); the profile's
    # payload bound is applied by `fn-sbud-post-boundary`.
    payload = read_regular_bounded(args.payload,
                                   frame_bridge.session().constants["max_store"])
    # Optional: harnesses build argument objects without every CLI flag.
    owner = getattr(args, "owner", None)
    if owner is not None:
        return post_via_owner(owner, msgid, payload, args.group, args.charge)
    if args.inject_fault is not None:
        faults = CLI_FAULTS[args.inject_fault]()
    store, bridge, records = open_live_store(args.store, writable=True, faults=faults)
    try:
        sequence, charge = post_article(store, bridge, len(records), msgid, payload,
                                        args.group, args.charge)
        if sequence is None:
            print("duplicate")
            return 0
        print("committed sequence={} charge={}".format(sequence, charge))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def orphan_report(store):
    """Name staged orphans so recovery reports them instead of hiding them."""
    if not store.orphans:
        return "staging-orphans=0"
    return "staging-orphans={} [{}]".format(len(store.orphans), " ".join(store.orphans))



# -----------------------------------------------------------------------------
# The external freshness anchor (books/anchor.lisp, specs/anchor.md)
#
# FLR-003: a valid store image cannot show it is not an old snapshot.
# A Roughtime response bound to a nonce this node chose can.  Python obtains
# and parses it and runs Ed25519; ACL2 owns the statement, the octets the
# signatures cover, the ordering and the monotone rule.


def pinned_keys():
    """The long-term keys this node trusts, from tools/roughtime_servers.json."""
    from tools import roughtime
    return [base64.b64decode(entry["public_key_base64"])
            for entry in roughtime.load_servers().values()]


def obtain_anchor(args):
    """One anchor, from a pinned server or a captured response.

    Returns (anchor, None) or (None, reason).  A reason is never a refusal:
    not reaching a server means the freshness question is unanswered.
    """
    from tools import crypto_host, roughtime
    try:
        vector = getattr(args, "anchor_vector", None)
        if vector:
            record = json.loads(Path(vector).read_bytes())
            return roughtime.parse_response(
                bytes.fromhex(record["response_hex"]),
                bytes.fromhex(record["nonce_hex"]),
                bytes.fromhex(record["key_id_hex"]),
                record.get("server", "captured")), None
        servers = roughtime.load_servers()
        name = getattr(args, "anchor_server", None) or "int08h"
        if name not in servers:
            return None, "no pinned server named {}".format(name)
        return roughtime.query(servers[name],
                               getattr(args, "anchor_timeout", 5.0))[0], None
    except crypto_host.CryptoUnavailable as error:
        return None, str(error)
    except (roughtime.RoughtimeError, OSError, ValueError, KeyError) as error:
        return None, "{}: {}".format(type(error).__name__, error)


def anchor_verdict(bridge, anchor):
    """`fn-anchor-signatures-okp` of this anchor: the Ed25519 seam, only.

    This is one of the two values the host owes the model, and
    `fn-anchor-node-accept-observed-is-node-accept`,
    `fn-anchor-node-advance-observed-is-node-advance` and
    `fn-anchor-restore-observed-is-restore` (books/anchor-invariants.lisp)
    hold exactly when it is what that seam names.  Two checks make the chain:
    the pinned long-term key over the delegation, and the delegated key over
    the response.

    The other seam value is `anchor.one_nonce`, passed alongside it; the
    delegation validity window is neither, because
    `fn-anchor-verifiedp-observed` applies it inside the entry.

    ACL2 rebuilds both signed messages from the record -- including the root,
    which is now a field -- and if its reconstruction and the octets on the
    wire disagree, that is a fault, not a verdict.
    """
    from tools import crypto_host, roughtime
    signed = bridge.anchor_signed_octets(anchor.radius, anchor.midpoint, anchor.root)
    if signed != roughtime.RESPONSE_CONTEXT + anchor.srep:
        raise StoreFault("ACL2 and the wire disagree about the signed response")
    delegation = bridge.anchor_delegation_octets(anchor.fields())
    if delegation != roughtime.DELEGATION_CONTEXT + anchor.dele:
        raise StoreFault("ACL2 and the wire disagree about the signed delegation")
    return (crypto_host.verify(anchor.key_id, delegation, anchor.delegation_signature)
            and crypto_host.verify(anchor.delegate, signed, anchor.signature))


def command_anchor(args):
    """Obtain one anchor and record it durably if the model accepts it."""
    bridge = Acl2Store()
    store = Store(args.store, writable=True)
    try:
        store.acquire(bridge)
    except BaseException:
        bridge.close()
        raise
    try:
        incarnation, held = store.load_anchor(bridge)
        anchor, reason = obtain_anchor(args)
        if anchor is None:
            print("anchor uncertain: {}".format(reason))
            return EXIT_UNCERTAIN
        fields = anchor.fields()
        status, why = bridge.anchor_accept(
            pinned_keys(), held, incarnation, fields,
            anchor_verdict(bridge, anchor), anchor.one_nonce)
        if status == "accepted":
            store.write_anchor(bridge, incarnation, fields)
            print("anchor accepted server={} midpoint_us={} radius_us={} "
                  "incarnation={}".format(anchor.server, anchor.midpoint,
                                          anchor.radius, incarnation))
            return EXIT_OK
        if status == "uncertain":
            print("anchor uncertain: {}".format(why))
            return EXIT_UNCERTAIN
        print("anchor refused: {}".format(why))
        return EXIT_REFUSED
    finally:
        if bridge is not None:
            bridge.close()
        store.close()


def anchor_restore_check(store, bridge, args):
    """The monotone rule over a recovered image.  Returns (report, exit code).

    A store that never recorded an anchor has nothing to be stale against and
    is reported as such.  One that did must show an anchor newer than the one
    its durable records stand under, or the restore is refused.
    """
    incarnation, referenced = store.load_anchor(bridge)
    if referenced is None:
        return "anchor=none", EXIT_OK
    anchor, reason = obtain_anchor(args)
    if anchor is None:
        return "anchor=uncertain [{}]".format(reason), EXIT_UNCERTAIN
    status, why, next_incarnation = bridge.anchor_restore(
        pinned_keys(), incarnation, referenced, anchor.fields(),
        anchor_verdict(bridge, anchor), anchor.one_nonce)
    if status == "accepted":
        store.write_anchor(bridge, next_incarnation, anchor.fields())
        return "anchor=accepted incarnation={}".format(next_incarnation), EXIT_OK
    if status == "uncertain":
        return "anchor=uncertain [{}]".format(why), EXIT_UNCERTAIN
    return "anchor=refused:{}".format(why), EXIT_REFUSED


def command_recover(args):
    from tools import checkpoint
    store, bridge, records = open_live_store(args.store, writable=True)
    try:
        report, code = anchor_restore_check(store, bridge, args)
        print("recovered transactions={} articles={} {} {} {}".format(
            len(records), bridge.article_count(), orphan_report(store), report,
            checkpoint.describe(store.checkpoint_outcome)))
        # Three outcomes stay distinct: an uncertain or refused anchor keeps its
        # own code; otherwise a corrupt selected generation is its own fault
        # code, because the journal recovered and the checkpoint subsystem did
        # not.
        if code != EXIT_OK:
            return code
        return EXIT_FAULT if store.checkpoint_outcome[0] == "corrupt" else EXIT_OK
    finally:
        bridge.close()
        store.close()


def command_status(args):
    store, bridge, records = open_live_store(args.store, writable=False)
    try:
        print("transactions={} articles={} {} unsigned-legacy-experiment".format(
            len(records), bridge.article_count(), orphan_report(store)))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def command_inspect(args):
    store, bridge, unused_records = open_live_store(args.store, writable=False)
    try:
        msgid = args.message_id.encode("ascii")
        if not bridge.lookup_found(msgid):
            # A known absence is a clean refusal, not a fault.
            return EXIT_REFUSED
        if args.provenance:
            # ACL2 renders the whole line (fn-prov-describe); this prints it.
            # An article accepted before the typed record existed prints as
            # the legacy kind, with the string the writer of the day wrote.
            line = bridge.prov_for_msgid(msgid)
            if not line:
                return EXIT_REFUSED
            sys.stdout.buffer.write(line + b"\n")
            return EXIT_OK
        payload = bridge.lookup(msgid)
        sys.stdout.buffer.write(payload)
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def read_keyring_file(path):
    """Lines of '<creator-hex> <public-key-hex>', as tools/stx.py --keyring
    reads them.  The keyring is supplied per invocation, not persisted: the
    durable configuration history (books/node-config) does not carry one yet,
    and D21 records that as the open half of the reconfiguration story."""
    pairs = []
    with open(path, "r") as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            fields = line.split()
            if len(fields) != 2:
                raise StoreError("keyring line is not '<id-hex> <key-hex>'")
            pairs.append((bytes.fromhex(fields[0]), bytes.fromhex(fields[1])))
    return pairs


def command_statement(args):
    """Answer the statement query from the carried index.

    Three outcomes stay distinct (D13): found prints the statement's
    canonical octets and exits 0, absent exits 1 (a known absence is a
    refusal, not a fault), and a keyring this node cannot read exits 5.
    """
    store, bridge, unused_records = open_live_store(args.store, writable=False)
    try:
        pairs = read_keyring_file(args.keyring) if args.keyring else []
        if bridge.set_keyring(pairs) != "configured":
            return EXIT_USAGE
        if args.equivocator is not None:
            outcome = bridge.equivocator(bytes.fromhex(args.equivocator),
                                         args.incarnation)
            if outcome == "invalid":
                return EXIT_USAGE
            print(outcome)
            return EXIT_OK if outcome == "equivocator" else EXIT_REFUSED
        if args.index_size:
            print(bridge.index_size())
            return EXIT_OK
        octets = bridge.statement(bytes.fromhex(args.id))
        if not octets:
            return EXIT_REFUSED
        sys.stdout.buffer.write(octets)
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def main(argv=None):
    parser = UsageParser(description=__doc__)
    parser.add_argument("--store", required=True, help="local store root")
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init")
    init.add_argument("--profile", metavar="WORD",
                      help="a preset ACL2 names (development, scale or default, "
                           "as the native init); default: ACL2's initial profile")
    init.add_argument("--group", action="append",
                      help="a group the new store serves (default: the two experimental groups)")
    group = sub.add_parser("group")
    group.add_argument("action", choices=("create", "retire"))
    group.add_argument("name")
    capacity = sub.add_parser("capacity")
    capacity.add_argument("capacity", type=int,
                          help="the retention capacity in bytes; must be above the reservation total")

    peer = sub.add_parser("peer")
    peer.add_argument("action", choices=("add", "remove", "list"))
    peer.add_argument("name", nargs="?", default="")
    peer.add_argument("--path-identity")
    peer.add_argument("--nntp", help="HOST:PORT of the peer's NNTP listener")
    peer.add_argument("--bp", help="the peer's BP endpoint id (instead of --nntp)")
    peer.add_argument("--inbound-groups", help="wildmat this peer may feed us")
    peer.add_argument("--inbound-max-octets", type=int, default=0,
                      help="the largest article this peer may send; 0, the "
                           "default, is the record layer's own ceiling, which "
                           "ACL2 supplies (fn-store-cfg-peer-record)")
    peer.add_argument("--inbound-max-inflight", type=int, default=16)
    peer.add_argument("--outbound-groups", help="wildmat we feed this peer")
    peer.add_argument("--streaming", action="store_true")
    peer.add_argument("--max-queue", type=int, default=1024)
    peer.add_argument("--backoff-ms", type=int, default=1000)
    peer.add_argument("--source-address")
    peer.add_argument("--principal")
    peer.add_argument("--carries", action="append", metavar="HEX",
                      help="D23: a principal (64 lowercase hex) whose signed "
                           "articles this peer may carry to us; repeatable")
    policy = sub.add_parser("policy")
    policy.add_argument("action", choices=("set", "get"))
    policy.add_argument("slot",
                        help="a configuration policy slot; `path-identity` is "
                             "the node's own RFC 5537 <path-identity>")
    policy.add_argument("value", nargs="?")
    sub.add_parser("config")
    post = sub.add_parser("post")
    post.add_argument("--message-id", required=True)
    post.add_argument("--payload", required=True)
    post.add_argument("--group", action="append", required=True)
    post.add_argument("--charge", type=int)
    post.add_argument("--inject-fault", choices=tuple(CLI_FAULTS),
                      help="test-only: select one scripted publication fault point")
    post.add_argument("--owner", help="post through the running owner's control socket")
    recover = sub.add_parser("recover")
    anchor = sub.add_parser("anchor")
    for parser_with_anchor in (recover, anchor):
        parser_with_anchor.add_argument(
            "--anchor-server", help="a name from tools/roughtime_servers.json")
        parser_with_anchor.add_argument(
            "--anchor-vector",
            help="test-only: a captured response instead of a live query")
        parser_with_anchor.add_argument("--anchor-timeout", type=float, default=5.0)
    sub.add_parser("status")
    statement = sub.add_parser("statement")
    statement.add_argument("--id", default="",
                           help="the statement content id, hex")
    statement.add_argument("--keyring",
                           help="lines of '<creator-hex> <public-key-hex>'; "
                                "without it the node knows no key and every "
                                "statement query is absent")
    statement.add_argument("--equivocator",
                           help="ask whether this creator (hex) has forked, "
                                "instead of looking an id up")
    statement.add_argument("--incarnation", type=int, default=0)
    statement.add_argument("--index-size", action="store_true",
                           help="print the number of bindings the index holds")
    inspect = sub.add_parser("inspect")
    inspect.add_argument("--message-id", required=True)
    inspect.add_argument("--provenance", action="store_true",
                         help="print the article's provenance (ACL2 renders the line) "
                              "instead of its octets")
    args = parser.parse_args(argv)
    try:
        if os.environ.get("FN_HOST") == "native":
            # The native host image performs the same command in-process; the
            # parse above and the exit-code table below are shared with it.
            from tools import fn_native
            return fn_native.exec_store(args)
        return {"init": command_init, "post": command_post, "recover": command_recover,
                "status": command_status, "inspect": command_inspect,
                "anchor": command_anchor, "group": command_group,
                "capacity": command_capacity,

                "peer": command_peer, "statement": command_statement,
                "policy": command_policy,
                "config": command_config}[args.command](args)
    except (StoreError, OSError, UnicodeError) as error:
        print("store: {}".format(error), file=sys.stderr)
        return exit_code_for(error)


if __name__ != "__main__":
    # The CLI entry points put `tools/` on sys.path while the tests and the BP
    # adapters import the `tools` package, so this file is reachable under two
    # names.  One module object under both keeps a single durability helper, a
    # single configuration profile and a single patch point, instead of two
    # copies whose constants can be patched apart.
    for _alias in ("run_store", "tools.run_store"):
        sys.modules.setdefault(_alias, sys.modules[__name__])

if __name__ == "__main__":
    sys.exit(main())
