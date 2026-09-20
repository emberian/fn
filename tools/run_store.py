#!/usr/bin/env python3
"""Experimental local immutable-transaction store backed by interpreted ACL2.

This is a storage experiment, not a durable-service or power-failure claim.
ACL2 decodes records, frames and unframes transaction files, derives content
identity, applies every bound and owns the group table and the charge policy.
Python owns bounded filesystem I/O, POSIX barriers, and SHA-256 over byte
strings it does not interpret (A-CRYPTO).
"""
import argparse
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
import time

ROOT = Path(__file__).resolve().parent.parent
# This module is imported both as `tools.run_store` and, with `tools/` on the
# path, as `run_store`.  Pin the framing bridge to one identity so its ACL2
# session is shared rather than opened once per spelling.
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import frame_bridge  # noqa: E402

PROMPT = b"ACL2 !>"
MAX_ACL2_OUTPUT = 4 * 1024 * 1024
MAX_TRANSACTION_COUNT = 128
MAX_RECOVERY_RECORD_BYTES = MAX_TRANSACTION_COUNT * 65538
UINT32_MAX = (1 << 32) - 1
DEFAULT_CONFIG = {
    # Format 5 is the first written under the v1 content identity profile of
    # `books/identity`; a store holding pre-v1 `"sha256:"`/`"archive:"`
    # identities is format 4 and is refused at open rather than misread.
    # Format 3 was the first written under the ACL2-owned frame grammar, which
    # carries the record kind octet the Python framing lacked.  The group
    # table is not here at all: it is the store's configuration record
    # history under `config/`, replayed by the core at every open.
    # The encoded-record bound left with it: `books/frame` owns
    # `*fn-frame-max-store-payload*`, the host reads it from the bridge, and a
    # configuration that could disagree with the model is not written at all.
    "format": "fn-store-experiment-5",
    "capacity": 1048576,
    "max_payload_bytes": 32768,
    "max_recovery_record_bytes": MAX_RECOVERY_RECORD_BYTES,
    "max_transactions": MAX_TRANSACTION_COUNT,
    "allocation_frontier_format": "fn-store-allocation-frontier-1",
}
# A second *named* profile, not a raised default.  `max_transactions` and the
# aggregate replay input it derives are the two bounds this host owns; every
# bound the model owns (`*fn-frame-max-store-payload*`, `*fn-article-max-octets*`,
# the configured group table, `fn-af-message-idp`, `fn-charge-for-payload`) is
# unchanged here and cannot be raised from configuration at all.  A store
# carries its profile name in its checksummed configuration, so a dev store and
# a scale store are distinguishable on disk and neither is read under the
# other's bounds.  `planning/scale-profile.md` holds the measurements that
# justify the number and the reopen cost it implies.
SCALE_TRANSACTION_COUNT = 4096
SCALE_CONFIG = dict(
    DEFAULT_CONFIG,
    profile="fn-store-profile-scale-1",
    max_transactions=SCALE_TRANSACTION_COUNT,
    max_recovery_record_bytes=SCALE_TRANSACTION_COUNT * 65538,
)
# The development profile keeps its exact configuration bytes: it gains no
# `profile` key, so every store written before this profile existed still
# checksums and still opens.
SUPPORTED_PROFILES = (DEFAULT_CONFIG, SCALE_CONFIG)
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
SEQ_NAME = re.compile(r"^[0-9]{20}\.txn$")
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


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def config_with_checksum(config):
    body = dict(config)
    body.pop("checksum", None)
    body["checksum"] = hashlib.sha256(canonical_json(body)).hexdigest()
    return body


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
                    b":REFUSED", b":FAULT", b":RECOVERING",
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


class Acl2Store:
    """Fixed ACL2 calls: all externally-derived values become decimal octets."""
    def __init__(self):
        env = os.environ.copy()
        env["ACL2_CUSTOMIZATION"] = "NONE"
        env["ACL2_BOOK_HASH_ALISTP"] = "NIL"  # content-hashed certificates: relocatable across worktrees and hosts
        self.proc = None
        # A bridge whose correlation is lost cannot be repaired by reading
        # further: a new ACL2 process is the only recovery.
        self.poisoned = False
        try:
            self.proc = subprocess.Popen([env.get("FN_ACL2", "acl2")], cwd=ROOT,
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, env=env)
            read_prompt(self.proc, ACL2_START_TIMEOUT_SECONDS)
            self.call('(include-book "books/replay")')
            self.call('(ld "host/store-host.lisp" :ld-error-action :return :ld-error-triples t)')
            self.call('(ld "host/store-node-host.lisp" :ld-error-action :return :ld-error-triples t)')
            self.call('(ld "host/checkpoint-host.lisp" :ld-error-action :return :ld-error-triples t)')
            self.call('(ld "host/anchor-host.lisp" :ld-error-action :return :ld-error-triples t)')
            self.call('(ld "host/config-host.lisp" :ld-error-action :return :ld-error-triples t)')
            self.reset()
        except BaseException:
            self.close()
            raise

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

    def record_sequence(self, record):
        return acl2_nat(self.call("(fn-store-record-sequence '" + self.literal(record) + ")"))

    def record_txid(self, record):
        return acl2_nat(self.call("(fn-store-record-txid '" + self.literal(record) + ")"))

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
         midpoint, radius, nonce, signature) = fields
        return "(list '{} '{} {} {} '{} {} {} '{} '{})".format(
            cls.literal(key), cls.literal(delegate), mint, maxt,
            cls.literal(delegation_signature), midpoint, radius,
            cls.literal(nonce), cls.literal(signature))

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
        if not isinstance(value, list) or len(value) != 10:
            raise StoreFault("durable anchor record does not decode")
        return value

    def anchor_accept(self, pinned, latest, incarnation, fields, verdict):
        status, reason = self._form(
            "(fn-anchor-host-accept {} {} {} {} {})".format(
                self.anchor_pinned_form(pinned), self.anchor_fields_form(latest),
                incarnation, self.anchor_fields_form(fields),
                "t" if verdict else "nil"))
        return str(status), (str(reason) if reason else None)

    def anchor_restore(self, pinned, incarnation, referenced, presented, verdict):
        status, reason, next_incarnation = self._form(
            "(fn-anchor-host-restore {} {} {} {} {})".format(
                self.anchor_pinned_form(pinned), incarnation,
                self.anchor_fields_form(referenced),
                self.anchor_fields_form(presented),
                "t" if verdict else "nil"))
        return str(status), (str(reason) if reason else None), next_incarnation

    def io(self, operation, result="ok"):
        return acl2_symbol(self.call("(fn-store-sn-io :{} :{} state)".format(operation, result)))

    def prepare(self, msgid, payload, group_codes, obligation_id, subject, evidence, charge):
        form = "(fn-store-sn-prepare '" + self.literal(msgid) + " '" + self.literal(payload)
        form += " '" + self.numeric_list(group_codes) + " '" + self.literal(obligation_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " " + str(charge) + " state)"
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

    def reconfigure(self, kind, name, monotonic, wall):
        """One create/retire request.  Returns ("ok", octets) or ("refused", reason)."""
        form = "(fn-store-cfg-reconfigure {} '{} {} {} state)".format(
            kind, self.literal(name.encode("utf-8", "strict")), int(monotonic), int(wall))
        status = acl2_keyword(self.call(form))
        if status == "ok":
            return status, acl2_octets(self.call("(fn-store-cfg-last-octets state)"))
        if status != "refused":
            raise StoreFault("unexpected reconfiguration outcome: {}".format(status))
        return "refused", acl2_keyword(self.call("(fn-store-cfg-last-reason state)"))

    def pin_count(self):
        return acl2_nat(self.call("(fn-store-sn-pin-count state)"))

    def reserved(self):
        return acl2_nat(self.call("(fn-store-sn-reserved state)"))

    def lookup(self, msgid):
        return acl2_octets(self.call("(fn-store-sn-lookup '" + self.literal(msgid) + " state)"))

    def lookup_found(self, msgid):
        return acl2_boolean(self.call("(fn-store-sn-lookup-foundp '" + self.literal(msgid) + " state)"))

    def close(self):
        if self.proc is None:
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


class Store:
    def __init__(self, root, writable=False, faults=NO_FAULTS, profile=None):
        self.root = Path(root).absolute()
        self.writable = writable
        self.faults = faults
        # Which named profile `initialize` would write.  Opening an existing
        # store still takes the profile from its durable configuration.
        self.profile = DEFAULT_CONFIG if profile is None else profile
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
        octets = (1, 2, 5, 8, 9)
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

    def config_record_path(self, generation):
        return self.config_dir / "{:08d}.cfg".format(generation)

    def config_record_files(self):
        """The durable configuration records in generation order."""
        if not self.config_dir.is_dir():
            return ()
        names = sorted(entry.name for entry in os.scandir(self.config_dir)
                       if entry.name.endswith(".cfg"))
        return tuple(self.config_dir / name for name in names)

    @staticmethod
    def _frontier_with_checksum(next_txid):
        body = {"format": "fn-store-allocation-frontier-1", "next_txid": next_txid}
        body["checksum"] = hashlib.sha256(canonical_json(body)).hexdigest()
        return body

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
        lock_fd = self._open_lock(exclusive=True, create=True)
        try:
            self._safe_directory(self.transactions, create=True)
            self._safe_directory(self.staging, create=True)
            self._safe_directory(self.config_dir, create=True)
            config = config_with_checksum(self.profile)
            if self._publish_initial_file(self.config_path, canonical_json(config) + b"\n"):
                self.config = config
            else:
                self._load_config()
            # A missing allocator alongside committed history would permit
            # reuse of an aborted ID.  It is a fault, never an implicit 0.
            if not self.config_record_files():
                try:
                    octets = frame_bridge.session(bridge).config_record_initial(groups)
                except frame_bridge.BridgeError as error:
                    raise StoreError("refused initial group table: {}".format(error)) from error
                self._publish_initial_file(self.config_record_path(1), octets)
                fsync_dir(self.config_dir)
            if not check_regular(self.frontier_path) and self.transaction_files():
                raise StoreFault("refusing missing allocator frontier with committed history")
            frontier = canonical_json(self._frontier_with_checksum(0)) + b"\n"
            if self._publish_initial_file(self.frontier_path, frontier):
                self.frontier = 0
            else:
                self._load_frontier()
            fsync_regular(self.config_path)
            for path in self.config_record_files():
                fsync_regular(path)
            fsync_regular(self.frontier_path)
            fsync_dir(self.transactions)
            fsync_dir(self.root)
            fsync_dir(self.root.parent)
        finally:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)

    def _load_config(self):
        check_regular(self.config_path)
        try:
            raw = read_regular_bounded(self.config_path, 16384)
            config = json.loads(raw)
        except (OSError, ValueError, UnicodeDecodeError) as error:
            raise StoreFault("invalid durable config: {}".format(error)) from error
        if not isinstance(config, dict) or config_with_checksum(config) != config:
            raise StoreFault("config checksum mismatch")
        if not any(config == config_with_checksum(supported)
                   for supported in SUPPORTED_PROFILES):
            raise StoreFault("unsupported store configuration")
        self.config = config

    def _load_frontier(self):
        check_regular(self.frontier_path)
        try:
            raw = read_regular_bounded(self.frontier_path, 4096)
            frontier = json.loads(raw)
        except (OSError, ValueError, UnicodeDecodeError) as error:
            raise StoreFault("invalid durable allocation frontier: {}".format(error)) from error
        if not isinstance(frontier, dict):
            raise StoreFault("allocation frontier must be an object")
        next_txid = frontier.get("next_txid")
        if (frontier != self._frontier_with_checksum(next_txid)
                or not isinstance(next_txid, int) or isinstance(next_txid, bool)
                or not 0 <= next_txid <= UINT32_MAX):
            raise StoreFault("allocation frontier checksum or range mismatch")
        self.frontier = next_txid

    def acquire(self):
        self._safe_directory(self.root)
        self._safe_directory(self.transactions)
        self._safe_directory(self.staging)
        try:
            self.lock_fd = self._open_lock(exclusive=self.writable, create=self.writable)
            # Frontiers are mutable writer-owned state.  Read them only after
            # the process-wide lock prevents a concurrent allocation update.
            self._load_config()
            self._load_frontier()
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
        with entries:
            for entry in entries:
                if len(files) >= self.config["max_transactions"]:
                    raise StoreFault("transaction count exceeds configured bound")
                if not SEQ_NAME.fullmatch(entry.name):
                    raise StoreFault("unexpected final-namespace entry: {}".format(entry.name))
                if entry.is_symlink() or not entry.is_file(follow_symlinks=False):
                    raise StoreFault("refusing transaction symlink or non-file")
                files.append((int(entry.name[:20]), Path(entry.path)))
        files.sort()
        for expected, (sequence, _) in enumerate(files):
            if sequence != expected:
                raise StoreFault("transaction sequence gap")
        return files

    def staging_orphans(self):
        """Enumerate staged names an interrupted publication left behind.

        Staging is outside recovery authority.  These names are reported so an
        operator can see them; recovery neither adopts nor deletes them.
        """
        names = []
        try:
            entries = os.scandir(self.staging)
        except OSError as error:
            raise StoreFault("cannot enumerate staging") from error
        with entries:
            for entry in entries:
                if len(names) >= MAX_STAGING_REPORT:
                    names.append("...")
                    break
                names.append(entry.name)
        return tuple(sorted(names))

    def durable_records(self, acl2):
        records = []
        aggregate = 0
        # The bounded read is sized from the model's record bound, not from a
        # host copy of it.
        constants = frame_bridge.session().constants
        bound = constants["overhead"] + constants["max_store"]
        for sequence, path in self.transaction_files():
            check_regular(path)
            raw = read_regular_bounded(path, bound)
            record = unframe(raw)
            aggregate += len(record)
            if aggregate > self.config["max_recovery_record_bytes"]:
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

    def write_config_record(self, generation, octets):
        """Make one admitted configuration record durable under its generation.

        The three outcomes stay distinct: the record either reaches its final
        name and its directory barrier (accepted), or an I/O failure leaves
        it uncertain -- the next open replays whatever became durable.
        """
        try:
            if not self._publish_initial_file(self.config_record_path(generation), octets):
                raise StoreFault("configuration generation {} already exists".format(generation))
            fsync_regular(self.config_record_path(generation))
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
            self._load_frontier()
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
        self.checkpoint_outcome = self._checkpoint_hook(acl2, records)
        return records

    def _checkpoint_hook(self, acl2, records):
        """C2-09: decode the selected checkpoint generation and replay only its suffix.

        The journal replayed above stays the authority.  The outcome is one of
        ("none",), ("ok", generation, sequence, differential) or ("corrupt",
        reason); a corrupt selected generation is reported, never replaced by
        an older one.  `differential` is ACL2's comparison of the two nodes;
        it is asserted only under FN_CHECKPOINT_DIFFERENTIAL.
        """
        from tools import checkpoint
        try:
            outcome = checkpoint.restore_selected(self, acl2, records, self.frontier)
        except checkpoint.CheckpointCorrupt as error:
            return ("corrupt", str(error))
        if outcome[0] == "ok" and checkpoint.differential_enabled():
            assert outcome[3], "checkpoint plus suffix differs from full replay"
        return outcome

    def advance_frontier(self, acl2, current_txid):
        """Report each allocator observation to the file kernel in order."""
        self._require_writer()
        if self.fenced:
            raise StoreIndeterminate("store is fenced pending recovery")
        if current_txid != self.frontier:
            self.fenced = True
            raise StoreFault("ACL2 allocator and durable frontier disagree")
        if not isinstance(current_txid, int) or current_txid < 0 or current_txid >= UINT32_MAX:
            raise StoreError("finite transaction-ID domain exhausted")
        next_frontier = current_txid + 1
        contents = canonical_json(self._frontier_with_checksum(next_frontier)) + b"\n"
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
                write_all(fd, contents)
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
        name = "{:020d}.txn".format(sequence)
        final = self.transactions / name
        stage = self.staging / (".stage-{}-{}".format(os.getpid(), os.urandom(12).hex()))
        data = frame(record)
        publication_attempted = False
        try:
            fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            try:
                write_all(fd, data)
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
    header are all strings.  The evidence label stays a host constant: it
    names a provenance the model only compares.
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
    if store.config.get("format") != session.format_id():
        raise StoreFault("store was written under a different store format")
    if not groups:
        raise StoreError("provide one or more distinct configured groups")
    try:
        return session.group_codes(groups, store.config_domain)
    except frame_bridge.BridgeError as error:
        raise StoreError("unknown or duplicate configured group") from error


def conservative_charge(payload, bridge=None):
    """`fn-charge-for-payload`, proved positive and monotone in length."""
    return frame_bridge.session(bridge).charge(len(payload))


def validate_post_boundary(msgid, payload, groups, charge, config, bridge=None):
    """One call: `fn-store-post-boundary` applies every bound in the model."""
    session = frame_bridge.session(bridge)
    if config["max_payload_bytes"] > session.constants["max_store"]:
        raise StoreFault("configured payload bound disagrees with the model")
    verdict = session.post_boundary(msgid, len(payload), len(groups), charge)
    if verdict == "ok":
        return
    raise StoreError({
        "bad-message-id": "Message-ID is not a valid RFC 5536 message identifier",
        "payload-bound": "payload exceeds the modelled bound",
        "group-bound": "group count exceeds codec bound",
        "charge-bound": "charge must be a positive uint32",
    }.get(verdict, "ACL2 refused the post boundary: {}".format(verdict)))


def command_init(args):
    store = Store(args.store, writable=True)
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
        generation = store.config_generation + 1
        store.write_config_record(generation, payload)
        print("group {} name={} generation={}".format(
            "created" if args.action == "create" else "retired", args.name, generation))
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
    store = Store(path, writable=writable, faults=faults)
    store.acquire()
    bridge = None
    try:
        bridge = Acl2Store()
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


def durable_post(store, bridge, records_count, msgid, payload, codes, charge):
    """The durable acceptance path, shared by the CLI and the served POST.

    ACL2 decides: `bridge.prepare` is fn-node-prepare and `store.finish` is the
    exact fn-sn durable completion.  This function performs I/O around those
    decisions and reports the sequence it committed.  It never invents a
    durable status.
    """
    current_txid = bridge.next_txid()
    next_frontier = store.advance_frontier(bridge, current_txid)
    obligation, subject, evidence = metadata(msgid, payload)
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
    if records_count >= store.config["max_transactions"]:
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
    payload = read_regular_bounded(args.payload, DEFAULT_CONFIG["max_payload_bytes"])
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
# FLR-003: a checksummed store image cannot show it is not an old snapshot.
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
    """Ed25519 over exactly the octets ACL2 says were signed.

    ACL2 rebuilds both signed messages; if its reconstruction and the octets
    on the wire disagree, that is a fault, not a verdict.  Two checks make the
    chain: the pinned long-term key over the delegation, and the delegated key
    over the response.
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
    store = Store(args.store, writable=True)
    store.acquire()
    bridge = None
    try:
        bridge = Acl2Store()
        incarnation, held = store.load_anchor(bridge)
        anchor, reason = obtain_anchor(args)
        if anchor is None:
            print("anchor uncertain: {}".format(reason))
            return EXIT_UNCERTAIN
        fields = anchor.fields()
        status, why = bridge.anchor_accept(
            pinned_keys(), held, incarnation, fields,
            anchor_verdict(bridge, anchor))
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
        anchor_verdict(bridge, anchor))
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
        payload = bridge.lookup(msgid)
        sys.stdout.buffer.write(payload)
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def main(argv=None):
    parser = UsageParser(description=__doc__)
    parser.add_argument("--store", required=True, help="local store root")
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init")
    init.add_argument("--group", action="append",
                      help="a group the new store serves (default: the two experimental groups)")
    group = sub.add_parser("group")
    group.add_argument("action", choices=("create", "retire"))
    group.add_argument("name")
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
    inspect = sub.add_parser("inspect")
    inspect.add_argument("--message-id", required=True)
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
