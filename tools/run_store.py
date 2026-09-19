#!/usr/bin/env python3
"""Experimental local immutable-transaction store backed by interpreted ACL2.

This is a storage experiment, not a durable-service or power-failure claim.
Only ACL2 decodes records and reconstructs node state.  Python owns bounded
filesystem I/O, SHA-256 integrity trailers, and POSIX barriers.
"""
import argparse
import errno
import fcntl
import hashlib
import hmac
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
PROMPT = b"ACL2 !>"
MAX_ACL2_OUTPUT = 4 * 1024 * 1024
MAX_TRANSACTION_COUNT = 128
MAX_RECOVERY_RECORD_BYTES = MAX_TRANSACTION_COUNT * 65538
UINT32_MAX = (1 << 32) - 1
DEFAULT_CONFIG = {
    "format": "fn-store-experiment-2",
    "groups": ["fn.letters", "fn.test"],
    "capacity": 1048576,
    "max_payload_bytes": 32768,
    "max_record_bytes": 65538,
    "max_recovery_record_bytes": MAX_RECOVERY_RECORD_BYTES,
    "max_transactions": MAX_TRANSACTION_COUNT,
    "allocation_frontier_format": "fn-store-allocation-frontier-1",
}
MAGIC = b"FNST\x01"
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


def frame(record):
    if len(record) > DEFAULT_CONFIG["max_record_bytes"]:
        raise StoreFault("record exceeds fixed store bound")
    header = MAGIC + len(record).to_bytes(4, "big") + record
    return header + hashlib.sha256(header).digest()


def unframe(raw, max_record_bytes):
    minimum = len(MAGIC) + 4 + TRAILER_BYTES
    if len(raw) < minimum or raw[:len(MAGIC)] != MAGIC:
        raise StoreFault("bad transaction frame")
    start = len(MAGIC)
    size = int.from_bytes(raw[start:start + 4], "big")
    if size > max_record_bytes:
        raise StoreFault("transaction record exceeds configured bound")
    expected = len(MAGIC) + 4 + size + TRAILER_BYTES
    if len(raw) != expected:
        raise StoreFault("truncated or overlong transaction frame")
    protected = raw[:-TRAILER_BYTES]
    if not hmac.compare_digest(hashlib.sha256(protected).digest(), raw[-TRAILER_BYTES:]):
        raise StoreFault("transaction integrity trailer mismatch")
    return raw[len(MAGIC) + 4:-TRAILER_BYTES]


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

    def recover(self, records, frontier):
        literal = "(" + " ".join(self.literal(record) for record in records) + ")"
        form = "(fn-store-sn-recover '" + literal + " " + str(frontier) + " state)"
        # Replay cost grows with the recovered history, so the bound does too.
        timeout = max(ACL2_RECOVER_BASE_SECONDS + ACL2_RECOVER_PER_RECORD_SECONDS * len(records),
                      self.form_timeout(form))
        return acl2_symbol(self.call(form, timeout=timeout))

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
    def __init__(self, root, writable=False, faults=NO_FAULTS):
        self.root = Path(root).absolute()
        self.writable = writable
        self.faults = faults
        self.lock_fd = None
        self.config = None
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

    def initialize(self):
        self._safe_directory(self.root, create=True)
        lock_fd = self._open_lock(exclusive=True, create=True)
        try:
            self._safe_directory(self.transactions, create=True)
            self._safe_directory(self.staging, create=True)
            config = config_with_checksum(DEFAULT_CONFIG)
            if self._publish_initial_file(self.config_path, canonical_json(config) + b"\n"):
                self.config = config
            else:
                self._load_config()
            # A missing allocator alongside committed history would permit
            # reuse of an aborted ID.  It is a fault, never an implicit 0.
            if not check_regular(self.frontier_path) and self.transaction_files():
                raise StoreFault("refusing missing allocator frontier with committed history")
            frontier = canonical_json(self._frontier_with_checksum(0)) + b"\n"
            if self._publish_initial_file(self.frontier_path, frontier):
                self.frontier = 0
            else:
                self._load_frontier()
            fsync_regular(self.config_path)
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
        if config != config_with_checksum(DEFAULT_CONFIG):
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
        for sequence, path in self.transaction_files():
            check_regular(path)
            raw = read_regular_bounded(
                path, len(MAGIC) + 4 + self.config["max_record_bytes"] + TRAILER_BYTES)
            record = unframe(raw, self.config["max_record_bytes"])
            aggregate += len(record)
            if aggregate > self.config["max_recovery_record_bytes"]:
                raise StoreFault("transaction recovery input exceeds configured bound")
            if acl2.record_sequence(record) != sequence:
                raise StoreFault("record sequence does not match immutable filename")
            records.append(record)
        return records

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
            records = self.durable_records(acl2)
            self.orphans = self.staging_orphans()
            if acl2.recover(records, self.frontier) != "recovering":
                raise StoreFault("ACL2 replay rejected committed transaction history")
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
            if phase != "ready":
                raise StoreFault("ACL2 did not complete all recovery barriers")
        except OSError as error:
            self.fenced = True
            raise StoreIndeterminate("cannot establish recovered namespace frontier") from error
        self.fenced = False
        return records

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
            publication_attempted = True
            # Replacement is a namespace attempt; close the mutation gate
            # before both the syscall and its corresponding ACL2 observation.
            self.fenced = True
            try:
                os.replace(stage, self.frontier_path)
            except OSError:
                self._observe(acl2, "frontier-replace", "error")
                raise
            if self._observe(acl2, "frontier-replace", "ok") != "frontier-attempted":
                # The replacement already reached the namespace; a core that
                # will not record it leaves the frontier unresolved.
                raise StoreIndeterminate(
                    "ACL2 rejected allocator replacement after the namespace attempt")
            self.fenced = True
            try:
                fsync_dir(self.root)
            except OSError:
                self._observe(acl2, "frontier-directory", "error")
                raise
            if self._observe(acl2, "frontier-directory", "ok") != "reserved":
                raise StoreIndeterminate(
                    "ACL2 rejected durable allocator frontier after its barrier")
            # The exact file-kernel reservation is installed.  Preparation
            # remains the next ACL2 gate while the writer lock is still held.
            self.fenced = False
            self.frontier = next_frontier
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
        if len(record) > self.config["max_record_bytes"]:
            raise StoreFault("ACL2 record exceeds configured bound")
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
            if self._observe(acl2, "record-directory", "ok") != "completing":
                raise StoreIndeterminate(
                    "ACL2 rejected record directory barrier after publication")
            # The directory barrier and its ACL2 reply were both observed.
            # This sole opportunity is consumed before any finish call.
            self.completion_pending = True
            # Staging files are ignored by recovery.  Their best-effort cleanup
            # occurs only after the final namespace barrier succeeded.
            try:
                os.unlink(stage)
                fsync_dir(self.staging)
            except OSError:
                pass
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
        try:
            completion = acl2.finish()
        except (StoreError, OSError) as error:
            self.fenced = True
            raise StoreIndeterminate("ACL2 completion failed after publication") from error
        if completion != "durable":
            self.fenced = True
            raise StoreIndeterminate("ACL2 rejected durable completion after publication")
        self.fenced = False
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


def metadata(msgid, payload):
    digest = hashlib.sha256(payload).hexdigest().encode("ascii")
    subject = b"sha256:" + digest
    obligation = b"archive:" + hashlib.sha256(msgid + b"\x00" + subject).hexdigest().encode("ascii")
    return obligation, subject, b"unsigned-legacy-v0"


def group_codes(groups, config):
    configured = config["groups"]
    if not groups or len(groups) != len(set(groups)):
        raise StoreError("provide one or more distinct configured groups")
    try:
        return [configured.index(group) for group in groups]
    except ValueError as error:
        raise StoreError("unknown configured group") from error


def conservative_charge(payload):
    return max(1, 1 + (len(payload) + 4095) // 4096)


def validate_post_boundary(msgid, payload, groups, charge, config):
    if not (0 < len(msgid) <= 250 and all(octet <= 127 for octet in msgid)):
        raise StoreError("Message-ID must be 1 through 250 ASCII octets")
    if len(payload) > config["max_payload_bytes"]:
        raise StoreError("payload exceeds configured bound")
    if not 0 < len(groups) <= 16:
        raise StoreError("group count exceeds codec bound")
    if not isinstance(charge, int) or isinstance(charge, bool) or not 0 < charge <= UINT32_MAX:
        raise StoreError("charge must be a positive uint32")


def command_init(args):
    store = Store(args.store, writable=True)
    try:
        store.initialize()
        store.acquire()
        print("initialized {}".format(store.root))
    finally:
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


def command_post(args):
    msgid = args.message_id.encode("ascii")
    payload = read_regular_bounded(args.payload, DEFAULT_CONFIG["max_payload_bytes"])
    faults = NO_FAULTS if args.inject_fault is None else CLI_FAULTS[args.inject_fault]()
    store, bridge, records = open_live_store(args.store, writable=True, faults=faults)
    try:
        codes = group_codes(args.group, store.config)
        charge = args.charge if args.charge is not None else conservative_charge(payload)
        validate_post_boundary(msgid, payload, codes, charge, store.config)
        existing = bridge.existing_action(msgid, payload, codes)
        if existing == "duplicate":
            print("duplicate")
            return 0
        if existing == "conflict":
            raise StoreError("conflicting immutable Message-ID")
        if len(records) >= store.config["max_transactions"]:
            raise StoreError("transaction count has reached configured bound")
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
            store.publish(bridge, len(records), record)
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
        print("committed sequence={} charge={}".format(len(records), charge))
        return EXIT_OK
    finally:
        bridge.close()
        store.close()


def orphan_report(store):
    """Name staged orphans so recovery reports them instead of hiding them."""
    if not store.orphans:
        return "staging-orphans=0"
    return "staging-orphans={} [{}]".format(len(store.orphans), " ".join(store.orphans))


def command_recover(args):
    store, bridge, records = open_live_store(args.store, writable=True)
    try:
        print("recovered transactions={} articles={} {}".format(
            len(records), bridge.article_count(), orphan_report(store)))
        return EXIT_OK
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
    sub.add_parser("init")
    post = sub.add_parser("post")
    post.add_argument("--message-id", required=True)
    post.add_argument("--payload", required=True)
    post.add_argument("--group", action="append", required=True)
    post.add_argument("--charge", type=int)
    post.add_argument("--inject-fault", choices=tuple(CLI_FAULTS),
                      help="test-only: select one scripted publication fault point")
    sub.add_parser("recover")
    sub.add_parser("status")
    inspect = sub.add_parser("inspect")
    inspect.add_argument("--message-id", required=True)
    args = parser.parse_args(argv)
    try:
        return {"init": command_init, "post": command_post, "recover": command_recover,
                "status": command_status, "inspect": command_inspect}[args.command](args)
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
