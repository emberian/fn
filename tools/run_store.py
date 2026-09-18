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


class StoreError(RuntimeError):
    pass


class StoreFault(StoreError):
    pass


class StoreIndeterminate(StoreError):
    pass


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


def fsync_dir(path):
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    fd = os.open(path, flags)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def fsync_file(fd):
    os.fsync(fd)


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
        os.fsync(fd)
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


def read_prompt(proc, timeout=20):
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


def acl2_octets(output):
    body = acl2_result(output)
    if body == b"NIL":
        return b""
    if not re.fullmatch(rb"\((?:\s*[0-9]+)*\s*\)", body):
        raise StoreError("ACL2 returned a non-octet result")
    values = [int(value) for value in body[1:-1].split()]
    if any(value > 255 for value in values):
        raise StoreError("ACL2 returned a non-octet")
    return bytes(values)


def acl2_symbol(output):
    body = acl2_result(output).upper()
    if body not in {b":READY", b":PREPARED", b":DURABLE", b":ABORTED",
                    b":INDETERMINATE", b":DUPLICATE", b":CONFLICT", b":ABSENT", b":INVALID",
                    b":REFUSED", b":FAULT"}:
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
        try:
            self.proc = subprocess.Popen([env.get("FN_ACL2", "acl2")], cwd=ROOT,
                                         stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, env=env)
            read_prompt(self.proc, 30)
            self.call('(include-book "books/replay")')
            self.call('(ld "host/store-host.lisp" :ld-error-action :return :ld-error-triples t)')
            self.reset()
        except BaseException:
            self.close()
            raise

    def call(self, form):
        self.proc.stdin.write((form + "\n").encode("ascii"))
        self.proc.stdin.flush()
        output = read_prompt(self.proc)
        upper = output.upper()
        if b"ACL2 ERROR" in upper or b"HARD ACL2 ERROR" in upper or b"FAILED" in upper:
            raise StoreError(output.decode("utf-8", "replace"))
        return output

    @staticmethod
    def literal(octets):
        return "(" + " ".join(str(value) for value in octets) + ")"

    @staticmethod
    def numeric_list(values):
        return "(" + " ".join(str(value) for value in values) + ")"

    def reset(self):
        return acl2_symbol(self.call("(fn-store-reset state)"))

    def record_sequence(self, record):
        return acl2_nat(self.call("(fn-store-record-sequence '" + self.literal(record) + ")"))

    def record_txid(self, record):
        return acl2_nat(self.call("(fn-store-record-txid '" + self.literal(record) + ")"))

    def recover(self, records, frontier):
        literal = "(" + " ".join(self.literal(record) for record in records) + ")"
        return acl2_symbol(self.call("(fn-store-recover '" + literal + " " + str(frontier) + " state)"))

    def advance_frontier(self, frontier):
        return acl2_symbol(self.call("(fn-store-advance-frontier {} state)".format(frontier)))

    def prepare(self, msgid, payload, group_codes, obligation_id, subject, evidence, charge):
        form = "(fn-store-prepare '" + self.literal(msgid) + " '" + self.literal(payload)
        form += " '" + self.numeric_list(group_codes) + " '" + self.literal(obligation_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " " + str(charge) + " state)"
        return acl2_symbol(self.call(form))

    def existing_action(self, msgid, payload, group_codes):
        form = "(fn-store-existing-action '" + self.literal(msgid)
        form += " '" + self.literal(payload) + " '" + self.numeric_list(group_codes) + " state)"
        return acl2_symbol(self.call(form))

    def pending_record(self):
        return acl2_octets(self.call("(fn-store-pending-octets state)"))

    def complete(self, status):
        return acl2_symbol(self.call("(fn-store-complete :{} state)".format(status)))

    def article_count(self):
        return acl2_nat(self.call("(fn-store-article-count state)"))

    def next_txid(self):
        return acl2_nat(self.call("(fn-store-next-txid state)"))

    def group_next(self, code):
        return acl2_nat(self.call("(fn-store-group-next {} state)".format(code)))

    def pin_count(self):
        return acl2_nat(self.call("(fn-store-pin-count state)"))

    def reserved(self):
        return acl2_nat(self.call("(fn-store-reserved state)"))

    def lookup(self, msgid):
        return acl2_octets(self.call("(fn-store-lookup '" + self.literal(msgid) + " state)"))

    def lookup_found(self, msgid):
        return acl2_boolean(self.call("(fn-store-lookup-foundp '" + self.literal(msgid) + " state)"))

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
    def __init__(self, root, writable=False):
        self.root = Path(root).absolute()
        self.writable = writable
        self.lock_fd = None
        self.config = None
        self.frontier = None
        self.fenced = False

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
        fd = None
        try:
            fd = os.open(self.lock_path, flags, 0o600)
            if not stat.S_ISREG(os.fstat(fd).st_mode):
                os.close(fd)
                fd = None
                raise StoreFault("refusing non-regular writer lock")
            fcntl.flock(fd, (fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH) | fcntl.LOCK_NB)
            return fd
        except StoreFault:
            raise
        except (OSError, BlockingIOError) as error:
            if fd is not None:
                os.close(fd)
            if error.errno == errno.ELOOP:
                raise StoreFault("refusing writer-lock symlink") from error
            raise StoreError("store is already locked") from error

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

    def initialize(self):
        self._safe_directory(self.root, create=True)
        lock_fd = self._open_lock(exclusive=True, create=True)
        try:
            self._safe_directory(self.transactions, create=True)
            self._safe_directory(self.staging, create=True)
            config = config_with_checksum(DEFAULT_CONFIG)
            raw = canonical_json(config) + b"\n"
            try:
                fd = os.open(self.config_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            except FileExistsError:
                self._load_config()
            else:
                try:
                    write_all(fd, raw)
                    fsync_file(fd)
                finally:
                    os.close(fd)
                fsync_dir(self.root)
                self.config = config
            frontier = self._frontier_with_checksum(0)
            encoded_frontier = canonical_json(frontier) + b"\n"
            try:
                fd = os.open(self.frontier_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            except FileExistsError:
                self._load_frontier()
            else:
                # A missing allocator alongside committed history would permit
                # reuse of an aborted ID.  It is a fault, never an implicit 0.
                if self.transaction_files():
                    os.close(fd)
                    raise StoreFault("refusing missing allocator frontier with committed history")
                try:
                    write_all(fd, encoded_frontier)
                    fsync_file(fd)
                finally:
                    os.close(fd)
                fsync_dir(self.root)
                self.frontier = 0
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
        try:
            # A replacement may have become visible before its directory
            # barrier failed. Recover the observed frontier under the held
            # store lock, never a cached pre-error allocation value.
            self._load_frontier()
            records = self.durable_records(acl2)
            if acl2.recover(records, self.frontier) != "ready":
                raise StoreFault("ACL2 replay rejected committed transaction history")
        except StoreError:
            self.fenced = True
            raise
        # A directory-barrier failure may have left an observed link in cache.
        # Validate and replay first, then establish the recovered namespace
        # frontier before treating it as a usable durable state.
        try:
            fsync_regular(self.config_path)
            fsync_regular(self.frontier_path)
            fsync_dir(self.transactions)
            fsync_dir(self.root)
            fsync_dir(self.root.parent)
        except OSError as error:
            self.fenced = True
            raise StoreIndeterminate("cannot establish recovered namespace frontier") from error
        self.fenced = False
        return records

    def advance_frontier(self, current_txid):
        """Durably consume one local transaction ID before it reaches ACL2."""
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
            fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            try:
                write_all(fd, contents)
                fsync_file(fd)
            finally:
                os.close(fd)
            publication_attempted = True
            os.replace(stage, self.frontier_path)
            fsync_dir(self.root)
            self.frontier = next_frontier
            return next_frontier
        except OSError as error:
            if publication_attempted:
                self.fenced = True
                raise StoreIndeterminate("allocation-frontier update is indeterminate") from error
            raise StoreError("known pre-publication allocator failure: {}".format(error)) from error

    def publish(self, sequence, record, fault=None):
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
            if fault == "prepublish":
                os.unlink(stage)
                fsync_dir(self.staging)
                return "known-abort"
            publication_attempted = True
            os.link(stage, final)
            if fault == "postpublish":
                self.fenced = True
                raise StoreIndeterminate("indeterminate injected failure after final publication")
            fsync_dir(self.transactions)
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
            raise StoreError("known pre-publication store failure: {}".format(error)) from error


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


def open_live_store(path, writable):
    store = Store(path, writable=writable)
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


def command_post(args):
    msgid = args.message_id.encode("ascii")
    payload = read_regular_bounded(args.payload, DEFAULT_CONFIG["max_payload_bytes"])
    store, bridge, records = open_live_store(args.store, writable=True)
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
        next_frontier = store.advance_frontier(current_txid)
        obligation, subject, evidence = metadata(msgid, payload)
        action = bridge.prepare(msgid, payload, codes, obligation,
                                subject, evidence, charge)
        if action != "prepared":
            # The durable allocator intentionally reserves this identity even
            # for duplicate or refused attempts.  ACL2 performs the matching
            # monotone advance; Python never edits node state.
            if bridge.advance_frontier(next_frontier) != "ready":
                raise StoreIndeterminate("ACL2 could not advance consumed transaction ID")
        if action != "prepared":
            raise StoreError("ACL2 refused post: {}".format(action))
        record = bridge.pending_record()
        try:
            outcome = store.publish(len(records), record, args.inject_fault)
        except StoreIndeterminate:
            bridge.complete("indeterminate")
            raise
        except StoreError:
            # The final namespace was not observed, so this is a known abort
            # in the matching ACL2 node rather than an inferred rollback.
            bridge.complete("aborted")
            raise
        if outcome == "known-abort":
            bridge.complete("aborted")
            raise StoreError("injected known abort before publication")
        # The file is already published. A rejected completion or a lost core
        # reply must retain the host fence even if this one-shot CLI then exits.
        # Only matching completion permits further mutation without recovery.
        store.fenced = True
        try:
            completion = bridge.complete("durable")
        except (StoreError, OSError) as error:
            raise StoreIndeterminate("ACL2 completion failed after publication") from error
        if completion != "durable":
            raise StoreIndeterminate("ACL2 rejected durable completion after publication")
        store.fenced = False
        print("committed sequence={} charge={}".format(len(records), charge))
        return 0
    finally:
        bridge.close()
        store.close()


def command_recover(args):
    store, bridge, records = open_live_store(args.store, writable=True)
    try:
        print("recovered transactions={} articles={}".format(len(records), bridge.article_count()))
        return 0
    finally:
        bridge.close()
        store.close()


def command_status(args):
    store, bridge, records = open_live_store(args.store, writable=False)
    try:
        print("transactions={} articles={} unsigned-legacy-experiment".format(
            len(records), bridge.article_count()))
        return 0
    finally:
        bridge.close()
        store.close()


def command_inspect(args):
    store, bridge, unused_records = open_live_store(args.store, writable=False)
    try:
        msgid = args.message_id.encode("ascii")
        if not bridge.lookup_found(msgid):
            return 1
        payload = bridge.lookup(msgid)
        sys.stdout.buffer.write(payload)
        return 0
    finally:
        bridge.close()
        store.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store", required=True, help="local store root")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("init")
    post = sub.add_parser("post")
    post.add_argument("--message-id", required=True)
    post.add_argument("--payload", required=True)
    post.add_argument("--group", action="append", required=True)
    post.add_argument("--charge", type=int)
    post.add_argument("--inject-fault", choices=("prepublish", "postpublish"))
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
        return 2


if __name__ == "__main__":
    sys.exit(main())
