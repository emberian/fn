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
DEFAULT_CONFIG = {
    "format": "fn-store-experiment-1",
    "groups": ["fn.letters", "fn.test"],
    "capacity": 1048576,
    "max_record_bytes": 32768,
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
                    b":INDETERMINATE", b":DUPLICATE", b":CONFLICT", b":INVALID",
                    b":REFUSED", b":FAULT"}:
        raise StoreError("unexpected ACL2 action: {}".format(body.decode("ascii", "replace")))
    return body.decode("ascii").lower()[1:]


def acl2_nat(output):
    body = acl2_result(output)
    if not re.fullmatch(rb"[0-9]+", body):
        raise StoreError("ACL2 returned a non-natural")
    return int(body)


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

    def recover(self, records):
        literal = "(" + " ".join(self.literal(record) for record in records) + ")"
        return acl2_symbol(self.call("(fn-store-recover '" + literal + " state)"))

    def prepare(self, msgid, payload, group_codes, obligation_id, subject, evidence, charge):
        form = "(fn-store-prepare '" + self.literal(msgid) + " '" + self.literal(payload)
        form += " '" + self.numeric_list(group_codes) + " '" + self.literal(obligation_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " " + str(charge) + " state)"
        return acl2_symbol(self.call(form))

    def pending_record(self):
        return acl2_octets(self.call("(fn-store-pending-octets state)"))

    def complete(self, status):
        return acl2_symbol(self.call("(fn-store-complete :{} state)".format(status)))

    def article_count(self):
        return acl2_nat(self.call("(fn-store-article-count state)"))

    def group_next(self, code):
        return acl2_nat(self.call("(fn-store-group-next {} state)".format(code)))

    def lookup(self, msgid):
        return acl2_octets(self.call("(fn-store-lookup '" + self.literal(msgid) + " state)"))

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
        self.fenced = False

    @property
    def config_path(self): return self.root / "config.json"
    @property
    def transactions(self): return self.root / "transactions"
    @property
    def staging(self): return self.root / "staging"
    @property
    def lock_path(self): return self.root / "writer.lock"

    def _safe_directory(self, path, create=False):
        if create and not path.exists():
            path.mkdir(mode=0o700)
            fsync_dir(path.parent)
        try:
            st = os.lstat(path)
        except FileNotFoundError:
            raise StoreFault("missing store directory: {}".format(path))
        if not path.is_dir() or os.path.islink(path):
            raise StoreFault("refusing non-directory store path: {}".format(path))
        return st

    def initialize(self):
        if self.root.exists():
            self._safe_directory(self.root)
        else:
            self.root.mkdir(mode=0o700, parents=False)
            fsync_dir(self.root.parent)
        self._safe_directory(self.transactions, create=True)
        self._safe_directory(self.staging, create=True)
        config = config_with_checksum(DEFAULT_CONFIG)
        raw = canonical_json(config) + b"\n"
        try:
            fd = os.open(self.config_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        except FileExistsError:
            self._load_config()
            return
        try:
            write_all(fd, raw)
            fsync_file(fd)
        finally:
            os.close(fd)
        fsync_dir(self.root)
        self.config = config

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

    def acquire(self):
        self._safe_directory(self.root)
        self._safe_directory(self.transactions)
        self._safe_directory(self.staging)
        self._load_config()
        flags = os.O_RDWR | os.O_CREAT if self.writable else os.O_RDONLY
        try:
            self.lock_fd = os.open(self.lock_path, flags, 0o600)
            fcntl.flock(self.lock_fd, (fcntl.LOCK_EX if self.writable else fcntl.LOCK_SH) | fcntl.LOCK_NB)
        except (OSError, BlockingIOError) as error:
            self.close()
            raise StoreError("store is already locked") from error

    def close(self):
        if self.lock_fd is not None:
            try:
                fcntl.flock(self.lock_fd, fcntl.LOCK_UN)
            finally:
                os.close(self.lock_fd)
                self.lock_fd = None

    def transaction_files(self):
        files = []
        try:
            entries = list(os.scandir(self.transactions))
        except OSError as error:
            raise StoreFault("cannot enumerate transactions") from error
        for entry in entries:
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
        for sequence, path in self.transaction_files():
            check_regular(path)
            raw = read_regular_bounded(
                path, len(MAGIC) + 4 + self.config["max_record_bytes"] + TRAILER_BYTES)
            record = unframe(raw, self.config["max_record_bytes"])
            if acl2.record_sequence(record) != sequence:
                raise StoreFault("record sequence does not match immutable filename")
            records.append(record)
        return records

    def recover(self, acl2):
        records = self.durable_records(acl2)
        if acl2.recover(records) != "ready":
            raise StoreFault("ACL2 replay rejected committed transaction history")
        # A directory-barrier failure may have left an observed link in cache.
        # Validate and replay first, then establish the recovered namespace
        # frontier before treating it as a usable durable state.
        try:
            fsync_dir(self.transactions)
            fsync_dir(self.root)
        except OSError as error:
            raise StoreIndeterminate("cannot establish recovered namespace frontier") from error
        return records

    def publish(self, sequence, record, fault=None):
        if self.fenced:
            raise StoreIndeterminate("store is fenced pending recovery")
        if len(record) > self.config["max_record_bytes"]:
            raise StoreFault("ACL2 record exceeds configured bound")
        name = "{:020d}.txn".format(sequence)
        final = self.transactions / name
        stage = self.staging / (".stage-{}-{}".format(os.getpid(), os.urandom(12).hex()))
        data = frame(record)
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
            os.link(stage, final)
            if fault == "postpublish":
                self.fenced = True
                raise StoreIndeterminate("indeterminate injected failure after final publication")
            fsync_dir(self.transactions)
            # Staging files are ignored by recovery.  Their best-effort cleanup
            # occurs only after the final namespace barrier succeeded.
            os.unlink(stage)
            fsync_dir(self.staging)
            return "durable"
        except FileExistsError as error:
            self.fenced = True
            raise StoreIndeterminate("immutable transaction name was unexpectedly occupied") from error
        except StoreIndeterminate:
            raise
        except OSError as error:
            # Once a final link could possibly have been installed, the host
            # cannot classify ordinary I/O failure as a known abort.
            if final.exists():
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
    payload = Path(args.payload).read_bytes()
    if len(payload) > DEFAULT_CONFIG["max_record_bytes"]:
        raise StoreError("payload exceeds fixed experimental bound")
    store, bridge, records = open_live_store(args.store, writable=True)
    try:
        obligation, subject, evidence = metadata(msgid, payload)
        charge = args.charge if args.charge is not None else conservative_charge(payload)
        action = bridge.prepare(msgid, payload, group_codes(args.group, store.config), obligation,
                                subject, evidence, charge)
        if action == "duplicate":
            print("duplicate")
            return 0
        if action == "conflict":
            raise StoreError("conflicting immutable Message-ID")
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
        if bridge.complete("durable") != "durable":
            raise StoreIndeterminate("ACL2 rejected durable completion after publication")
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
        payload = bridge.lookup(args.message_id.encode("ascii"))
        if not payload:
            return 1
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
