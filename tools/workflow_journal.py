#!/usr/bin/env python3
"""Provisional durable BP workflow journal.

The journal owns framing and filesystem ordering only.  Callers must supply an
ACL2-backed replay callback; this module does not decide workflow state,
receipts, release eligibility, or transport success.
"""

from __future__ import annotations

from dataclasses import dataclass
import errno
import hashlib
import fcntl
import os
from pathlib import Path
import stat
from typing import Callable, Iterable, Sequence

from tools import frame_bridge

# The durability barrier and the fault-point protocol have exactly one owner.
try:
    from tools.run_store import FaultPoints, NO_FAULTS, durable_barrier
except ImportError:  # loaded with tools/ itself on sys.path
    from run_store import FaultPoints, NO_FAULTS, durable_barrier

MAGIC = b"FNWF"
SCHEMA = 1
MAX_TEXT = 512
MAX_RECORD = 16_384
MAX_RECORDS = 4_096
MAX_AGGREGATE = 16 * 1024 * 1024
# `*fn-frame-max-inbound-payload*`, the u32 frame width since P2 (D27); the
# frame bridge refuses to open when the two differ.  MAX_INBOUND_AGGREGATE
# below still caps this Python inbox at 64 MiB in total: a data cap the
# retiring Python host keeps (planning/evidence/bounds-join-2026-09-25.md).
MAX_INBOUND_BUNDLE = 4_294_967_295
# `*fn-frame-max-identity*`: the canonical primary-block identity ACL2 derives
# from a staged bundle.  The inbox is keyed by this, never by the agent's BID.
MAX_IDENTITY = 1_152
MAX_INBOUND_COUNT = 1_024
MAX_INBOUND_AGGREGATE = 64 * 1024 * 1024
MAX_BPA_INVENTORY = 8_192
# Frame head (10) + BID text field (2 + cap) + identity blob field (4 + cap)
# + trailer (32); the same slice bound ACL2 checks on the way back in.
MAX_INBOUND_FRAME = MAX_INBOUND_BUNDLE + MAX_TEXT + MAX_IDENTITY + 48

# The record kinds, their field names, their field types and the transport,
# phase, result and authorization enumerations all live in `books/frame`.
# `frame_bridge` asks for the schema of a kind and caches the answer; this
# module keeps no copy of any of them.


class JournalError(RuntimeError): pass
class JournalFault(JournalError): pass
class JournalUncertain(JournalError): pass
class InboundDeletePending(JournalError): pass


def fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try: durable_barrier(fd)
    finally: os.close(fd)


def read_regular_barriered(path: Path, maximum: int) -> bytes:
    """Read and barrier one regular file through a single no-follow descriptor.

    Checking the pathname and then opening it again admits a replacement
    between the two calls, so the type check, the size, the bytes and the
    barrier all come from the same open descriptor.
    """
    try:
        fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    except OSError as error:
        if error.errno == errno.ELOOP: raise JournalFault("refusing journal symlink") from error
        raise
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode): raise JournalFault("refusing non-regular journal file")
        if info.st_size > maximum: raise JournalFault("journal file exceeds bound")
        chunks, remaining = [], maximum + 1
        while remaining:
            chunk = os.read(fd, min(65536, remaining))
            if not chunk: break
            chunks.append(chunk); remaining -= len(chunk)
        data = b"".join(chunks)
        if len(data) != info.st_size: raise JournalFault("record changed while reading")
        durable_barrier(fd)
        return data
    finally:
        os.close(fd)


def open_exclusive_lock(path: Path, owned: str) -> int:
    """Open one regular non-symlink lock pathname and take it exclusively.

    Opening the pathname and contending for the lock are distinct outcomes: a
    missing or unusable lock pathname is an invalid journal state, and only a
    refused lock means another owner holds the journal.
    """
    try:
        fd = os.open(path, os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0), 0o600)
    except OSError as error:
        if error.errno == errno.ELOOP:
            raise JournalFault(f"refusing {owned} lock symlink") from error
        raise JournalFault(f"cannot open {owned} lock: {error}") from error
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise JournalFault(f"refusing non-regular {owned} lock")
    except BaseException:
        os.close(fd); raise
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError as error:
        os.close(fd)
        raise JournalFault(f"{owned} journal is already owned") from error
    return fd


def write_all(fd: int, data: bytes) -> None:
    view = memoryview(data)
    while view:
        count = os.write(fd, view)
        if count <= 0: raise OSError("short workflow journal write")
        view = view[count:]


def encode_record(kind: str, values: dict[str, object], bridge=None) -> bytes:
    """`books/frame` builds the record; the host appends the trailer only."""
    try:
        return frame_bridge.session(bridge).record_frame("workflow", kind, values)
    except frame_bridge.BridgeError as error:
        raise JournalError(str(error)) from error


def decode_record(data: bytes, bridge=None) -> tuple[str, dict[str, object]]:
    """`books/frame` parses the record and compares the host's digest."""
    try:
        return frame_bridge.session(bridge).record_unframe("workflow", data)
    except (frame_bridge.BridgeError, UnicodeDecodeError) as error:
        raise JournalFault(str(error)) from error


@dataclass(frozen=True)
class Published:
    sequence: int
    path: Path


class WorkflowJournal:
    def __init__(self, root: Path, replay: Callable[[Sequence[tuple[str, dict]]], object],
                 faults: FaultPoints = NO_FAULTS):
        self.root = Path(root); self.records = self.root / "records"; self.staging = self.root / "staging"
        self.inbound = self.root / "inbound"
        self.replay = replay; self.fenced = True; self.image = None; self.lock_fd = None
        self.inbound_items = ()
        self.faults = faults

    def open(self) -> object:
        self.fenced=True; self.image=None; self.inbound_items=()
        if self.lock_fd is not None:
            raise JournalFault("workflow journal is already open")
        self.root.mkdir(mode=0o700, parents=True, exist_ok=True)
        self.lock_fd=open_exclusive_lock(self.root/"workflow.lock", "workflow")
        try:
            self.records.mkdir(mode=0o700, exist_ok=True); self.staging.mkdir(mode=0o700, exist_ok=True)
            self.inbound.mkdir(mode=0o700, exist_ok=True)
            fsync_dir(self.root); fsync_dir(self.root.parent)
            decoded=[]; aggregate=0
            entries=sorted(self.records.iterdir())
            if len(entries) > MAX_RECORDS: raise JournalFault("record count")
            for sequence, path in enumerate(entries):
                if path.name != f"{sequence:016x}.wf": raise JournalFault("record namespace")
                data=read_regular_barriered(path, MAX_RECORD)
                if len(data) < 42: raise JournalFault("record size")
                aggregate += len(data)
                if aggregate > MAX_AGGREGATE: raise JournalFault("aggregate bytes")
                decoded.append(decode_record(data))
            fsync_dir(self.records)
            inbox=[]; inbound_aggregate=0; inbound_entries=list(self.inbound.iterdir())
            if len(inbound_entries) > MAX_INBOUND_COUNT: raise JournalFault("inbound count")
            for path in inbound_entries:
                if path.suffix != ".bp": raise JournalFault("inbound namespace")
                data=read_regular_barriered(path, MAX_INBOUND_FRAME)
                inbound_aggregate += len(data)
                if inbound_aggregate > MAX_INBOUND_AGGREGATE: raise JournalFault("inbound aggregate")
                bid, identity, _payload = decode_inbound(data)
                # The file name is the identity's digest, so a recovered inbox
                # is keyed by what the bundle says it is and not by the handle
                # whichever agent happened to hand it over.
                expected=hashlib.sha256(identity).hexdigest()+".bp"
                if path.name != expected: raise JournalFault("inbound name")
                inbox.append((bid,identity,path))
            fsync_dir(self.inbound)
            self.image=self.replay(tuple(decoded)); self.inbound_items=tuple(inbox); self.fenced=False
            return self.image
        except Exception as error:
            self.close()
            if isinstance(error, JournalError): raise
            raise JournalFault("workflow recovery failed") from error

    def close(self) -> None:
        self.fenced=True
        if self.lock_fd is not None:
            fcntl.flock(self.lock_fd, fcntl.LOCK_UN)
            os.close(self.lock_fd); self.lock_fd=None

    def publish(self, kind: str, values: dict[str, object],
                replay_image: bool=True) -> Published:
        if self.fenced: raise JournalFault("journal is fenced")
        record=(kind, values)
        encoded=encode_record(kind, values)
        entries=sorted(self.records.iterdir())
        if kind != "config" and hasattr(self.replay, "history_preflight"):
            history=tuple(decode_record(path.read_bytes()) for path in entries)
            if self.replay.history_preflight(history+(record,)) is not True:
                raise JournalError("ACL2 rejected workflow durable history before publication")
        if kind != "config" and hasattr(self.replay, "preflight"):
            if self.replay.preflight(record) is not True:
                raise JournalError("ACL2 rejected workflow record before publication")
        sequence=len(entries)
        if sequence >= MAX_RECORDS: raise JournalFault("record count")
        # Refuse before staging when the image would exceed its own reopen cap.
        # Existing records remain authoritative; refusal cannot expire work or
        # release any application/archive obligation.
        aggregate=sum(path.stat().st_size for path in entries)
        if aggregate + len(encoded) > MAX_AGGREGATE:
            raise JournalFault("aggregate bytes")
        stage=self.staging / f"{sequence:016x}.{os.getpid()}.tmp"
        final=self.records / f"{sequence:016x}.wf"
        fd=os.open(stage, os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600)
        attempted=False
        try:
            write_all(fd, encoded)
            self.faults.at("write")
            durable_barrier(fd)
            self.faults.at("file-fsync")
        except Exception:
            os.close(fd)
            try: stage.unlink()
            except OSError: pass
            raise
        os.close(fd)
        try:
            self.faults.at("prepublish")
            attempted=True; os.link(stage, final)
            self.faults.at("postlink")
            fsync_dir(self.records)
            self.faults.at("directory-fsync")
        except Exception as error:
            if attempted:
                self.fenced=True
                raise JournalUncertain("publication outcome requires recovery") from error
            raise
        finally:
            try: stage.unlink()
            except OSError: pass
        published=Published(sequence, final)
        # Publication is only storage completion.  Rebuild through ACL2 before
        # the caller can observe an acknowledgement or invoke the BPA.
        if hasattr(self.replay, "apply_record") and kind != "config":
            try:
                self.replay.apply_record(record)
                self.image=self.replay
            except Exception:
                self.fenced=True
                raise
        elif replay_image:
            try:
                ordered=sorted(self.records.iterdir())
                self.image=self.replay(tuple(decode_record(path.read_bytes())
                                             for path in ordered))
            except Exception:
                self.fenced=True
                raise
        self.faults.at("image-applied")
        return published

    def publish_intent(self, kind: str, values: dict[str, object]) -> Published:
        """Publish an intent only when one worst-case resolution still fits."""
        if kind not in {"enqueue", "attempt", "receipt-intent"}:
            raise JournalError("record is not a workflow intent")
        entries=list(self.records.iterdir())
        encoded=encode_record(kind, values)
        aggregate=sum(path.stat().st_size for path in entries)
        if len(entries) + 2 > MAX_RECORDS:
            raise JournalFault("record count lacks resolution headroom")
        if aggregate + len(encoded) + MAX_RECORD > MAX_AGGREGATE:
            raise JournalFault("aggregate lacks resolution headroom")
        return self.publish(kind, values, replay_image=False)

    def publish_outcome(self, txid: int, generation: int, phase: str,
                        result: str) -> Published:
        return self.publish("outcome", {"txid": txid, "tx-generation": generation,
                            "phase": phase, "result": result})

    def abort_intent(self, values: dict[str, object]) -> Published:
        """Persist a known abort; the reserved pair remains consumed in ACL2."""
        return self.publish_outcome(values["txid"], values["tx-generation"],
                                    "ordinary", "aborted")

    def recover_intent(self, values: dict[str, object], result: str) -> Published:
        """Persist inspection of a previously unresolved durable intent."""
        if result not in {"committed", "absent"}:
            raise JournalError("invalid recovery result")
        return self.publish_outcome(values["txid"], values["tx-generation"],
                                    "recovery", result)

    def initialize(self, config: dict[str, object]) -> Published:
        """Create the sole first CONFIG record and install its ACL2 image."""
        if self.fenced or list(self.records.iterdir()):
            raise JournalFault("workflow journal is already initialized")
        return self.publish("config", config)

    def persist_attempt_then_call(self, values: dict[str, object], bpa_call: Callable[[], object]) -> object:
        self.publish_intent("attempt", values)
        self.publish_outcome(values["txid"], values["tx-generation"],
                             "ordinary", "durable")
        if hasattr(self.replay, "take_submit") and self.replay.take_submit(values) is not True:
            self.fenced=True
            raise JournalFault("ACL2 did not grant current submit permission")
        return bpa_call()

    def persist_enqueue(self, values: dict[str, object],
                        durable_node_binding: Callable[[dict[str, object]], bool]) -> Published:
        """Acknowledge enqueue only after the caller proves the article binding.

        The callback must consult the already-recovered node image.  It is a
        boundary check, not a second implementation of article acceptance.
        """
        if durable_node_binding(values) is not True:
            raise JournalError("enqueue lacks durable node article binding")
        self.publish_intent("enqueue", values)
        return self.publish_outcome(values["txid"], values["tx-generation"],
                                    "ordinary", "durable")

    def stage_inbound(self, bid: str, identity: bytes,
                      inventory: Callable[[], Iterable[str]],
                      download: Callable[[str], bytes],
                      delete: Callable[[str], None]) -> Path:
        """Durably stage a BPA bundle before explicitly deleting it by BID.

        `identity` is the canonical primary-block identity ACL2 derived from the
        bundle's own octets; this journal never derives it and never inspects
        it.  It is the inbox key, so a redelivery under a fresh BID lands on the
        same file and reconciles, while two bundles that merely carry the same
        payload stay apart.  The BID remains the transport handle and nothing
        else: it is what `delete` is called with.
        """
        if self.fenced: raise JournalFault("journal is fenced")
        if not isinstance(bid, str) or not bid: raise JournalError("BID is not present in inventory")
        if not isinstance(identity, (bytes, bytearray)) or not identity \
                or len(identity) > MAX_IDENTITY:
            raise JournalError("bundle identity bound")
        identity=bytes(identity)
        found=self._in_inventory(bid, inventory)
        local_name=hashlib.sha256(identity).hexdigest()+".bp"
        final=self.inbound/local_name
        if not found:
            # A BID that is durably staged here and absent from the inventory
            # reconciles an earlier pending delete as completed: the request
            # took effect and only its reply was lost.  Absence without a
            # durable frame is an ordinary missing bundle.
            if not final.exists(): raise JournalError("BID is not present in inventory")
            return self._validated_durable_frame(identity, final)
        existing=list(self.inbound.iterdir())
        if not final.exists() and len(existing) >= MAX_INBOUND_COUNT:
            raise JournalError("inbound count")
        aggregate=sum(path.stat().st_size for path in existing)
        payload=download(bid)
        if not isinstance(payload, bytes) or len(payload) > MAX_INBOUND_BUNDLE:
            raise JournalError("inbound bundle bound")
        framed=encode_inbound(bid,identity,payload)
        if not final.exists() and aggregate + len(framed) > MAX_INBOUND_AGGREGATE:
            raise JournalError("inbound aggregate")
        stage=self.staging/(local_name+f".{os.getpid()}.tmp")
        if final.exists():
            # The stored frame keeps the BID it was first staged under: a
            # redelivery of one bundle under a fresh transport handle is the
            # same bundle, so the BID is not part of what must agree.  The
            # identity and the bundle octets are.
            if final.is_symlink():
                self.fenced=True; raise JournalFault("conflicting staged bundle")
            _stored_bid, stored_identity, stored_payload=decode_inbound(
                read_regular_barriered(final, MAX_INBOUND_FRAME))
            if stored_identity != identity or stored_payload != payload:
                self.fenced=True; raise JournalFault("conflicting staged bundle")
            fsync_dir(self.inbound)
            self.faults.at("inbound-reconciled")
            try: delete(bid)
            except Exception as error:
                raise InboundDeletePending(f"durable inbound awaits BPA delete: {bid}") from error
            return final
        fd=os.open(stage, os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600)
        attempted=False
        try:
            write_all(fd, framed); durable_barrier(fd)
            self.faults.at("inbound-staged-durable")
            # Retire the descriptor number before closing it: a failing close
            # may already have released it, and closing again would close a
            # descriptor this journal does not own.
            handle, fd = fd, -1
            os.close(handle)
            attempted=True; os.link(stage, final)
            self.faults.at("inbound-linked")
            fsync_dir(self.inbound)
            self.faults.at("inbound-durable")
        except Exception as error:
            if fd >= 0: os.close(fd)
            if attempted: self.fenced=True; raise JournalUncertain("inbound staging uncertain") from error
            raise
        finally:
            try: stage.unlink()
            except OSError: pass
        try: delete(bid)
        except Exception as error:
            raise InboundDeletePending(f"durable inbound awaits BPA delete: {bid}") from error
        self.faults.at("inbound-deleted")
        return final

    def _in_inventory(self, bid: str, inventory: Callable[[], Iterable[str]]) -> bool:
        present=False
        for count, item in enumerate(inventory()):
            if count >= MAX_BPA_INVENTORY: raise JournalError("BPA inventory bound")
            if item == bid: present=True
        return present

    def _validated_durable_frame(self, identity: bytes, final: Path) -> Path:
        """Re-barrier one durable inbound frame and recheck its identity."""
        if final.is_symlink() or not final.is_file():
            raise JournalFault("durable inbound frame is absent")
        _stored_bid, stored_identity, _payload=decode_inbound(
            read_regular_barriered(final, MAX_INBOUND_FRAME))
        if stored_identity != bytes(identity):
            self.fenced=True; raise JournalFault("conflicting staged identity")
        fsync_dir(self.inbound)
        return final

    def retry_staged_delete(self, bid: str, identity: bytes,
                            inventory: Callable[[], Iterable[str]],
                            delete: Callable[[str], None]) -> Path:
        """Finish BPA deletion for an already durable frame without downloading again.

        A BID still in the inventory is retried.  A BID absent from it is
        reconciled as a completed delete: the only local evidence a lost delete
        reply leaves is the bundle's absence, and a durable frame proves the
        request was ours.  Absence is never treated as an fn acceptance event.
        """
        if self.fenced: raise JournalFault("journal is fenced")
        if not isinstance(identity, (bytes, bytearray)) or not identity:
            raise JournalError("bundle identity bound")
        name=hashlib.sha256(bytes(identity)).hexdigest()+".bp"
        final=self.inbound/name
        if not self._in_inventory(bid, inventory):
            # Returning normally is what clears the pending state, because the
            # caller raised InboundDeletePending to create it.
            return self._validated_durable_frame(identity, final)
        self._validated_durable_frame(identity, final)
        try: delete(bid)
        except Exception as error:
            raise InboundDeletePending(f"durable inbound awaits BPA delete: {bid}") from error
        self.faults.at("inbound-retry-deleted")
        return final


def encode_inbound(bid: str, identity: bytes, payload: bytes, bridge=None) -> bytes:
    """ACL2 builds the frame head through the BID field; the bundle is opaque.

    An inbound bundle is up to four mebibytes, which cannot cross the decimal
    octet bridge, so the host concatenates the bundle and appends the trailer
    over bytes it never interprets.  Every decision -- magic, version, kind,
    the declared length, the BID and identity fields and their bounds -- is
    ACL2's.
    """
    try:
        return frame_bridge.session(bridge).inbound_frame(bid, identity, payload)
    except frame_bridge.BridgeError as error:
        raise JournalError(str(error)) from error


def decode_inbound(data: bytes, bridge=None) -> tuple[str, bytes, bytes]:
    try:
        return frame_bridge.session(bridge).inbound_unframe(data)
    except (frame_bridge.BridgeError, UnicodeDecodeError) as error:
        raise JournalFault(str(error)) from error
