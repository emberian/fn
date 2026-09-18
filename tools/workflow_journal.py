#!/usr/bin/env python3
"""Provisional durable BP workflow journal.

The journal owns framing and filesystem ordering only.  Callers must supply an
ACL2-backed replay callback; this module does not decide workflow state,
receipts, release eligibility, or transport success.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import fcntl
import os
from pathlib import Path
import struct
from typing import Callable, Iterable, Sequence

MAGIC = b"FNWF"
SCHEMA = 1
MAX_TEXT = 512
MAX_RECORD = 16_384
MAX_RECORDS = 4_096
MAX_AGGREGATE = 16 * 1024 * 1024
MAX_INBOUND_BUNDLE = 4 * 1024 * 1024
MAX_INBOUND_COUNT = 1_024
MAX_INBOUND_AGGREGATE = 64 * 1024 * 1024
MAX_BPA_INVENTORY = 8_192

KINDS = {
    "config": 1,
    "enqueue": 2,
    "attempt": 3,
    "transport": 4,
    "receipt-intent": 5,
    "outcome": 6,
    "retry-request": 7,
}
KIND_NAMES = {value: key for key, value in KINDS.items()}

FIELDS = {
    "config": (("local-eid", "text"), ("peer-eid", "text"),
               ("policy-id", "text"), ("receipt-authority", "text"),
               ("bp-lifetime", "nat"), ("incarnation", "text"),
               ("authorization-context", "text")),
    "enqueue": (("txid", "nat"), ("tx-generation", "nat"),
                ("work-id", "text"), ("msgid", "text"),
                ("immutable-subject", "text"),
                ("archive-obligation-id", "text"),
                ("forward-obligation-id", "text"), ("peer-eid", "text"),
                ("policy-id", "text"), ("terms-id", "text")),
    "attempt": (("txid", "nat"), ("tx-generation", "nat"),
                ("work-id", "text"), ("attempt-id", "text"),
                ("attempt-generation", "nat"), ("local-eid", "text"),
                ("peer-eid", "text"), ("policy-id", "text"),
                ("bp-lifetime", "nat")),
    "transport": (("work-id", "text"), ("attempt-id", "text"),
                  ("attempt-generation", "nat"), ("status", "status")),
    "receipt-intent": (("txid", "nat"), ("tx-generation", "nat"),
                       ("receipt-id", "text"), ("work-id", "text"),
                       ("immutable-subject", "text"), ("issuer-eid", "text"),
                       ("peer-eid", "text"), ("policy-id", "text"),
                       ("incarnation", "text"),
                       ("authorization-context", "text"),
                       ("terms-id", "text")),
    "outcome": (("txid", "nat"), ("tx-generation", "nat"),
                ("phase", "phase"), ("result", "result")),
    "retry-request": (("work-id", "text"), ("attempt-id", "text"),
                      ("attempt-generation", "nat"), ("policy-id", "text")),
}
STATUSES = {name: number for number, name in enumerate((
    "intent", "bpa-submit-replied", "bpa-accepted", "attempted", "forwarded",
    "delivered", "deleted", "expired", "unknown", "no-contact",
    "inbound-persisted", "dequeued", "restart-observed"), 1)}
PHASES = {"ordinary": 1, "recovery": 2}
RESULTS = {"durable": 1, "aborted": 2, "committed": 3, "absent": 4}


class JournalError(RuntimeError): pass
class JournalFault(JournalError): pass
class JournalUncertain(JournalError): pass
class InboundDeletePending(JournalError): pass


def fsync_dir(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try: os.fsync(fd)
    finally: os.close(fd)


def write_all(fd: int, data: bytes) -> None:
    view = memoryview(data)
    while view:
        count = os.write(fd, view)
        if count <= 0: raise OSError("short workflow journal write")
        view = view[count:]


def _text(value: object) -> bytes:
    if not isinstance(value, str): raise JournalError("text field is not a string")
    encoded = value.encode("utf-8", "strict")
    if not encoded or len(encoded) > MAX_TEXT: raise JournalError("text field length")
    return struct.pack(">H", len(encoded)) + encoded


def _nat(value: object) -> bytes:
    if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value < 2**64:
        raise JournalError("natural field range")
    return struct.pack(">Q", value)


def encode_record(kind: str, values: dict[str, object]) -> bytes:
    if kind not in FIELDS or set(values) != {name for name, _ in FIELDS[kind]}:
        raise JournalError("record fields do not match schema")
    payload = bytearray()
    for name, field_type in FIELDS[kind]:
        value = values[name]
        if field_type == "text": payload += _text(value)
        elif field_type == "nat": payload += _nat(value)
        elif field_type == "status":
            if value not in STATUSES: raise JournalError("unknown transport status")
            payload.append(STATUSES[value])
        elif field_type == "phase":
            if value not in PHASES: raise JournalError("unknown outcome phase")
            payload.append(PHASES[value])
        elif field_type == "result":
            if value not in RESULTS: raise JournalError("unknown outcome result")
            if (values["phase"], value) not in {
                    ("ordinary", "durable"), ("ordinary", "aborted"),
                    ("recovery", "committed"), ("recovery", "absent")}:
                raise JournalError("outcome phase/result mismatch")
            payload.append(RESULTS[value])
    header = MAGIC + bytes((SCHEMA, KINDS[kind])) + struct.pack(">I", len(payload))
    framed = header + payload
    framed += hashlib.sha256(framed).digest()
    if len(framed) > MAX_RECORD: raise JournalError("record exceeds bound")
    return framed


def decode_record(data: bytes) -> tuple[str, dict[str, object]]:
    if len(data) < 42 or len(data) > MAX_RECORD: raise JournalFault("record size")
    if data[:4] != MAGIC or data[4] != SCHEMA: raise JournalFault("magic/schema")
    if hashlib.sha256(data[:-32]).digest() != data[-32:]: raise JournalFault("checksum")
    kind = KIND_NAMES.get(data[5])
    if kind is None: raise JournalFault("record kind")
    size = struct.unpack(">I", data[6:10])[0]
    if size != len(data) - 42: raise JournalFault("payload length")
    payload = memoryview(data)[10:-32]; offset = 0; values = {}
    reverse_status = {v: k for k, v in STATUSES.items()}
    reverse_phase = {v: k for k, v in PHASES.items()}
    reverse_result = {v: k for k, v in RESULTS.items()}
    for name, field_type in FIELDS[kind]:
        if field_type == "nat":
            if offset + 8 > len(payload): raise JournalFault("truncated natural")
            values[name] = struct.unpack(">Q", payload[offset:offset+8])[0]; offset += 8
        elif field_type == "text":
            if offset + 2 > len(payload): raise JournalFault("truncated text length")
            count = struct.unpack(">H", payload[offset:offset+2])[0]; offset += 2
            if not 1 <= count <= MAX_TEXT or offset + count > len(payload):
                raise JournalFault("text length")
            try: values[name] = bytes(payload[offset:offset+count]).decode("utf-8", "strict")
            except UnicodeDecodeError as error: raise JournalFault("invalid UTF-8") from error
            offset += count
        else:
            if offset >= len(payload): raise JournalFault("truncated enumeration")
            table = (reverse_status if field_type == "status" else
                     reverse_phase if field_type == "phase" else reverse_result)
            if payload[offset] not in table: raise JournalFault("unknown enumeration")
            values[name] = table[payload[offset]]; offset += 1
    if offset != len(payload): raise JournalFault("trailing payload")
    if kind == "outcome" and (values["phase"], values["result"]) not in {
            ("ordinary", "durable"), ("ordinary", "aborted"),
            ("recovery", "committed"), ("recovery", "absent")}:
        raise JournalFault("outcome phase/result mismatch")
    return kind, values


@dataclass(frozen=True)
class Published:
    sequence: int
    path: Path


class WorkflowJournal:
    def __init__(self, root: Path, replay: Callable[[Sequence[tuple[str, dict]]], object]):
        self.root = Path(root); self.records = self.root / "records"; self.staging = self.root / "staging"
        self.inbound = self.root / "inbound"
        self.replay = replay; self.fenced = True; self.image = None; self.lock_fd = None
        self.inbound_items = ()

    def open(self) -> object:
        self.fenced=True; self.image=None; self.inbound_items=()
        if self.lock_fd is not None:
            raise JournalFault("workflow journal is already open")
        self.root.mkdir(mode=0o700, parents=True, exist_ok=True)
        lock_path=self.root/"workflow.lock"
        lock_fd=os.open(lock_path, os.O_RDWR|os.O_CREAT, 0o600)
        try: fcntl.flock(lock_fd, fcntl.LOCK_EX|fcntl.LOCK_NB)
        except OSError as error:
            os.close(lock_fd)
            raise JournalFault("workflow journal is already owned") from error
        self.lock_fd=lock_fd
        try:
            self.records.mkdir(mode=0o700, exist_ok=True); self.staging.mkdir(mode=0o700, exist_ok=True)
            self.inbound.mkdir(mode=0o700, exist_ok=True)
            fsync_dir(self.root); fsync_dir(self.root.parent)
            decoded=[]; aggregate=0
            entries=sorted(self.records.iterdir())
            if len(entries) > MAX_RECORDS: raise JournalFault("record count")
            for sequence, path in enumerate(entries):
                if path.is_symlink() or not path.is_file() or path.name != f"{sequence:016x}.wf":
                    raise JournalFault("record namespace")
                size=path.stat().st_size
                if size < 42 or size > MAX_RECORD: raise JournalFault("record size")
                aggregate += size
                if aggregate > MAX_AGGREGATE: raise JournalFault("aggregate bytes")
                data=path.read_bytes()
                if len(data) != size: raise JournalFault("record changed while reading")
                decoded.append(decode_record(data))
                fd=os.open(path, os.O_RDONLY)
                try: os.fsync(fd)
                finally: os.close(fd)
            fsync_dir(self.records)
            inbox=[]; inbound_aggregate=0; inbound_entries=list(self.inbound.iterdir())
            if len(inbound_entries) > MAX_INBOUND_COUNT: raise JournalFault("inbound count")
            for path in inbound_entries:
                if path.is_symlink() or not path.is_file() or path.suffix != ".bp":
                    raise JournalFault("inbound namespace")
                size=path.stat().st_size; inbound_aggregate += size
                if size > MAX_INBOUND_BUNDLE + MAX_TEXT + 42: raise JournalFault("inbound size")
                if inbound_aggregate > MAX_INBOUND_AGGREGATE: raise JournalFault("inbound aggregate")
                bid, _payload = decode_inbound(path.read_bytes())
                expected=hashlib.sha256(bid.encode("utf-8")).hexdigest()+".bp"
                if path.name != expected: raise JournalFault("inbound name")
                inbox.append((bid,path))
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

    def publish(self, kind: str, values: dict[str, object], fault: str | None=None,
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
            if fault == "write": raise OSError("injected write fault")
            os.fsync(fd)
            if fault == "file-fsync": raise OSError("injected file barrier fault")
        except Exception:
            os.close(fd)
            try: stage.unlink()
            except OSError: pass
            raise
        os.close(fd)
        try:
            if fault == "process-prepublish": os._exit(91)
            if fault == "prepublish": raise JournalError("known prepublication failure")
            attempted=True; os.link(stage, final)
            if fault == "process-postlink": os._exit(92)
            if fault == "link": raise OSError("injected link uncertainty")
            fsync_dir(self.records)
            if fault == "directory-fsync": raise OSError("injected directory uncertainty")
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
        return published

    def publish_intent(self, kind: str, values: dict[str, object],
                       fault: str | None=None) -> Published:
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
        return self.publish(kind, values, fault, replay_image=False)

    def publish_outcome(self, txid: int, generation: int, phase: str,
                        result: str, fault: str | None=None) -> Published:
        return self.publish("outcome", {"txid": txid, "tx-generation": generation,
                            "phase": phase, "result": result}, fault)

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

    def stage_inbound(self, bid: str, inventory: Callable[[], Iterable[str]],
                      download: Callable[[str], bytes],
                      delete: Callable[[str], None]) -> Path:
        """Durably stage a BPA bundle before explicitly deleting it by BID."""
        if self.fenced: raise JournalFault("journal is fenced")
        found=False
        for count, item in enumerate(inventory()):
            if count >= MAX_BPA_INVENTORY: raise JournalError("BPA inventory bound")
            if item == bid: found=True
        if not isinstance(bid, str) or not bid or not found:
            raise JournalError("BID is not present in inventory")
        existing=list(self.inbound.iterdir())
        local_name=hashlib.sha256(bid.encode("utf-8", "strict")).hexdigest()+".bp"
        final=self.inbound/local_name
        if not final.exists() and len(existing) >= MAX_INBOUND_COUNT:
            raise JournalError("inbound count")
        aggregate=sum(path.stat().st_size for path in existing)
        payload=download(bid)
        if not isinstance(payload, bytes) or len(payload) > MAX_INBOUND_BUNDLE:
            raise JournalError("inbound bundle bound")
        framed=encode_inbound(bid,payload)
        if not final.exists() and aggregate + len(framed) > MAX_INBOUND_AGGREGATE:
            raise JournalError("inbound aggregate")
        stage=self.staging/(local_name+f".{os.getpid()}.tmp")
        if final.exists():
            if final.is_symlink() or final.read_bytes() != framed:
                self.fenced=True; raise JournalFault("conflicting staged BID")
            fd=os.open(final,os.O_RDONLY)
            try: os.fsync(fd)
            finally: os.close(fd)
            fsync_dir(self.inbound)
            try: delete(bid)
            except Exception as error:
                raise InboundDeletePending(f"durable inbound awaits BPA delete: {bid}") from error
            return final
        fd=os.open(stage, os.O_WRONLY|os.O_CREAT|os.O_EXCL, 0o600)
        attempted=False
        try:
            write_all(fd, framed); os.fsync(fd); os.close(fd); fd=-1
            attempted=True; os.link(stage, final); fsync_dir(self.inbound)
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
        return final

    def retry_staged_delete(self, bid: str, inventory: Callable[[], Iterable[str]],
                            delete: Callable[[str], None]) -> Path:
        """Finish BPA deletion for an already durable frame without downloading again."""
        if self.fenced: raise JournalFault("journal is fenced")
        present=False
        for count, item in enumerate(inventory()):
            if count >= MAX_BPA_INVENTORY: raise JournalError("BPA inventory bound")
            if item == bid: present=True
        if not present: raise JournalError("BID is not present in inventory")
        name=hashlib.sha256(bid.encode("utf-8", "strict")).hexdigest()+".bp"
        final=self.inbound/name
        if final.is_symlink() or not final.is_file():
            raise JournalFault("durable inbound frame is absent")
        stored_bid, _payload=decode_inbound(final.read_bytes())
        if stored_bid != bid:
            self.fenced=True; raise JournalFault("conflicting staged BID")
        fd=os.open(final,os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
        fsync_dir(self.inbound)
        try: delete(bid)
        except Exception as error:
            raise InboundDeletePending(f"durable inbound awaits BPA delete: {bid}") from error
        return final


def encode_inbound(bid: str, payload: bytes) -> bytes:
    bid_bytes=bid.encode("utf-8","strict")
    if not 1 <= len(bid_bytes) <= MAX_TEXT or len(payload) > MAX_INBOUND_BUNDLE:
        raise JournalError("inbound frame bound")
    head=b"FNBI"+struct.pack(">HI",len(bid_bytes),len(payload))+bid_bytes+payload
    return head+hashlib.sha256(head).digest()


def decode_inbound(data: bytes) -> tuple[str,bytes]:
    if len(data)<42 or data[:4]!=b"FNBI": raise JournalFault("inbound frame")
    bid_len,payload_len=struct.unpack(">HI",data[4:10])
    if not 1<=bid_len<=MAX_TEXT or payload_len>MAX_INBOUND_BUNDLE:
        raise JournalFault("inbound frame bound")
    if len(data)!=42+bid_len+payload_len: raise JournalFault("inbound frame length")
    if hashlib.sha256(data[:-32]).digest()!=data[-32:]: raise JournalFault("inbound checksum")
    try: bid=data[10:10+bid_len].decode("utf-8","strict")
    except UnicodeDecodeError as error: raise JournalFault("inbound BID UTF-8") from error
    return bid,data[10+bid_len:-32]
