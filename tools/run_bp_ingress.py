#!/usr/bin/env python3
"""Isolated legacy-article BP ingress host experiment.

The caller supplies a bounded BPA inventory/download/delete adapter.  This
module delegates staging to the workflow journal and delegates article parsing,
field extraction, routing, duplicate recognition, and Store admission to ACL2.
It emits no application receipt.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import importlib.util
from pathlib import Path
import sys
from typing import Callable, Iterable

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import run_store  # noqa: E402

DEFAULT_DESTINATION = "dtn://fn.lab/inbox"
DEFAULT_LIFETIME = 3600
MAX_CONTEXT_TEXT = 512


class BpIngressError(RuntimeError):
    pass


class BpDeletePending(BpIngressError):
    """The article was accepted, but the BPA BID remains for a later delete."""


@dataclass(frozen=True)
class IngressResult:
    outcome: str  # accepted | duplicate | rejected
    bid: str
    staged_path: Path


def load_workflow_journal(path: Path):
    """Load Sol's journal by explicit path; do not copy its protocol locally."""
    source = Path(path).resolve()
    module_name = "fn_workflow_journal_" + hashlib.sha256(str(source).encode("utf-8")).hexdigest()[:16]
    if module_name in sys.modules:
        return sys.modules[module_name]
    spec = importlib.util.spec_from_file_location(module_name, source)
    if spec is None or spec.loader is None:
        raise BpIngressError("cannot load workflow journal")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def bounded_ascii_text(value: str, label: str) -> bytes:
    if not isinstance(value, str):
        raise BpIngressError(f"{label} is not text")
    try:
        encoded = value.encode("ascii", "strict")
    except UnicodeEncodeError as error:
        raise BpIngressError(f"{label} is not ASCII transport metadata") from error
    if not 1 <= len(encoded) <= MAX_CONTEXT_TEXT or any(byte < 33 or byte > 126 for byte in encoded):
        raise BpIngressError(f"{label} has an invalid bounded transport representation")
    return encoded


class Acl2BpIngress(run_store.Acl2Store):
    """The ordinary Store bridge plus the certified BP ingress composition."""
    def __init__(self):
        super().__init__()
        try:
            self.call('(include-book "books/bp-ingress")')
            self.call('(ld "host/bp-ingress-host.lisp" :ld-error-action :return :ld-error-triples t)')
            run_store.acl2_symbol(self.call("(fn-bpi-host-reset state)"))
        except BaseException:
            self.close()
            raise

    def extract_message_id(self, adu: bytes) -> bytes:
        return run_store.acl2_octets(self.call(
            "(fn-bpi-host-message-id '" + self.literal(adu) + " state)"))

    def ingress_prepare(self, destination: bytes, source_eid: bytes, bid: bytes,
                        lifetime: int, archive_id: bytes, subject: bytes,
                        evidence: bytes, charge: int, adu: bytes) -> str:
        if not isinstance(lifetime, int) or isinstance(lifetime, bool) or not 0 <= lifetime <= 0xffffffff:
            raise BpIngressError("BP lifetime is not a uint32")
        form = "(fn-bpi-host-prepare '" + self.literal(destination)
        form += " '" + self.literal(source_eid) + " '" + self.literal(bid)
        form += " " + str(lifetime) + " '" + self.literal(archive_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " " + str(charge) + " '" + self.literal(adu) + " state)"
        value = run_store.acl2_result(self.call(form)).upper()
        if value == b":PREPARED":
            return "prepared"
        if value == b":REJECTED":
            return "rejected"
        if value == b":INVALID":
            return "invalid"
        raise BpIngressError("unexpected ACL2 BP ingress result")

    def already_durable(self, destination: bytes, source_eid: bytes, bid: bytes,
                        lifetime: int, archive_id: bytes, subject: bytes,
                        evidence: bytes, charge: int, adu: bytes) -> bool:
        form = "(fn-bpi-host-already-durablep '" + self.literal(destination)
        form += " '" + self.literal(source_eid) + " '" + self.literal(bid)
        form += " " + str(lifetime) + " '" + self.literal(archive_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        form += " " + str(charge) + " '" + self.literal(adu) + " state)"
        return run_store.acl2_boolean(self.call(form))


def open_live_bp_store(path: Path, writable: bool):
    store = run_store.Store(path, writable=writable)
    store.acquire()
    bridge = None
    try:
        bridge = Acl2BpIngress()
        records = store.recover(bridge)
        return store, bridge, records
    except BaseException:
        if bridge is not None:
            bridge.close()
        store.close()
        raise


def _defer_bpa_delete(_bid: str) -> None:
    # WorkflowJournal records the durable inbound item and reports this exact
    # pending deletion.  Actual deletion waits for ACL2 Store outcome below.
    raise OSError("defer BPA deletion until Store acceptance")


def _staged_item(journal, journal_module, bid: str, inventory, download) -> Path:
    try:
        journal.stage_inbound(bid, inventory, download, _defer_bpa_delete)
    except journal_module.InboundDeletePending:
        # The journal has fsynced and published the inbound item.  Reopen it
        # before use so recovery validates the durable image rather than a
        # pre-publication in-memory path.
        journal.close()
        journal.open()
        for found_bid, path in journal.inbound_items:
            if found_bid == bid:
                return path
        raise BpIngressError("journal lost its durably staged inbound BID")
    raise BpIngressError("workflow journal deleted BPA before Store acceptance")


def _consume_reserved_refusal(store, bridge) -> None:
    store.fenced = True
    if bridge.refuse_reservation() != "refused":
        raise run_store.StoreIndeterminate("ACL2 could not consume rejected BP reservation")


def _publish_accepted(store, bridge, records, record) -> None:
    try:
        outcome = store.publish(bridge, len(records), record)
    except run_store.StoreIndeterminate:
        raise
    except run_store.StoreError:
        if not store.fenced:
            store.fenced = True
            if bridge.known_abort() != "aborted":
                raise run_store.StoreIndeterminate("ACL2 rejected known BP pre-publication abort")
        raise
    if outcome != "durable":
        raise run_store.StoreIndeterminate("unexpected BP Store publication result")
    store.fenced = True
    if store.finish(bridge) != "durable":
        raise run_store.StoreIndeterminate("ACL2 rejected BP durable completion")


def ingest_bpa_adu(*, store_root: Path, journal_root: Path, journal_module_path: Path,
                   bid: str, inventory: Callable[[], Iterable[str]],
                   download: Callable[[str], bytes], delete: Callable[[str], None],
                   destination: str = DEFAULT_DESTINATION,
                   source_eid: str, lifetime: int = DEFAULT_LIFETIME) -> IngressResult:
    """Stage one BPA BID, then accept its exact legacy ADU through ACL2.

    A valid existing durable article is a duplicate replay and permits BPA
    deletion. Any parser, policy, or Store rejection leaves the staged BID and
    BPA bundle present for explicit operator/workflow handling.
    """
    destination_bytes = bounded_ascii_text(destination, "destination EID")
    source_bytes = bounded_ascii_text(source_eid, "source EID")
    bid_bytes = bounded_ascii_text(bid, "BPA BID")
    if not isinstance(lifetime, int) or isinstance(lifetime, bool) or not 0 <= lifetime <= 0xffffffff:
        raise BpIngressError("BP lifetime is not a uint32")
    workflow = load_workflow_journal(journal_module_path)
    # Until Sol's ACL2 workflow replay bridge is available, this ingress owns
    # only an empty workflow-record namespace.  Never silently treat prior
    # workflow decisions as an identity image.
    def empty_workflow_replay(records):
        if records:
            raise BpIngressError("nonempty workflow journal needs its ACL2 replay bridge")
        return ()
    journal = workflow.WorkflowJournal(Path(journal_root), empty_workflow_replay)
    journal.open()
    store = bridge = None
    try:
        staged_path = _staged_item(journal, workflow, bid, inventory, download)
        staged_bid, adu = workflow.decode_inbound(staged_path.read_bytes())
        if staged_bid != bid:
            raise BpIngressError("staged BPA BID does not match requested BID")
        if not isinstance(adu, bytes):
            raise BpIngressError("workflow journal returned non-byte ADU")
        if len(adu) > run_store.DEFAULT_CONFIG["max_payload_bytes"]:
            raise BpIngressError("staged ADU exceeds certified article/Store bound")
        store, bridge, records = open_live_bp_store(Path(store_root), writable=True)
        # The ACL2 wrapper alone extracts Message-ID.  Metadata remains the
        # existing Store host's domain-separated payload hash construction.
        msgid = bridge.extract_message_id(adu)
        if not msgid:
            return IngressResult("rejected", bid, staged_path)
        archive_id, subject, evidence = run_store.metadata(msgid, adu)
        charge = run_store.conservative_charge(adu)
        if bridge.already_durable(destination_bytes, source_bytes, bid_bytes, lifetime,
                                  archive_id, subject, evidence, charge, adu):
            try:
                delete(bid)
            except Exception as error:
                raise BpDeletePending("exact durable ADU awaits BPA delete") from error
            return IngressResult("duplicate", bid, staged_path)
        if len(records) >= store.config["max_transactions"]:
            raise BpIngressError("Store transaction capacity reached")
        store.advance_frontier(bridge, bridge.next_txid())
        action = bridge.ingress_prepare(destination_bytes, source_bytes, bid_bytes, lifetime,
                                        archive_id, subject, evidence, charge, adu)
        if action != "prepared":
            _consume_reserved_refusal(store, bridge)
            return IngressResult("rejected", bid, staged_path)
        _publish_accepted(store, bridge, records, bridge.pending_record())
        try:
            delete(bid)
        except Exception as error:
            raise BpDeletePending("durably accepted ADU awaits BPA delete") from error
        return IngressResult("accepted", bid, staged_path)
    finally:
        if bridge is not None:
            bridge.close()
        if store is not None:
            store.close()
        journal.close()


def _file_inventory(path: Path):
    return [line.strip() for line in path.read_text("utf-8").splitlines() if line.strip()]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--journal", required=True, type=Path)
    parser.add_argument("--workflow-journal", required=True, type=Path,
                        help="Sol workflow_journal.py; it is not copied into this bridge")
    parser.add_argument("--bid", required=True)
    parser.add_argument("--inventory", required=True, type=Path,
                        help="test/lab newline BID inventory snapshot")
    parser.add_argument("--adu", required=True, type=Path,
                        help="test/lab non-destructive downloaded ADU for --bid")
    parser.add_argument("--source-eid", required=True)
    parser.add_argument("--destination", default=DEFAULT_DESTINATION)
    parser.add_argument("--lifetime", type=int, default=DEFAULT_LIFETIME)
    args = parser.parse_args(argv)
    try:
        inventory = lambda: _file_inventory(args.inventory)
        download = lambda found_bid: args.adu.read_bytes() if found_bid == args.bid else b""
        deleted = []
        result = ingest_bpa_adu(store_root=args.store, journal_root=args.journal,
                                journal_module_path=args.workflow_journal, bid=args.bid,
                                inventory=inventory, download=download,
                                delete=deleted.append, destination=args.destination,
                                source_eid=args.source_eid, lifetime=args.lifetime)
        print(f"{result.outcome} bid={result.bid} staged={result.staged_path}")
        return 0
    except (BpIngressError, run_store.StoreError, OSError, UnicodeError) as error:
        print(f"bp-ingress: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
