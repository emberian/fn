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
from tools import bundle_bridge  # noqa: E402

DEFAULT_DESTINATION = "dtn://fn.lab/inbox"
DEFAULT_LIFETIME = 3600
MAX_CONTEXT_TEXT = 512


class BpIngressError(RuntimeError):
    pass


class BpDeletePending(BpIngressError):
    """The article is durably accepted; the BPA BID remains for a later delete.

    This is an acceptance carrying a pending transport obligation, not a
    refusal and not an uncertain acceptance, so it keeps the outcome it earned.
    """
    def __init__(self, message: str, outcome: str, bid: str, staged_path: Path):
        super().__init__(message)
        self.outcome = outcome
        self.bid = bid
        self.staged_path = staged_path


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
            self.call('(include-book "books/codec-attach")')
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
                        evidence: bytes, charge: int, adu: bytes,
                        observation=None) -> str:
        if not isinstance(lifetime, int) or isinstance(lifetime, bool) or not 0 <= lifetime <= 0xffffffff:
            raise BpIngressError("BP lifetime is not a uint32")
        form = "(fn-bpi-host-prepare '" + self.literal(destination)
        form += " '" + self.literal(source_eid) + " '" + self.literal(bid)
        form += " " + str(lifetime) + " '" + self.literal(archive_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        monotonic_ns, wall_ns, error_ms, has_wall = (
            bundle_bridge.observation() if observation is None else observation)
        form += " " + str(charge) + " '" + self.literal(adu)
        form += " {} {} {} {} state)".format(
            monotonic_ns, wall_ns, error_ms, "t" if has_wall else "nil")
        value = run_store.acl2_result(self.call(form)).upper()
        if value == b":PREPARED":
            return "prepared"
        if value == b":REJECTED":
            return "rejected"
        if value == b":CLOCK-UNUSABLE":
            return "clock-unusable"
        if value == b":INVALID":
            return "invalid"
        raise BpIngressError("unexpected ACL2 BP ingress result")

    def already_durable(self, destination: bytes, source_eid: bytes, bid: bytes,
                        lifetime: int, archive_id: bytes, subject: bytes,
                        evidence: bytes, charge: int, adu: bytes,
                        observation=None) -> bool:
        form = "(fn-bpi-host-already-durablep '" + self.literal(destination)
        form += " '" + self.literal(source_eid) + " '" + self.literal(bid)
        form += " " + str(lifetime) + " '" + self.literal(archive_id)
        form += " '" + self.literal(subject) + " '" + self.literal(evidence)
        monotonic_ns, wall_ns, error_ms, has_wall = (
            bundle_bridge.observation() if observation is None else observation)
        form += " " + str(charge) + " '" + self.literal(adu)
        form += " {} {} {} {} state)".format(
            monotonic_ns, wall_ns, error_ms, "t" if has_wall else "nil")
        return run_store.acl2_boolean(self.call(form))


def open_live_bp_store(path: Path, writable: bool, faults=run_store.NO_FAULTS):
    store = run_store.Store(path, writable=writable, faults=faults)
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


def identify_bundle(bid: str, bundle: Callable[[str], bytes],
                    wall_error_ms: int = bundle_bridge.DEFAULT_WALL_ERROR_MS,
                    bridge=None) -> bundle_bridge.BundleReport:
    """Ask ACL2 what this bundle is and whether it is still live.

    The raw octets the agent holds are the only evidence used.  A refusal here
    means nothing is staged at all: the BID stays in the agent's inventory for
    an explicit operator decision, which is a different thing from a bundle fn
    staged and then declined to accept.
    """
    raw = bundle(bid)
    if not isinstance(raw, bytes) or not raw:
        raise BpIngressError("BPA returned no bundle octets for the BID")
    return bundle_bridge.session(bridge).report(raw, wall_error_ms)


def _staged_item(journal, journal_module, bid: str, identity: bytes,
                 inventory, download) -> Path:
    try:
        journal.stage_inbound(bid, identity, inventory, download, _defer_bpa_delete)
    except journal_module.InboundDeletePending:
        # The journal has fsynced and published the inbound item.  Reopen it
        # before use so recovery validates the durable image rather than a
        # pre-publication in-memory path.
        journal.close()
        journal.open()
        for _found_bid, found_identity, path in journal.inbound_items:
            if found_identity == identity:
                return path
        raise BpIngressError("journal lost its durably staged bundle identity")
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
                   bundle: Callable[[str], bytes],
                   destination: str = DEFAULT_DESTINATION,
                   source_eid: str, lifetime: int = DEFAULT_LIFETIME,
                   wall_error_ms: int = bundle_bridge.DEFAULT_WALL_ERROR_MS) -> IngressResult:
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
        try:
            report = identify_bundle(bid, bundle, wall_error_ms)
        except bundle_bridge.BundleRefused as refusal:
            # Staged nowhere, deleted nowhere: refused, and distinct from a
            # bundle whose expiry this node cannot decide.
            return IngressResult("refused-identity:" + refusal.reason, bid, None)
        if report.decision == "expired":
            return IngressResult("refused-expired", bid, None)
        if report.decision == "uncertain":
            return IngressResult("uncertain-expiry", bid, None)
        observation = bundle_bridge.observation(wall_error_ms)
        staged_path = _staged_item(journal, workflow, bid, report.identity,
                                   inventory, download)
        _staged_bid, staged_identity, adu = workflow.decode_inbound(
            staged_path.read_bytes())
        if staged_identity != report.identity:
            raise BpIngressError("staged bundle identity does not match the bundle")
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
                                  archive_id, subject, evidence, charge, adu,
                                  observation):
            try:
                delete(bid)
            except Exception as error:
                raise BpDeletePending("exact durable ADU awaits BPA delete",
                                      "duplicate", bid, staged_path) from error
            return IngressResult("duplicate", bid, staged_path)
        if len(records) >= store.config["max_transactions"]:
            raise BpIngressError("Store transaction capacity reached")
        store.advance_frontier(bridge, bridge.next_txid())
        action = bridge.ingress_prepare(destination_bytes, source_bytes, bid_bytes, lifetime,
                                        archive_id, subject, evidence, charge, adu,
                                        observation)
        if action != "prepared":
            _consume_reserved_refusal(store, bridge)
            return IngressResult("refused-clock-unusable" if action == "clock-unusable"
                                 else "rejected", bid, staged_path)
        _publish_accepted(store, bridge, records, bridge.pending_record())
        try:
            delete(bid)
        except Exception as error:
            raise BpDeletePending("durably accepted ADU awaits BPA delete",
                                  "accepted", bid, staged_path) from error
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
    parser = run_store.UsageParser(description=__doc__)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--journal", required=True, type=Path)
    parser.add_argument("--workflow-journal", required=True, type=Path,
                        help="Sol workflow_journal.py; it is not copied into this bridge")
    parser.add_argument("--bid", required=True)
    parser.add_argument("--inventory", required=True, type=Path,
                        help="test/lab newline BID inventory snapshot")
    parser.add_argument("--adu", required=True, type=Path,
                        help="test/lab non-destructive downloaded ADU for --bid")
    parser.add_argument("--bundle", required=True, type=Path,
                        help="the raw BP bundle octets the BPA holds for --bid; "
                             "ACL2 derives the identity and expiry from these")
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
                                bundle=lambda found_bid: (
                                    args.bundle.read_bytes()
                                    if found_bid == args.bid else b""),
                                delete=deleted.append, destination=args.destination,
                                source_eid=args.source_eid, lifetime=args.lifetime)
        if result.outcome == "uncertain-expiry":
            print(f"{result.outcome} bid={result.bid} staged=none bpa-delete=none")
            return run_store.EXIT_UNCERTAIN
        if result.outcome.startswith("refused-"):
            print(f"{result.outcome} bid={result.bid} staged=none bpa-delete=none")
            return run_store.EXIT_REFUSED
        print(f"{result.outcome} bid={result.bid} staged={result.staged_path} bpa-delete=done")
        return run_store.EXIT_OK
    except BpDeletePending as pending:
        # A durable acceptance whose BPA delete has not completed is still an
        # acceptance; the pending transport obligation is named, not encoded
        # as a failure the caller would read as a refusal.
        print(f"{pending.outcome} bid={pending.bid} staged={pending.staged_path} "
              f"bpa-delete=pending")
        return run_store.EXIT_OK
    except (BpIngressError, run_store.StoreError, OSError, UnicodeError) as error:
        print(f"bp-ingress: {error}", file=sys.stderr)
        return run_store.exit_code_for(
            error, default=run_store.EXIT_REFUSED if isinstance(error, BpIngressError)
            else run_store.EXIT_FAULT)


if __name__ == "__main__":
    raise SystemExit(main())
