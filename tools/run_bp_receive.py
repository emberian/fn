#!/usr/bin/env python3
"""Durable receiver path for one staged portable fn-bpa request ADU.

FNBI staging retains the full wrapper ADU.  ACL2 alone unwraps its exact legacy
article, validates request context, and drives Store/receiver-journal decisions.
No receipt is signed or transmitted here; a committed canonical ADU is returned.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable
import sys

from tools import bundle_bridge, run_bp_ingress, run_store, workflow_journal
from tools.receipt_bridge import Acl2ReceiptBridge
from tools.receipt_journal import ReceiptJournal, JournalError, JournalFault, JournalUncertain

DESTINATION = "dtn://fn.lab/inbox"
POLICY_ID = "bp-lab-policy-v0"
ISSUER = "dtn://fn.lab/issuer"
LIFETIME = 300
MAX_BID_OCTETS = 512
MAX_RECEIPT_ID_OCTETS = 256

class BpReceiveError(RuntimeError): pass
class BpReceiveDeletePending(BpReceiveError):
    """The receipt decision is durable; the BPA BID awaits a later delete.

    It carries the acceptance it earned so a caller can tell this apart from a
    refusal or an uncertain decision.
    """
    def __init__(self, message, outcome="accepted", receipt_adu=b"", staged_path=None):
        super().__init__(message)
        self.outcome = outcome
        self.receipt_adu = receipt_adu
        self.staged_path = staged_path
@dataclass(frozen=True)
class ReceiveResult:
    outcome: str
    receipt_adu: bytes
    staged_path: Path


def _defer_delete(_bid):
    raise OSError("defer BPA deletion until receipt decision commits")

def _stage(inbox_root, bid, identity, inventory, download, faults=run_store.NO_FAULTS):
    journal = workflow_journal.WorkflowJournal(Path(inbox_root), lambda records: () if not records else (_ for _ in ()).throw(BpReceiveError("nonempty sender workflow journal")), faults=faults)
    journal.open()
    try:
        try:
            journal.stage_inbound(bid, identity, inventory, download, _defer_delete)
        except workflow_journal.InboundDeletePending:
            journal.close(); journal.open()
            for _found, found_identity, path in journal.inbound_items:
                if found_identity == identity: return journal, path
            raise BpReceiveError("durably staged identity was not recovered")
        raise BpReceiveError("staging deleted BPA before receiver decision")
    except BaseException:
        journal.close(); raise

def _acl2_octets(bridge, form):
    return run_store.acl2_octets(bridge.call(form))
def _acl2_bool(bridge, form):
    return run_store.acl2_boolean(bridge.call(form))
def _request_status(bridge, request_adu):
    body = run_store.acl2_result(bridge.call(
        "(fn-bpreq-request-status '" + bridge.literal(request_adu) + " state)")).upper()
    statuses = {b":NEW": "new", b":COMMITTED": "committed",
                b":CONTEXT": "context", b":PENDING": "pending",
                b":CONFLICT": "conflict", b":MALFORMED": "malformed",
                b":REFUSED": "refused", b":BLOCKED": "blocked"}
    if body not in statuses:
        raise BpReceiveError("ACL2 request-status boundary")
    return statuses[body]

def _work_identity(bridge, request_adu):
    """Derive the receipt identity from ACL2's work id, before any mutation.

    The length bound is a property of the identity, so it is known here rather
    than after the article has been charged and its context persisted.
    """
    work_id = _acl2_octets(bridge, "(fn-bpreq-work-id '" + bridge.literal(request_adu) + " state)")
    if not work_id:
        raise BpReceiveError("ACL2 request work-id boundary")
    receipt_id = b"receipt:" + work_id
    try:
        return work_id.decode("ascii"), receipt_id.decode("ascii"), len(receipt_id)
    except UnicodeDecodeError as error:
        raise BpReceiveError("ACL2 request metadata encoding") from error

def _durably_decide(receipt_journal, request_adu, work_id, receipt_id,
                    faults=run_store.NO_FAULTS):
    receipt_journal.prepare_receipt(work_id, receipt_id)
    faults.at("receipt-intent")
    receipt_journal.commit_receipt(work_id, receipt_id, "committed")
    faults.at("receipt-committed")
    receipt = receipt_journal.receipt_adu(request_adu)
    if not receipt:
        raise BpReceiveError("receipt decision did not regenerate canonical ADU")
    faults.at("receipt-regenerated")
    return receipt

def _delete_after_decision(delete, bid, outcome="accepted", receipt=b"", staged=None,
                           faults=run_store.NO_FAULTS):
    try:
        delete(bid)
        faults.at("bpa-deleted")
    except Exception as error:
        raise BpReceiveDeletePending("committed receipt awaits BPA delete",
                                     outcome, receipt, staged) from error

def receive_bpa_request(*, store_root, inbox_root, receipt_root, bid, inventory,
                        download, delete, bundle, source_eid,
                        local_policy_authorized=True,
                        wall_error_ms=bundle_bridge.DEFAULT_WALL_ERROR_MS,
                        pending_outcome=None, faults=run_store.NO_FAULTS,
                        store_faults=run_store.NO_FAULTS,
                        inbox_faults=run_store.NO_FAULTS,
                        receipt_faults=run_store.NO_FAULTS):
    """Stage, accept, decide, and regenerate one portable request receipt.

    The explicit Boolean is a trusted local lab A_POLICY input.  Request wire
    `authorization-context` is retained by ACL2 but never substitutes for it.
    """
    if local_policy_authorized is not True:
        raise BpReceiveError("local A_POLICY did not authorize receiver request")
    if not isinstance(bid, str) or not bid:
        raise BpReceiveError("BPA BID boundary")
    try:
        encoded_bid = bid.encode("ascii", "strict")
    except UnicodeEncodeError as error:
        # A non-ASCII BID is a bounded-transport-metadata refusal, not a codec
        # exception escaping the receiver boundary.
        raise BpReceiveError("BPA BID boundary") from error
    if len(encoded_bid) > MAX_BID_OCTETS:
        raise BpReceiveError("BPA BID boundary")
    source_bytes = run_bp_ingress.bounded_ascii_text(source_eid, "observed BPA source EID")
    # Identity and expiry are settled from the bundle's own primary block before
    # anything is written.  A refusal, an expiry and an undecidable expiry are
    # three different answers and each leaves the BPA bundle exactly where it
    # was: nothing is staged, nothing is deleted.
    try:
        report = run_bp_ingress.identify_bundle(bid, bundle, wall_error_ms)
    except bundle_bridge.BundleRefused as refusal:
        return ReceiveResult("refused-identity:" + refusal.reason, b"", None)
    if report.decision == "expired":
        return ReceiveResult("refused-expired", b"", None)
    if report.decision == "uncertain":
        return ReceiveResult("uncertain-expiry", b"", None)
    inbox, staged = _stage(inbox_root, bid, report.identity, inventory, download,
                           inbox_faults)
    faults.at("staged")
    store = bridge = receipt_journal = None
    try:
        # The staged frame keeps whichever BID first carried this bundle; the
        # identity is what must agree with the bundle in hand.
        _staged_bid, staged_identity, request_adu = workflow_journal.decode_inbound(
            staged.read_bytes())
        if staged_identity != report.identity:
            raise BpReceiveError("staged bundle identity boundary")
        if len(request_adu) > 65538:
            raise BpReceiveError("staged request boundary")
        store, bridge, records = run_bp_ingress.open_live_bp_store(
            Path(store_root), writable=True, faults=store_faults)
        bridge.call('(ld "host/bp-receive-host.lisp" :ld-error-action :return :ld-error-triples t)')
        receipt_bridge = Acl2ReceiptBridge(bridge)
        receipt_journal = ReceiptJournal(Path(receipt_root), receipt_bridge,
                                        faults=receipt_faults)
        receipt_journal.open()
        if not list(receipt_journal.records.iterdir()):
            receipt_journal.initialize({"destination-eid": DESTINATION, "policy-id": POLICY_ID,
                                        "issuer-eid": ISSUER})
        # The journal-owned ACL2 state is queried before Store mutation.  A
        # same work with different exact request bytes is a conflict; an exact
        # committed retry only regenerates the already-durable receipt.
        status = _request_status(bridge, request_adu)
        if status == "conflict":
            raise BpReceiveError("conflicting request context")
        if status in {"malformed", "refused"}:
            raise BpReceiveError("request context is not safely reusable")
        if status == "blocked":
            raise BpReceiveError("another receipt intent is pending recovery")
        # Preflight the receipt identity before any Store mutation, charge or
        # receiver-journal write.  A work id whose receipt id cannot be
        # represented is refused with the BPA request still present, rather
        # than after the article has been charged and its context persisted.
        work_id, receipt_id, receipt_id_octets = _work_identity(bridge, request_adu)
        if receipt_id_octets > MAX_RECEIPT_ID_OCTETS:
            return ReceiveResult("refused-receipt-id", b"", staged)
        if status == "pending":
            if pending_outcome not in {"committed", "absent"}:
                raise BpReceiveError("pending receipt needs explicit recovery outcome")
            receipt_journal.commit_receipt(work_id, receipt_id, pending_outcome)
            if pending_outcome == "absent":
                # The durable intent has been resolved absent, but the BPA
                # request remains for a later explicit receiver action.
                return ReceiveResult("pending-absent", b"", staged)
            receipt = receipt_journal.receipt_adu(request_adu)
            if not receipt:
                raise BpReceiveError("committed recovery did not regenerate receipt")
            _delete_after_decision(delete, bid, "duplicate", receipt, staged, faults)
            return ReceiveResult("duplicate", receipt, staged)
        if status == "committed":
            prior = receipt_journal.receipt_adu(request_adu)
            if not prior:
                raise BpReceiveError("committed request did not regenerate receipt")
            _delete_after_decision(delete, bid, "duplicate", prior, staged, faults)
            return ReceiveResult("duplicate", prior, staged)
        if status == "context":
            receipt = _durably_decide(receipt_journal, request_adu, work_id, receipt_id,
                                      faults)
            _delete_after_decision(delete, bid, "duplicate", receipt, staged, faults)
            return ReceiveResult("duplicate", receipt, staged)
        existing_record = _acl2_octets(
            bridge, "(fn-bpreq-existing-record '" + bridge.literal(request_adu) + " state)")
        if existing_record:
            # Store publication may have completed before FNRJ context
            # publication.  Bind only ACL2's recovered exact record; do not
            # allocate a replacement transaction or charge a second article.
            receipt_journal.accept_request(bid, request_adu, existing_record,
                                           policy_authorized=True)
            faults.at("context-persisted")
            receipt = _durably_decide(receipt_journal, request_adu, work_id, receipt_id,
                                      faults)
            _delete_after_decision(delete, bid, "accepted", receipt, staged, faults)
            return ReceiveResult("accepted", receipt, staged)
        article = _acl2_octets(bridge, "(fn-bpreq-article '" + bridge.literal(request_adu) + " state)")
        if not article or len(article) > store.config["max_payload_bytes"]:
            raise BpReceiveError("ACL2 rejected request/article boundary")
        # ACL2's article gate at this article's own figure, as the native
        # `store post` asks it.  A transaction published past the configured
        # bound makes every later Store.recover() fault, so the store would be
        # unopenable with no recovery path.  Refuse before any frontier
        # advance or charge; the BPA request and its staged frame stay present.
        verdict = bridge.article_verdict(store.config["profile"], article)
        if verdict == "rejected":
            raise BpReceiveError("ACL2 Store refused request article")
        if verdict != "admissible":
            return ReceiveResult("refused-capacity", b"", staged)
        msgid = bridge.extract_message_id(article)
        if not msgid: raise BpReceiveError("ACL2 rejected article Message-ID")
        archive, subject, evidence = run_store.metadata(msgid, article)
        if not _acl2_bool(bridge, "(fn-bpreq-subject-matchp '" + bridge.literal(request_adu) +
                           " '" + bridge.literal(subject) + " state)"):
            raise BpReceiveError("request subject disagrees with accepted-article subject")
        # Store mutation follows the same actual allocator/publication path as
        # raw ingress, but only for the article extracted by ACL2 from FNBI.
        store.advance_frontier(bridge, bridge.next_txid())
        action = bridge.ingress_prepare(DESTINATION.encode(), source_bytes, bid.encode(), LIFETIME,
                                        archive, subject, evidence, run_store.conservative_charge(article), article)
        if action != "prepared":
            run_bp_ingress._consume_reserved_refusal(store, bridge)
            raise BpReceiveError("ACL2 Store refused request article")
        record = bridge.pending_record()
        run_bp_ingress._publish_accepted(store, bridge, records, record)
        faults.at("store-published")
        receipt_journal.accept_request(bid, request_adu, record, policy_authorized=True)
        faults.at("context-persisted")
        receipt = _durably_decide(receipt_journal, request_adu, work_id, receipt_id,
                                  faults)
        _delete_after_decision(delete, bid, "accepted", receipt, staged, faults)
        return ReceiveResult("accepted", receipt, staged)
    finally:
        if receipt_journal is not None: receipt_journal.close()
        if bridge is not None: bridge.close()
        if store is not None: store.close()
        inbox.close()
