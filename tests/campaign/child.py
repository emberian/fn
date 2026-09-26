#!/usr/bin/env python3
"""Run one campaign scenario up to one named cut, then block until killed.

The child runs the real host entry point.  The only test-only code is the
injector object: `PauseAt.at` is called by the host at its own named fault
point, writes down what the host had already told the world, reports readiness
on a pipe and then blocks on a read the parent never answers.  The kill is
therefore ordered strictly after the boundary the cut names, and no host
durable path contains a campaign branch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parent.parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import run_bp_ingress, run_bp_receive, run_store, workflow_journal  # noqa: E402
from tools.receipt_journal import ReceiptJournal  # noqa: E402
from tools.workflow_bridge import Acl2WorkflowReplay  # noqa: E402

BASELINE_MSGID = "<baseline@fn.example>"
CAMPAIGN_MSGID = "<campaign@fn.example>"
BASELINE_PAYLOAD = b"acknowledged before the campaign operation begins"
CAMPAIGN_PAYLOAD = b"the operation the campaign interrupts"
GROUPS = ("fn.letters", "fn.test")
SOURCE_EID = "dtn://sender.lab"
CAMPAIGN_BID = "bid-campaign"
RETRY_BID = "bid-campaign-retry"
ENQUEUE_TXID = 10
WORKFLOW_CONFIG = {"local-eid": "dtn://local/", "peer-eid": "dtn://peer/",
                   "policy-id": "policy:1", "receipt-authority": "dtn://issuer/",
                   "bp-lifetime": 3600, "incarnation": "inc:1",
                   "authorization-context": "auth:1"}

# What the host told the caller or the transport before the kill.  Written to
# disk as it happens, so a SIGKILL cannot lose it.
OBSERVED: dict[str, object] = {"receipt_sha256": None, "bpa_deleted": False}


def enqueue_values(txid: int = ENQUEUE_TXID) -> dict[str, object]:
    # ACL2 owns the identity derivation (identity v1, domain-separated): ask
    # the bridge, never re-derive the preimages here.  The old Python twin
    # (plain SHA-256 of the payload) stopped matching the store's binding
    # when the v1 profile landed, and the preflight rightly refused it.
    archive_id, subject_id, _evidence = run_store.metadata(
        CAMPAIGN_MSGID.encode("ascii"), CAMPAIGN_PAYLOAD)
    subject = subject_id.decode("ascii")
    archive = archive_id.decode("ascii")
    return {"txid": txid, "tx-generation": 0, "work-id": "work:campaign",
            "msgid": CAMPAIGN_MSGID, "immutable-subject": subject,
            "archive-obligation-id": archive, "forward-obligation-id": "forward:campaign",
            "peer-eid": "dtn://peer/", "policy-id": "policy:1", "terms-id": "terms:1"}


def _durable_write(path: Path, data: bytes) -> None:
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    try:
        os.write(fd, data)
        os.fsync(fd)
    finally:
        os.close(fd)


def note_receipt(root: Path, receipt: bytes) -> None:
    if not receipt:
        return
    OBSERVED["receipt_sha256"] = hashlib.sha256(receipt).hexdigest()
    _durable_write(root / "observed-receipt.bin", receipt)


def note_delete(root: Path, bid: str) -> None:
    OBSERVED["bpa_deleted"] = True
    _durable_write(root / "observed-bpa-deleted", bid.encode("ascii"))


class PauseAt(run_store.FaultPoints):
    """Report readiness at one named point and block until the parent kills us."""
    __slots__ = ("point", "root", "cut_id", "ready_fd", "control_fd", "fired")

    def __init__(self, point, root, cut_id, ready_fd, control_fd):
        self.point = point
        self.root = root
        self.cut_id = cut_id
        self.ready_fd = ready_fd
        self.control_fd = control_fd
        self.fired = False

    def at(self, point):
        if point != self.point or self.fired:
            return None
        self.fired = True
        _durable_write(self.root / "observed.json",
                       json.dumps({"cut": self.cut_id, **OBSERVED},
                                  sort_keys=True).encode("ascii"))
        os.write(self.ready_fd, ("READY {}\n".format(self.cut_id)).encode("ascii"))
        # The parent kills this process group while this read is blocked, so
        # nothing after the named boundary runs.
        os.read(self.control_fd, 1)
        return None


def bundle_path(root: Path, bid: str) -> Path:
    """Where a case keeps the BPv7 bundle octets the BPA holds for `bid`.

    The receiver settles identity and expiry from the bundle's own primary
    block, so a case must carry the bundle beside the request ADU: the parent
    builds both once per template, and the killed child reads the same file.
    """
    return root / ("bundle-" + hashlib.sha256(
        bid.encode("ascii")).hexdigest()[:16] + ".bp")


def bundle_for(root: Path, bid: str) -> bytes:
    return bundle_path(root, bid).read_bytes()


def _injectors(component: str, pause: PauseAt) -> dict[str, run_store.FaultPoints]:
    table = {name: run_store.NO_FAULTS
             for name in ("store", "workflow", "receipt", "receive")}
    table[component] = pause
    return table


def _receive(root: Path, injectors, bid: str, inventory: dict[str, bytes],
             **extra):
    def delete(found: str) -> None:
        inventory.pop(found, None)
        note_delete(root, found)

    return run_bp_receive.receive_bpa_request(
        store_root=root / "store", inbox_root=root / "inbox",
        receipt_root=root / "receipts", bid=bid,
        inventory=lambda: list(inventory),
        download=lambda found: inventory[found], delete=delete,
        bundle=lambda found: bundle_for(root, found),
        source_eid=SOURCE_EID,
        faults=injectors["receive"], store_faults=injectors["store"],
        inbox_faults=injectors["workflow"], receipt_faults=injectors["receipt"],
        **extra)


def scenario_cross_post(root: Path, injectors) -> str:
    payload = root / "article"
    _durable_write(payload, CAMPAIGN_PAYLOAD)
    code = run_store.command_post(
        SimpleNamespace(store=root / "store", message_id=CAMPAIGN_MSGID,
                        payload=payload, group=list(GROUPS), charge=None,
                        inject_fault=None),
        faults=injectors["store"])
    return "accepted" if code == run_store.EXIT_OK else "refused"


def scenario_receive(root: Path, injectors) -> str:
    request = (root / "request.adu").read_bytes()
    result = _receive(root, injectors, CAMPAIGN_BID, {CAMPAIGN_BID: request})
    return result.outcome


def scenario_workflow(root: Path, injectors) -> str:
    store, bridge, _records = run_store.open_live_store(root / "store", True)
    try:
        replay = Acl2WorkflowReplay(bridge)
        journal = workflow_journal.WorkflowJournal(root / "workflow", replay,
                                                   faults=injectors["workflow"])
        journal.open()
        try:
            journal.persist_enqueue(enqueue_values(), lambda _values: True)
        finally:
            journal.close()
    finally:
        bridge.close()
        store.close()
    return "accepted"


SCENARIOS = {
    "cross-post": scenario_cross_post,
    "bp-receive": scenario_receive,
    "bp-retry": scenario_receive,
    "capacity-refusal": scenario_receive,
    "sender-enqueue": scenario_workflow,
}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scenario", required=True, choices=sorted(SCENARIOS))
    parser.add_argument("--component", required=True)
    parser.add_argument("--point", required=True)
    parser.add_argument("--cut-id", required=True)
    parser.add_argument("--root", required=True)
    parser.add_argument("--ready-fd", required=True, type=int)
    parser.add_argument("--control-fd", required=True, type=int)
    parser.add_argument("--max-transactions", type=int, default=None)
    args = parser.parse_args(argv)
    root = Path(args.root).absolute()
    if args.max_transactions is not None:
        # The bound is ACL2's (the article verdict, `fn-sbud-article-verdict-at`
        # under the persisted profile); the scenario stands in a verdict that
        # refuses after MAX_TRANSACTIONS admissions, to reach the host's
        # refusal path.  ACL2 still answers first; any other word passes.
        admitted = [0]
        original = run_bp_ingress.Acl2BpIngress.article_verdict

        def article_verdict(self, profile, adu):
            verdict = original(self, profile, adu)
            if verdict != "admissible":
                return verdict
            admitted[0] += 1
            return ("admissible" if admitted[0] <= args.max_transactions
                    else "unaffordable")

        run_bp_ingress.Acl2BpIngress.article_verdict = article_verdict

    # Observe the receipt the host regenerates without changing what it does.
    original_receipt = ReceiptJournal.receipt_adu

    def observed_receipt(journal, request_adu):
        receipt = original_receipt(journal, request_adu)
        note_receipt(root, receipt)
        return receipt

    ReceiptJournal.receipt_adu = observed_receipt
    pause = PauseAt(args.point, root, args.cut_id, args.ready_fd, args.control_fd)
    outcome = SCENARIOS[args.scenario](root, _injectors(args.component, pause))
    # Reached only when the cut was never hit; the parent treats a child that
    # completes as a failed cut rather than a passing case.
    _durable_write(root / "completed.json",
                   json.dumps({"outcome": outcome, "cut": args.cut_id,
                               **OBSERVED}, sort_keys=True).encode("ascii"))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except BaseException as error:  # reported through the child's stderr
        print("child {}: {}".format(type(error).__name__, error),
              file=sys.stderr, flush=True)
        raise
