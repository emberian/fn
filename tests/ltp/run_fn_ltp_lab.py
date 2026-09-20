#!/usr/bin/env python3
"""Minimal fn experiment across an actual ION BP-over-LTP link.

Sender-side fn work and the request ADU are produced by ACL2 exactly as in the
pinned TCP laboratory.  The ADU crosses an ION LTP/UDP link between two local
ION nodes, is durably staged by `fn_ltp_stage`, and is then offered to fn's own
`tools/run_bp_receive.py` acceptance.  This is feasibility evidence for one
adapter route; it is not interoperability qualification or a mission profile.
"""
from __future__ import annotations
import argparse, hashlib, json, os, platform, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tests/bp-dtn7"))
sys.path.insert(0, str(HERE))

from ion_bpa import IonLtpSender, IonStagingInbox
from fn_sender_lab import Sender, ARTICLE, CONFIG, create_sender, article_snapshot
from tools import run_store
from tools.run_bp_receive import receive_bpa_request


def wait_for_staged(inbox, deadline_seconds=90):
    deadline = time.monotonic() + deadline_seconds
    while time.monotonic() < deadline:
        names = inbox.inventory()
        if names:
            return names[0]
        time.sleep(0.5)
    raise RuntimeError("no ADU was staged from the LTP link before the deadline")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ion-root", type=Path, default=Path("/tank/fn/ltp"))
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--send-eid", default="ipn:1.1")
    parser.add_argument("--recv-eid", default="ipn:2.1")
    parser.add_argument("--lifetime", type=int, default=300)
    args = parser.parse_args()

    run = args.run.resolve()
    run.mkdir(parents=True, exist_ok=True)
    stage = run / "stage"
    stage.mkdir(exist_ok=True)
    env = dict(os.environ)
    env["PATH"] = f"{args.ion_root}/install/bin:" + env["PATH"]
    env["LD_LIBRARY_PATH"] = f"{args.ion_root}/install/lib:" + env.get("LD_LIBRARY_PATH", "")
    env["ION_NODE_LIST_DIR"] = str(args.ion_root / "run")
    node1 = args.ion_root / "cfg/node1"
    node2 = args.ion_root / "cfg/node2"

    report = {"schema": 1, "status": "running", "run": str(run),
              "ion_prefix": str(args.ion_root / "install"),
              "send_eid": args.send_eid, "recv_eid": args.recv_eid,
              "invocation": [sys.executable, *sys.argv],
              "versions": {"python": sys.version, "platform": platform.platform()},
              "steps": {}}
    steps = report["steps"]
    stager = None
    try:
        create_sender(run / "a-store", run / "source.article")
        run_store.Store(run / "b-store", True).initialize()
        steps["fn_sender_article_published"] = True

        stager = subprocess.Popen(
            ["fn_ltp_stage", args.recv_eid, str(stage), "120", "1"],
            cwd=str(node2), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        time.sleep(2)

        bpa = IonLtpSender(node1, run, args.send_eid, env, args.recv_eid)
        with Sender(run / "a-store", run / "a-workflow") as sender:
            sender.enqueue()
            local_handle, request = sender.submit(
                bpa, txid=11, generation=0, label="request-ltp")
            if not sender.outstanding():
                raise RuntimeError("fn work was not left outstanding after submission")
        steps["fn_request_adu_projected_and_submitted_over_ltp"] = True
        report["request_sha256"] = hashlib.sha256(request).hexdigest()
        report["request_octets"] = len(request)
        report["sender_local_handle"] = local_handle
        report["eid_mapping"] = bpa.submits

        inbox = IonStagingInbox(stage)
        bid = wait_for_staged(inbox)
        staged_bytes = inbox.download(bid)
        report["staged_bid"] = bid
        report["staged_sha256"] = hashlib.sha256(staged_bytes).hexdigest()
        steps["adu_crossed_ltp_link_byte_identical"] = staged_bytes == request
        if staged_bytes != request:
            raise RuntimeError("staged ADU differs from the projected fn request")

        result = receive_bpa_request(
            store_root=run / "b-store", inbox_root=run / "b-inbox",
            receipt_root=run / "b-receipts", bid=bid, source_eid=args.send_eid,
            inventory=inbox.inventory, download=inbox.download, delete=inbox.delete,
            local_policy_authorized=True)
        report["receiver_outcome"] = result.outcome
        report["receipt_sha256"] = hashlib.sha256(result.receipt_adu).hexdigest()
        steps["fn_acceptance_ran_on_ltp_delivered_adu"] = result.outcome == "accepted"
        if result.outcome != "accepted" or not result.receipt_adu:
            raise RuntimeError(f"fn acceptance returned {result.outcome!r}")
        if bid in inbox.inventory():
            raise RuntimeError("staged copy survived the committed receipt decision")
        steps["staged_copy_deleted_only_after_durable_receipt"] = True
        report["receiver_snapshot"] = article_snapshot(run / "b-store")
        report["article_sha256"] = hashlib.sha256(ARTICLE).hexdigest()
        report["status"] = "passed"
    except BaseException as error:
        report.update(status="failed", error=repr(error))
        raise
    finally:
        if stager is not None:
            try:
                out, _ = stager.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                stager.terminate()
                out, _ = stager.communicate(timeout=10)
            report["stager_output"] = out.decode("utf-8", "replace")
        report["not_demonstrated"] = [
            "No receipt was returned over BP: ION gives the sender no transport handle to bind, so the return leg is out of this packet's scope.",
            "Trusted local A_POLICY only; no authenticated peer, author signature or BPSec.",
            "Loopback UDP under LTP; no real space link, delay, asymmetry or contact plan.",
            "Not interoperability qualification and not a mission profile.",
        ]
        (run / "evidence.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"status": report["status"], "evidence": str(run / "evidence.json")}))
    if report["status"] != "passed":
        raise RuntimeError(report.get("error", "fn LTP lab failed"))


if __name__ == "__main__":
    main()
