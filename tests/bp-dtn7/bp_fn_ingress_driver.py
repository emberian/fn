#!/usr/bin/env python3
"""Drive one real BPA bundle through the isolated ACL2 ingress host twice.

The dtn7-rs CLI is used only as the bounded BPA adapter: inventory, a
non-destructive BID download, and the explicit delete callback required by the
existing ingress host.  Article interpretation and Store admission remain in
run_bp_ingress's ACL2 path.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

MAX_BPA_INVENTORY = 8192
MAX_BID_OCTETS = 512
MAX_ADU_BYTES = 4 * 1024 * 1024


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], *, output: Path | None = None) -> str:
    completed = subprocess.run(command, check=True, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, env={**os.environ, "NO_PROXY": "*", "no_proxy": "*"})
    if output is not None:
        output.write_text(completed.stdout + completed.stderr)
    return completed.stdout


def load_ingress(path: Path):
    tools = str(path / "tools")
    if tools not in sys.path:
        sys.path.insert(0, tools)
    import run_bp_ingress
    return run_bp_ingress


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ingress-root", required=True, type=Path)
    parser.add_argument("--workflow-journal", required=True, type=Path)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--journal", required=True, type=Path)
    parser.add_argument("--bpa-bin", required=True, type=Path)
    parser.add_argument("--bpa-port", required=True, type=int)
    parser.add_argument("--bid", required=True)
    parser.add_argument("--expected-adu", required=True, type=Path)
    parser.add_argument("--expected-msgid", required=True)
    parser.add_argument("--destination", required=True)
    parser.add_argument("--source-eid", required=True)
    parser.add_argument("--lifetime", required=True, type=int)
    parser.add_argument("--artifact-dir", required=True, type=Path)
    parser.add_argument("--phase", required=True, choices=("accept", "duplicate"))
    parser.add_argument("--baseline", type=Path,
                        help="accepted-state JSON required for duplicate comparison")
    args = parser.parse_args()

    if len(args.bid.encode("ascii", "strict")) > MAX_BID_OCTETS:
        raise ValueError("BPA BID exceeds lab boundary")
    if not args.expected_adu.is_file():
        raise ValueError("missing legacy ADU input")
    expected = args.expected_adu.read_bytes()
    if not expected or len(expected) > MAX_ADU_BYTES:
        raise ValueError("legacy article ADU exceeds lab boundary")
    ingress = load_ingress(args.ingress_root.resolve())
    # The ingress bridge recovers an existing concrete Store image.  This lab
    # owns only the initial empty-image setup; every subsequent open, recovery,
    # allocation, and acceptance decision is the existing Store/ACL2 path.
    if not args.store.exists():
        ingress.run_store.Store(args.store, writable=True).initialize()
    bpa = args.bpa_bin.resolve()
    args.artifact_dir.mkdir(parents=True, exist_ok=True)

    def inventory() -> list[str]:
        text = run([str(bpa / "dtnquery"), "-6", "-p", str(args.bpa_port), "bundles"])
        begin = text.find("[")
        if begin < 0:
            raise RuntimeError("BPA inventory has no JSON list")
        values = json.loads(text[begin:])
        if (not isinstance(values, list) or len(values) > MAX_BPA_INVENTORY or
                any(not isinstance(value, str) or not value or
                    len(value.encode("ascii", "strict")) > MAX_BID_OCTETS for value in values)):
            raise RuntimeError("BPA inventory violates lab bounds")
        return values

    def download(bid: str) -> bytes:
        # dtnrecv --bid maps to dtn7-rs /download and leaves the BPA copy in
        # inventory.  The ingress journal itself owns durable inbox staging.
        with tempfile.TemporaryDirectory(prefix="fn-bp-download-", dir=args.artifact_dir) as temporary:
            target = Path(temporary) / "download.adu"
            run([str(bpa / "dtnrecv"), "-6", "-p", str(args.bpa_port), "-b", bid,
                 "-o", str(target)])
            value = target.read_bytes()
            if not value or len(value) > MAX_ADU_BYTES:
                raise RuntimeError("BPA download violates ADU lab bound")
            return value

    def delete(bid: str) -> None:
        # The ingress host calls this only after its journal reopen and ACL2
        # durable success/duplicate predicate.  It is intentionally not an
        # endpoint dequeue/pop operation.
        run([str(bpa / "dtnrecv"), "-6", "-p", str(args.bpa_port), "-d", bid])

    def state_snapshot(label: str) -> dict[str, object]:
        store, bridge, records = ingress.open_live_bp_store(args.store, writable=False)
        try:
            payload = bridge.lookup(args.expected_msgid.encode("ascii", "strict"))
            snapshot = {
                "label": label,
                "records": len(records),
                "articles": bridge.article_count(),
                "pins": bridge.pin_count(),
                "payload_sha256": hashlib.sha256(payload).hexdigest(),
                "payload_matches": payload == expected,
            }
        finally:
            bridge.close()
            store.close()
        if snapshot["records"] != 1 or snapshot["articles"] != 1 or not snapshot["payload_matches"]:
            raise RuntimeError(f"unexpected Store state after {label}: {snapshot}")
        return snapshot

    if args.bid not in inventory():
        raise RuntimeError("BPA BID absent before ingress")
    result = ingress.ingest_bpa_adu(
        store_root=args.store, journal_root=args.journal,
        journal_module_path=args.workflow_journal, bid=args.bid,
        inventory=inventory, download=download, delete=delete,
        destination=args.destination, source_eid=args.source_eid, lifetime=args.lifetime)
    expected_outcome = "accepted" if args.phase == "accept" else "duplicate"
    if result.outcome != expected_outcome or args.bid in inventory():
        raise RuntimeError(f"{args.phase} ingress/delete did not complete: {result.outcome}")
    snapshot = state_snapshot(args.phase)
    if args.phase == "duplicate":
        if args.baseline is None or not args.baseline.is_file():
            raise ValueError("duplicate phase requires accepted-state baseline")
        baseline = json.loads(args.baseline.read_text())["state"]
        if {key: snapshot[key] for key in ("records", "articles", "pins", "payload_sha256")} != \
           {key: baseline[key] for key in ("records", "articles", "pins", "payload_sha256")}:
            raise RuntimeError("exact duplicate changed article or retention state")

    report = {
        "schema": 1,
        "phase": args.phase,
        "outcome": result.outcome,
        "bid": args.bid,
        "destination": args.destination,
        "source_eid": args.source_eid,
        "lifetime": args.lifetime,
        "expected_adu_sha256": hashlib.sha256(expected).hexdigest(),
        "ingress_tool_sha256": sha256(args.ingress_root / "tools" / "run_bp_ingress.py"),
        "workflow_journal_sha256": sha256(args.workflow_journal),
        "state": snapshot,
        "endpoint_pop_used": False,
        "receipt_emitted": False,
    }
    (args.artifact_dir / f"fn-ingress-{args.phase}.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
