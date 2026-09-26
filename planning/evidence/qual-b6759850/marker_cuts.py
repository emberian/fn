#!/usr/bin/env python3
"""qual-b6759850: the five committed-history marker cuts through both entries.

For each cut in ACL2's fn-hm-marker-cut-names (tests/test_native_history_marker
MARKER_CUTS), each action (kill, eio) and each entry (`store ROOT post`, and
`operator CFG post` to an owner started with the selector), on the developer
image: seed one article through the owner, post the candidate under
FN_NATIVE_POST_FAULT=<cut>:<action>, then recover, resubmit the candidate
through the same entry (no fault), post a third article, and delete the newest
transaction file: the open must refuse `history-short-of-marker`.
Reuses the campaign's Node/seed helpers unchanged.  A lane driver; it changes
nothing in the tree.  Usage: marker_cuts.py DEV_IMAGE WORK OUT.json
"""
import json, sys
from pathlib import Path
from tests.campaign.native_operator_campaign import (
    Node, seed, snapshot, article, public, PRIOR_ID, CANDIDATE_ID)
from tests.test_native_history_marker import MARKER_CUTS

dev, work, out = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
work.mkdir(parents=True, exist_ok=True)
prior = work / "prior.art"; prior.write_bytes(article(PRIOR_ID, "prior", "prior content"))
cand = work / "candidate.art"; cand.write_bytes(article(CANDIDATE_ID, "candidate", "candidate content"))
third = work / "third.art"; third.write_bytes(article("<third@campaign.invalid>", "third", "third content"))
rows = []


def submit(node, entry, payload, msgid, extra=None):
    if entry == "store":
        return {"post": public(node.store_post(msgid, payload, extra))}
    owner = node.start_owner(extra)
    r = {"owner_ready": owner["ready"], "post": public(node.post(msgid, payload))}
    r["owner_alive_after_post"] = owner["proc"].poll() is None
    r["owner"] = node.stop_owner(owner)
    return r


for cut in MARKER_CUTS:
    for action in ("kill", "eio"):
        for entry in ("store", "operator"):
            name = "{}-{}-{}".format(cut, action, entry)
            node = Node(dev, work, name)
            row = {"cut": cut, "action": action, "entry": entry}
            try:
                seed(node, prior, row)
                row["faulted"] = submit(node, entry, cand, CANDIDATE_ID,
                                        {"FN_NATIVE_POST_FAULT": "{}:{}".format(cut, action)})
                row["after_fault"] = snapshot(node.store)
                row["tx_after_fault"] = len(row["after_fault"]["transactions"])
                row["marker_after_fault"] = (node.store / "committed-history.json").read_text("ascii", "replace") \
                    if (node.store / "committed-history.json").is_file() else None
                row["recover"] = public(node.run(["store", str(node.store), "recover"]))
                row["resubmit"] = submit(node, entry, cand, CANDIDATE_ID)
                row["third"] = public(node.store_post("<third@campaign.invalid>", third))
                txs = sorted((node.store / "transactions").iterdir())
                row["tx_before_loss"] = len(txs)
                txs[-1].unlink()
                row["lost_open"] = public(node.run(["store", str(node.store), "recover"]))
                rc = row["lost_open"]["rc"]
                err = row["lost_open"]["stderr"]
                n = row["tx_before_loss"]
                rs = row["resubmit"]["post"]
                dup = rs["rc"] == 0 and ("DUPLICATE" in rs["stderr"] or rs["stdout"] == "duplicate\n")
                row["checks"] = {
                    "record_durable": row["tx_after_fault"] == 2,
                    "fault_rc": row["faulted"]["post"]["rc"],
                    "recover_rc0": row["recover"]["rc"] == 0,
                    "resubmit_duplicate": dup,
                    "third_committed": row["third"]["rc"] == 0,
                    "lost_refused": rc == 4 and "history-short-of-marker" in err
                                    and "marker={} records={}".format(n, n - 1) in err,
                }
                c = row["checks"]
                row["pass"] = all(c[k] for k in ("record_durable", "recover_rc0", "resubmit_duplicate",
                                                 "third_committed", "lost_refused"))
            except Exception as e:  # recorded, never hidden
                row["error"] = repr(e); row["pass"] = False
            finally:
                node.reap()
            rows.append(row)
            print("{} {} fault_rc={} tx={} recover={} resubmit_dup={} third={} lost_refused={}".format(
                "PASS" if row["pass"] else "FAIL", name, row.get("checks", {}).get("fault_rc"),
                row.get("tx_after_fault"), row.get("recover", {}).get("rc"),
                row.get("checks", {}).get("resubmit_duplicate"), row.get("third", {}).get("rc"),
                row.get("checks", {}).get("lost_refused")), flush=True)
out.write_text(json.dumps(rows, indent=1, default=str))
print("marker cuts: {}/{} pass".format(sum(r["pass"] for r in rows), len(rows)))
sys.exit(0 if all(r["pass"] for r in rows) else 1)
