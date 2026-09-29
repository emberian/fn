"""power_loss as a backend (design §10 row W7d, first increment): the block
replay rig's records as IR scenarios and journals, judged WHOLE-HISTORY by
the checker instead of per article.

The rig (tools/power_loss.py; dm-log-writes over the node's file system on
hbox) writes one record per crash image to `cuts-full.jsonl`: the cut
position, the mode (flush: every completed write through the cut; prefix: a
prefix of the unflushed writes; subset: a random subset of them; torn: a
torn block), the seed, the acknowledged and refused POSTs before the cut,
what the recovered store served for every attempted article (its
`classify`: the reference bytes, the reclaimed reference, 430, other), the
binding checks (the newest acknowledged Message-ID posted again with other
bytes; a fresh article's number above every served number), and for a
`recover-crash` record the second cut during the first recovery.  This
adapter does not run the rig (the convergence checklist runs it once); it
turns each record into

  scenario   `power-loss-<phase>-<cut>` (replay `image`: cut, mode and seed
             rebuild the image): the acknowledged posts, the refused ones,
             the attempted-but-unanswered ones (lost replies), the crash at
             the write boundary (fault `drop-writes` at `power-loss`), the
             recovery (and, for recover-crash, a second `drop-writes` at
             `recovery-power-loss` during it), the reads, the bindings;
  journal    the client history (replies in acknowledgement order, the
             recoveries, the served counts, the repost and the fresh post)
             and the environment facts (`persisted-write-selection` per
             cut: mode, cut, durable_upto, tail, kept, e2fsck; the fault
             fired; `persisted-records` from the recovery's own report).

The checker composes them: every acknowledged post is committed (its 240
was durable), the committed unacknowledged ones are a PREFIX of the open
batch in log order (`power-loss-prefix`: the store-log crash theorem, the
recovery truncating at the first incomplete record), the served count is
exactly the committed count and no article is served with other bytes
(`committed-serves-exact`), the repost with other bytes is refused by name
(`identity-is-the-bytes`), the fresh number is above every served one
(`number-stability`).  The rig's control records (a POST judged acknowledged
whose writes all follow the cut) are the tooth: their expected verdict is
`violation`.  Per-article outcomes (`per`, written by the rig's classify
from the next run on) become individual `read` records; until then the
counts are one `served-counts` observation, and the verdict says so.

Over the 2026-09-26 evidence (236 images): every cut record is consistent
with one history and the six controls are violations, EXCEPT six init-phase
cuts (169, 187, 200, 222, 234, 236) the rig footnoted as a constraint
(planning/evidence/power-loss-2026-09-26.md, "Constraint"): a cut inside
`operator init` left a store directory that neither recovers (missing
staging directory, config.json or allocation frontier) nor re-initializes
(STORE-EXISTS).  The checker judges them: init is not old-or-new
(`recovery-keeps-history`); the operator is stuck.  Reported, not hidden.

    python3 -m tools.resilience.adapters.power_loss RECORDS.jsonl [--out DIR]
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.resilience.scenario import Scenario, Operation, Fault, check as check_scenario  # noqa: E402
from tools.resilience.journal import Journal  # noqa: E402
from tools.resilience import checker  # noqa: E402

BOUNDARY = "power-loss"
RECOVERY_BOUNDARY = "recovery-power-loss"
GROUP = "fn.test"
EVIDENCE = ROOT / "planning/evidence/power-loss-2026-09-26/full/cuts-full.jsonl"
RECOVERED = re.compile(r"recovered transactions=(\d+) articles=(\d+)")
PHASE_OP = {"checkpoint": "checkpoint", "compact": "reclaim", "reclaim": "reclaim",
            "retention": "reclaim", "reference-reclaimed": "probe", "reference": "probe",
            "end": "probe", "export": "probe", "import": "probe", "init": "probe"}
CONTROL_PHASES = ("control", "stmtcontrol")


def records(path=EVIDENCE) -> list:
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def attempted(rec: dict) -> int:
    return sum(rec.get(k, 0) for k in ("served_ref", "served_reclaimed", "absent", "other"))


def scenario_for(rec: dict) -> Scenario:
    phase = rec.get("first_phase", rec["phase"])
    acked, refused = rec.get("acked", 0), rec.get("refused", 0)
    n = max(attempted(rec), acked + refused)
    ops = [Operation("post-{}".format(i), "client", "post",
                     {"groups": [GROUP], "payload": "article {}".format(i)})
           for i in range(1, n + 1)]
    kind = PHASE_OP.get(phase, "post")
    if kind == "post":
        subject = ops[-1].id if ops else None
        if subject is None:
            ops.append(Operation("probe-cut", "client", "probe"))
            subject = "probe-cut"
    else:
        ops.append(Operation(kind + "-cut", "client", kind))
        subject = kind + "-cut"
    faults = [Fault(subject, BOUNDARY, "drop-writes", "contract-admissible", "persisted",
                    "served-post")]
    healing = []
    if rec.get("second"):
        ops.append(Operation("recover-first", "client", "recover"))
        faults.append(Fault("recover-first", RECOVERY_BOUNDARY, "drop-writes",
                            "contract-admissible", "persisted", "served-post"))
        healing.append("recover-first")
    ops.append(Operation("recover", "client", "recover"))
    healing.append("recover")
    ops.append(Operation("reads", "client", "read", {"article": ops[0].id if ops and ops[0].op == "post" else subject}))
    healing.append("reads")
    if rec.get("binding"):
        if acked:
            ops.append(Operation("repost", "client", "retry",
                                 {"of": "post-{}".format(acked), "route": "served-post",
                                  "bytes": "other"}))
            healing.append("repost")
        # The fresh post after recovery is the binding probe (its number
        # above every served one), not a fated post of the crashed history.
        ops.append(Operation("fresh", "client", "probe", {"what": "fresh-post"}))
        healing.append("fresh")
    if phase == "init" and not acked:
        # The cut fell in the store's initialization: the positive witness
        # is the old state (no store) re-initialized, not a recovery.
        witnesses = ["init-old-or-new"]
    else:
        witnesses = ["recovery-completed"] + (["post-accepted"] if acked else [])
    return check_scenario(Scenario(
        id="power-loss-{}-{}".format(rec["phase"], rec["cut"]),
        title="power cut at write {} ({} mode) during {}: {} acknowledged, {} refused, {} "
              "attempted; the recovered store serves exactly the committed history".format(
                  rec["cut"], rec["mode"], phase, acked, refused, n),
        requirements=["STO-002", "OBJ-005"], contract="local-commit-log",
        initial={"recipe": "block-replay", "groups": [GROUP], "prior": []},
        actors=[{"name": "client", "kind": "client"}, {"name": "device", "kind": "nemesis"}],
        operations=ops, faults=faults, healing=healing, witnesses=witnesses,
        healing_bound=None, replay="image",
        expected="violation" if rec["phase"] in CONTROL_PHASES else "consistent"))


def selection(rec: dict, second: bool = False) -> dict:
    if second:
        s = rec["second"]
        return {"mode": s["mode2"], "cut": s["cut2"], "durable_upto": s["durable_upto2"],
                "tail": s.get("tail2"), "kept": s.get("kept2"), "seed": s.get("seed2"),
                "writes": s.get("second_writes")}
    return {"mode": rec["mode"], "cut": rec["cut"], "durable_upto": rec.get("durable_upto"),
            "tail": rec.get("tail"), "kept": rec.get("kept"), "seed": rec.get("seed"),
            "e2fsck": rec.get("e2fsck")}


def _recover_outcome(code, text) -> tuple:
    m = RECOVERED.search(text or "")
    if code == 0 and m:
        return "completed", int(m.group(2))
    return ("failed" if code else "completed"), None


def journal_for(rec: dict, s: Scenario) -> Journal:
    j = Journal(s.id)
    acked, refused = rec.get("acked", 0), rec.get("refused", 0)
    posts = [o for o in s.operations if o.op == "post" and o.id != "fresh"]
    j.stage("workload", "begun")
    for i, o in enumerate(posts, 1):
        outcome = "accepted" if i <= acked else "refused" if i <= acked + refused else "lost"
        j.client("reply", operation=o.id, outcome=outcome, route="served-post")
    fault = s.faults[0]
    sel = selection(rec)
    j.environment("persisted-write-selection", operation=fault.operation, boundary=BOUNDARY,
                  open=[o.id for o in posts[acked + refused:]], **sel)
    j.environment("fault-fired", operation=fault.operation, boundary=BOUNDARY,
                  action="drop-writes", route=fault.route,
                  evidence="cut={} mode={} durable_upto={}".format(
                      sel["cut"], sel["mode"], sel["durable_upto"]))
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    if rec.get("second"):
        code, text = rec["second"].get("recover1", [None, ""])
        outcome, _ = _recover_outcome(code, text)
        j.client("recover", operation="recover-first", outcome=outcome, phase="killed",
                 returncode=code)
        sel2 = selection(rec, second=True)
        j.environment("persisted-write-selection", operation="recover-first",
                      boundary=RECOVERY_BOUNDARY, open=[], **sel2)
        j.environment("fault-fired", operation="recover-first", boundary=RECOVERY_BOUNDARY,
                      action="drop-writes", route="served-post",
                      evidence="cut2={} mode2={} of {} recovery writes".format(
                          sel2["cut"], sel2["mode"], sel2["writes"]))
    phase = rec.get("first_phase", rec["phase"])
    outcome, articles = _recover_outcome(rec.get("recover"), rec.get("recover_out"))
    if "NO-STORE" in str(rec.get("recover_out", "")):
        outcome = "no-store"        # the cut preceded a durable init (the old state)
    j.client("recover", operation="recover", outcome=outcome, phase="healing",
             returncode=rec.get("recover"), reinit=rec.get("reinit"),
             init_phase=(phase == "init"))
    phase = rec.get("first_phase", rec["phase"])
    if articles is not None and phase in ("post", "checkpoint", "init", "control"):
        j.environment("persisted-records", count=articles, phase="after-recovery",
                      source="operator recover (articles=)")
    per = rec.get("per")
    if per:
        for i, what in per:
            o = posts[i]
            j.client("read", operation="reads", article=o.id,
                     result={"ref": "match", "reclaimed": "match", "absent": "absent"}.get(
                         what, "other"), route="served")
    else:
        j.client("served-counts", operation="reads", attempted=len(posts),
                 served=rec.get("served_ref", 0) + rec.get("served_reclaimed", 0),
                 absent=rec.get("absent", 0), other=rec.get("other", 0),
                 route="served", granularity="counts")
    b = rec.get("binding") or {}
    if b and acked:
        repost = str(b.get("repost", ""))
        outcome = ("refused" if repost.startswith("441") else
                   "accepted" if repost.startswith("240") else "lost")
        j.client("reply", operation="repost", outcome=outcome, route="served-post",
                 status=repost, cross_route=True)
    if b:
        fresh = str(b.get("fresh", ""))
        j.client("numbers", operation="fresh", fresh=fresh,
                 fresh_number=b.get("fresh_number") if fresh.startswith("240") else None,
                 max_served=b.get("max_served"), listed=b.get("listed"))
    j.stage("healing", "ended", elapsed=0.0)
    return j


def check_record(rec: dict) -> tuple:
    s = scenario_for(rec)
    j = journal_for(rec, s)
    return s, j, checker.check(s, j)


def summary(path=EVIDENCE) -> dict:
    """Verdict counts over the rig's records, controls apart, and the
    records whose verdict is not the expected one."""
    kinds = collections.Counter()
    unexpected = []
    for rec in records(path):
        s, j, v = check_record(rec)
        kinds[(rec["phase"] in CONTROL_PHASES, v.kind)] += 1
        if v.kind != s.expected:
            unexpected.append((s.id, v.kind, v.cause, (v.explanation or {}).get("rules")))
    return {"kinds": {"{}:{}".format("control" if c else "cut", k): n
                      for (c, k), n in sorted(kinds.items())},
            "unexpected": unexpected}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("records", nargs="?", default=str(EVIDENCE))
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    if a.out:
        out = Path(a.out)
        out.mkdir(parents=True, exist_ok=True)
        for rec in records(a.records):
            s, j, v = check_record(rec)
            (out / (s.id + ".scenario.json")).write_text(json.dumps(s.to_json(), indent=1))
            j.write(out / (s.id + ".journal.jsonl"))
            (out / (s.id + ".verdict.json")).write_text(json.dumps(v.to_json(), indent=1))
    result = summary(a.records)
    for k, n in result["kinds"].items():
        print("{:<28} {}".format(k, n))
    for row in result["unexpected"]:
        print("UNEXPECTED " + " ".join(str(x) for x in row))
    return 1 if result["unexpected"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
