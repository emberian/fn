"""The native cut campaign as scenarios (design §1, row W7b).

`scenarios()` turns tests/campaign/native_cuts.py's POST_LOG_CUTS into one
scenario each: a prior post, the candidate post with a `kill` fault at the
cut's boundary, the image's scan, recovery, reads of both, the candidate's
retry; the cut's candidate column is the crash rule at that boundary (the
registry carries it; native_cuts.verify_post_log_cut_map checks it against
the model program).  `run()` performs the same process calls
tests/test_native_crash_model.py's NativeCampaignMixin makes, but records
what the client saw, what the environment did and what the image's own scan
says into a journal written OUTSIDE the store, and the verdict is
`checker.check`'s.

    python3 -m tools.resilience.adapters.native_cuts --image build/fn-host-developer \
        [--cut NAME] [--out DIR] [--no-fault]

`--no-fault` runs the scenario with the fault hook disabled: the tester's
own test on the box (the verdict must be harness-failure:fault-never-occurred).
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tests.campaign import native_cuts  # noqa: E402
from tests import native_log_observation  # noqa: E402
from tools.resilience.scenario import Scenario, Operation, Fault, check as check_scenario  # noqa: E402
from tools.resilience.journal import Journal  # noqa: E402
from tools.resilience import checker  # noqa: E402

GROUP = "fn.letters"
PRIOR = "post-prior"
CANDIDATE = "post-candidate"


def scenario_for(cut) -> Scenario:
    return check_scenario(Scenario(
        id="native-cut-" + cut.name,
        title="store post killed at {} ({}): the candidate's fate and its retry".format(
            cut.name, cut.program),
        requirements=["STO-002", "OBJ-005"],
        contract="local-commit-log",
        initial={"recipe": "empty-store", "groups": [GROUP], "prior": []},
        actors=[{"name": "client", "kind": "client"}, {"name": "nemesis", "kind": "nemesis"}],
        operations=[
            Operation(PRIOR, "client", "post", {"groups": [GROUP], "payload": "prior"}),
            Operation(CANDIDATE, "client", "post", {"groups": [GROUP], "payload": "candidate"}),
            Operation("recover", "client", "recover"),
            Operation("read-prior", "client", "read", {"article": PRIOR}),
            Operation("read-candidate", "client", "read", {"article": CANDIDATE}),
            Operation("retry-candidate", "client", "retry", {"of": CANDIDATE}),
        ],
        faults=[Fault(CANDIDATE, cut.name, "kill", "contract-admissible", "persisted")],
        healing=["recover", "read-prior", "read-candidate", "retry-candidate"],
        witnesses=["post-accepted", "retry-reconciled", "read-completed"],
        replay="exact"))


def scenarios() -> list:
    return [scenario_for(cut) for cut in native_cuts.POST_LOG_CUTS]


def _invoke(image, store, command, *arguments, env=None, cwd=ROOT):
    host_env = dict(os.environ)
    for k in ("FN_NATIVE_POST_FAULT", "FN_NATIVE_LOG_FAULT", "FN_NATIVE_RECOVERY_FAULT"):
        host_env.pop(k, None)
    host_env.update(env or {})
    return subprocess.run([str(image), "--fn", "store", str(store), command, *map(str, arguments)],
                          cwd=cwd, env=host_env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=False)


def _reply_outcome(result) -> str:
    if result.returncode == -9:
        return "lost"
    if result.returncode == 0 and (b"committed sequence=" in result.stdout
                                   or b"duplicate" in result.stdout):
        return "duplicate" if b"duplicate" in result.stdout else "accepted"
    return "refused"


def run(scenario: Scenario, image: Path, work: Path, fault_hook: bool = True) -> tuple:
    """Run SCENARIO on IMAGE under WORK; (journal, verdict).  The journal is
    WORK/journal.jsonl, beside the store, never inside it."""
    work = Path(work)
    store = work / "store"
    j = Journal(scenario.id)
    fault = scenario.faults[0]
    payloads = {}
    for o in scenario.posts():
        p = work / (o.id + ".payload")
        p.write_bytes(("{} protected content".format(o.args["payload"])).encode())
        payloads[o.id] = p
        j.bind(o.id, "<{}@resilience.invalid>".format(o.id))
    mid = lambda op_id: "<{}@resilience.invalid>".format(op_id)  # noqa: E731
    j.stage("workload", "begun")
    init = _invoke(image, store, "init", *scenario.initial["groups"])
    if init.returncode != 0:
        j.stage("workload", "ended")
        j.write(work / "journal.jsonl")
        return j, checker.harness_failure(scenario, j, "init-failed")
    for o in scenario.operations:
        if o.op != "post":
            continue
        env = {}
        if o.id == fault.operation and fault_hook:
            env["FN_NATIVE_POST_FAULT"] = "{}:{}".format(fault.boundary, fault.action)
        r = _invoke(image, store, "post", mid(o.id), payloads[o.id], "-", "-",
                    *o.args["groups"], env=env)
        outcome = _reply_outcome(r)
        j.client("reply", operation=o.id, outcome=outcome, returncode=r.returncode)
        if o.id == fault.operation and r.returncode == -9:
            j.environment("fault-fired", operation=o.id, boundary=fault.boundary,
                          action=fault.action, evidence="returncode=-9")
    scan = native_log_observation.committed_history(image, store, cwd=ROOT)
    j.environment("persisted-records", count=len(scan), last=scan.last,
                  source="log scan-store")
    j.stage("workload", "ended")
    j.stage("healing", "begun")
    for o in scenario.operations:
        if o.op == "recover":
            r = _invoke(image, store, "recover")
            j.client("recover", operation=o.id,
                     outcome="completed" if r.returncode == 0 and b"articles=" in r.stdout
                     else "failed")
            after = native_log_observation.committed_history(image, store, cwd=ROOT)
            j.environment("persisted-records", count=len(after), last=after.last,
                          source="log scan-store")
        elif o.op == "read":
            art = o.args["article"]
            r = _invoke(image, store, "inspect", mid(art))
            if r.returncode == 0:
                result = "match" if r.stdout == payloads[art].read_bytes() else "other"
            else:
                result = "absent"
            j.client("read", operation=o.id, article=art, result=result)
        elif o.op == "retry":
            of = o.args["of"]
            r = _invoke(image, store, "post", mid(of), payloads[of], "-", "-",
                        *scenario.operation(of).args["groups"])
            j.client("reply", operation=o.id, outcome=_reply_outcome(r), returncode=r.returncode)
    final = native_log_observation.committed_history(image, store, cwd=ROOT)
    j.environment("persisted-records", count=len(final), last=final.last, source="log scan-store")
    j.stage("healing", "ended")
    path = j.write(work / "journal.jsonl")
    reread = Journal.read(path)          # the verdict is over the journal as stored
    verdict = checker.check(scenario, reread)
    (work / "verdict.json").write_text(json.dumps(verdict.to_json(), indent=1, sort_keys=True))
    return reread, verdict


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--image", required=True)
    ap.add_argument("--cut")
    ap.add_argument("--out")
    ap.add_argument("--no-fault", action="store_true")
    a = ap.parse_args(argv)
    image = Path(a.image)
    if not (image.is_file() and os.access(image, os.X_OK)):
        print("not an executable image: " + str(image)); return 2
    out = Path(a.out) if a.out else Path(tempfile.mkdtemp(prefix="fn-resilience-"))
    worst = 0
    for s in scenarios():
        if a.cut and s.id != "native-cut-" + a.cut:
            continue
        work = out / s.id
        work.mkdir(parents=True, exist_ok=True)
        s.dump(work / "scenario.json")
        _, v = run(s, image, work, fault_hook=not a.no_fault)
        print("{} {} {} witnesses={} pending={}".format(
            s.id, v.kind, v.cause or "", ",".join(v.witnesses_observed) or "-",
            ",".join(v.pending_rules) or "-"))
        if not v.green:
            worst = max(worst, 1)
    print("journals under " + str(out))
    return worst


if __name__ == "__main__":
    raise SystemExit(main())
