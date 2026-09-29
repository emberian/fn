"""Bounded IR against actual ACL2 response-owner and arena pin transitions.

Model evidence only. The separate contract interpreter judges observations;
this does not run the native worker, release sectors, or prove composition.
"""
from pathlib import Path
import argparse
import json
import subprocess
import time

from tools import acl2_slots, run_simulator
from tools.resilience import checker, contract
from tools.resilience.journal import Journal
from tools.resilience.scenario import Scenario, Operation, Fault, check as validate

ROOT = Path(__file__).resolve().parents[3]
VIEW = ("g", "h", "q", "p", "r", "a")
KINDS = {"acquire-hold": ":ACQUIRE", "release-hold": ":RELEASE",
         "begin-compaction": ":RETIRE", "reclaim": ":REAP"}


def example():
    operations = [Operation("acquire-0", "core", "acquire-hold", {"owner": 0}),
        Operation("acquire-1", "core", "acquire-hold", {"owner": 1}),
        Operation("retire", "core", "begin-compaction"),
        Operation("release-0", "core", "release-hold", {"owner": 0}),
        Operation("blocked-reap", "core", "reclaim"),
        Operation("duplicate-release-0", "core", "release-hold", {"owner": 0}),
        Operation("release-1", "core", "release-hold", {"owner": 1}),
        Operation("productive-reap", "core", "reclaim")]
    return validate(Scenario("model-two-independent-response-holds",
        "One response settling does not release another's held retirement",
        "response-holds-model", {"recipe": "response-holds-model-empty", "prior": []},
        [{"name": "core", "kind": "client"}], operations,
        [Fault("duplicate-release-0", "model-response-release", "deliver-stale-completion",
               "contract-admissible", "observed")],
        [o.id for o in operations[6:]],
        ["two-model-holds", "one-model-hold-blocks", "model-retirement-released", "model-settled"],
        requirements=["HST-023"], replay="exact",
        healing_bound={"kind": "experimental", "value": 120,
                       "source": "model runner budget, not served latency"}))


def driver(scenario):
    validate(scenario)
    if scenario.contract != "response-holds-model" or scenario.initial != example().initial:
        raise ValueError("unsupported response model initial state")
    ids = [o.id for o in scenario.operations]
    if not scenario.healing or ids[-len(scenario.healing):] != scenario.healing:
        raise ValueError("response model healing must be a nonempty suffix")
    steps = " ".join(f'({KINDS[o.op]} {o.args.get("owner", 0)})' for o in scenario.operations)
    return f'''(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(ld "books/response-plan-pins.lisp" :ld-error-action :return :ld-error-triples t)
(defun fn-rsim-run (steps owners st i)
 (declare (xargs :mode :program))
 (if (atom steps) (cw "FN_SIM_RESULT s=response-holds-model r=passed~%")
  (let* ((event (car steps)) (kind (car event)) (id (cadr event)))
   (mv-let (next-owners next answer released)
    (if (member-eq kind '(:acquire :release))
      (mv-let (os ns ans) (fn-rpin-step owners st (list kind id)) (mv os ns ans 0))
     (mv-let (ns ans) (fn-arpn-step st (if (equal kind :retire) '(:retire (0)) '(:release)))
       (mv owners ns (if (equal kind :retire) ans (len ans))
                      (if (equal kind :retire) 0 (len ans)))))
    (prog2$ (cw "FN_SIM_TRACE s=response-holds-model k=0 i=~x0 t=~x1 o=~x2 g=~x3 h=~x4 q=~x5 p=~x6 r=~x7 a=~x8~%"
       i kind id (first next) (fn-arpn-count (second next))
       (+ (if (fn-rpin-owner 0 next-owners) 1 0) (if (fn-rpin-owner 1 next-owners) 2 0))
       (len (third next)) released answer)
      (fn-rsim-run (cdr steps) next-owners next (+ 1 i)))))))
(value-triple (prog2$ (cw "FN_SIM_PLAN s=response-holds-model k=0 n={len(scenario.operations)}~%")
 (fn-rsim-run '({steps}) nil (fn-arpn-initial) 0)))
(quit)
'''


def observe(scenario, output, status, elapsed):
    j = Journal(scenario.id)
    try:
        traces = run_simulator.parse_records(output, run_simulator.TRACE_PREFIX)
        plans = run_simulator.parse_records(output, run_simulator.PLAN_PREFIX)
        results = run_simulator.parse_records(output, run_simulator.RESULT_PREFIX)
    except ValueError as error:
        return j, checker.harness_failure(scenario, j, "malformed-response-model:" + str(error))
    if (status != 0 or plans != [dict(s="response-holds-model", k="0", n=str(len(scenario.operations)))]
        or results != [dict(s="response-holds-model", r="passed")]
        or [(r.get("k"), r.get("i")) for r in traces] != [("0", str(i)) for i in range(len(scenario.operations))]):
        return j, checker.harness_failure(scenario, j, "response-model-driver-incomplete")
    j.stage("workload", "begun")
    healing = False
    state = dict(generation=0, owners={}, pending=[], released=0, answer="-")
    for op, row in zip(scenario.operations, traces):
        if row.get("s") != "response-holds-model" or row.get("t") != KINDS[op.op] or row.get("o") != str(op.args.get("owner", 0)) or any(k not in row for k in VIEW):
            return j, checker.harness_failure(scenario, j, "response-model-operation-not-executed:" + op.id)
        if op.id in scenario.healing and not healing:
            j.stage("workload", "ended")
            j.stage("healing", "begun")
            healing = True
        j.client("response-model-step", operation=op.id, **{k: row[k] for k in VIEW})
        state = contract.response_holds_model_step(state, op)
        j.internal("response-model-oracle", operation=op.id, **contract.response_holds_model_view(state))
        for fault in scenario.faults:
            if fault.operation == op.id:
                if op.op != "release-hold" or row["a"] != ":ABSENT":
                    return j, checker.harness_failure(scenario, j, "response-model-fault-never-occurred")
                j.environment("fault-fired", operation=op.id, boundary=fault.boundary,
                              action=fault.action, owner=op.args["owner"], observed=row["a"])
    j.environment("response-model-terminal", **{k: traces[-1][k] for k in VIEW})
    j.stage("healing", "ended", elapsed=elapsed)
    return j, checker.check(scenario, j)


def execute(scenario, out, timeout=120):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    source = driver(scenario)
    (out / "driver.lsp").write_text(source)
    (out / "scenario.json").write_text(json.dumps(scenario.to_json(), indent=2) + "\n")
    launcher = run_simulator.executable()
    start = time.monotonic()
    output, status = "ACL2 unavailable", 2
    if launcher:
        try:
            result = acl2_slots.run([str(launcher)], "resilience response-holds-model", cwd=ROOT,
                input=source.encode(), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=timeout, check=False)
            output, status = result.stdout.decode(errors="replace"), result.returncode
        except subprocess.TimeoutExpired as error:
            output, status = (error.stdout or b"").decode(errors="replace"), "timed-out"
    elapsed = time.monotonic() - start
    (out / "acl2.log").write_text(output)
    j, verdict = observe(scenario, output, status, elapsed)
    j.write(out / "journal.jsonl")
    (out / "verdict.json").write_text(json.dumps(verdict.to_json(), indent=2) + "\n")
    inputs = ["books/response-plan-pins.lisp", "books/arena-reader-pins.lisp",
              "tools/resilience/adapters/response_holds.py", "tools/resilience/contract.py",
              "tools/resilience/checker.py", "tools/resilience/scenario.py", "tools/run_simulator.py"]
    (out / "manifest.json").write_text(json.dumps(dict(status=verdict.kind, exit_code=status,
        source_revision=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        elapsed=elapsed, scope="ACL2 response-owner/arena model; not native I/O or certification",
        inputs={p: run_simulator.digest(ROOT / p) for p in inputs},
        launcher=str(launcher), launcher_sha256=run_simulator.digest(launcher) if launcher else None,
        scenario_sha256=run_simulator.digest(out / "scenario.json"), driver_sha256=run_simulator.digest(out / "driver.lsp")), indent=2) + "\n")
    return verdict


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    scenario = Scenario.from_json(json.loads(args.scenario.read_text())) if args.scenario else example()
    verdict = execute(scenario, args.out)
    print(f"{scenario.id}: {verdict.kind} ({verdict.cause or 'model scope'})")
    raise SystemExit(0 if verdict.green else 1)


if __name__ == "__main__":
    main()
