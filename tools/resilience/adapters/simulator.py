"""Execute bounded acceptance-model IR against ACL2 and journal its observations.

This backend exercises logical acceptance, not sockets, storage or page I/O.
It deliberately uses model-* operations; native lifecycle scenarios cannot
silently acquire a simulator verdict. Independent ACL2 oracle records and the
Python contract checker judge each transition. Healing is an actual suffix of
the supplied operations, and terminal logical pending ownership is observed.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import time

from tools import acl2_slots, run_simulator
from tools.resilience import checker
from tools.resilience.journal import Journal
from tools.resilience.scenario import Scenario, Operation, Fault, check as validate

ROOT = Path(__file__).resolve().parents[3]
KINDS = {"model-prepare": ":PREPARE", "model-complete": ":COMPLETE",
         "model-recover": ":RECOVER"}
VIEW = ("a", "p", "f", "q")


def example() -> Scenario:
    def op(name, kind, identity, generation=7, result=None):
        args = dict(identity=identity, generation=generation)
        if result:
            args["result"] = result
        return Operation(name, "core", "model-" + kind, args)
    operations = [op("prepare-A", "prepare", "A"),
                  op("durable-A", "complete", "A", result="durable"),
                  op("prepare-B", "prepare", "B"),
                  op("stale-B", "complete", "B", 8, "durable"),
                  op("uncertain-B", "complete", "B", result="indeterminate"),
                  op("stale-recovery-B", "recover", "B", 8, "committed"),
                  op("resolve-B", "recover", "B", result="absent"),
                  op("repeat-B", "recover", "B", result="absent"),
                  op("retry-B", "prepare", "B"),
                  op("durable-B", "complete", "B", result="durable")]
    faults = [Fault("stale-B", "model-completion-delivery", "deliver-stale-completion",
                    "contract-admissible", "observed"),
              Fault("uncertain-B", "model-completion-delivery", "report-error",
                    "contract-admissible", "observed"),
              Fault("stale-recovery-B", "model-completion-delivery", "deliver-stale-completion",
                    "contract-admissible", "observed")]
    return validate(Scenario(
        "model-stale-uncertain-recovery", "Stale delivery, uncertainty, recovery and productive retry",
        "acceptance-model", {"recipe": "acceptance-model-empty", "prior": []},
        [{"name": "core", "kind": "client"}], operations, faults,
        [o.id for o in operations[6:]], ["model-prepared", "model-published", "model-settled"],
        requirements=["STO-002"], replay="exact",
        healing_bound={"kind": "experimental", "value": 120,
                       "source": "model runner wall budget, not a served latency claim"}))


def driver(scenario: Scenario) -> str:
    validate(scenario)
    if scenario.contract != "acceptance-model":
        raise ValueError("simulator accepts only acceptance-model IR")
    ids = [o.id for o in scenario.operations]
    if not scenario.healing or ids[-len(scenario.healing):] != scenario.healing:
        raise ValueError("model healing must be a nonempty operation suffix")
    steps = []
    for o in scenario.operations:
        a = o.args
        result = " :" + a["result"].upper() if "result" in a else ""
        # Identity is validated A/B, generation a natural, result a named atom.
        # No scenario text is passed to the Lisp reader as executable input.
        steps.append(f'({KINDS[o.op]} "{a["identity"]}" {a["generation"]}{result})')
    return f'''(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(ld '((include-book "books/acceptance")
      (ld "tests/acl2/simulator.lisp" :ld-error-action :return :ld-error-triples t)
      (value-triple
       (prog2$ (cw "FN_SIM_PLAN s=acceptance-world k=0 n={len(steps)}~%")
        (if (fn-sim-world-run '({' '.join(steps)}) (fn-sim-acceptance-initial)
                             nil (list nil nil nil nil) 0 0)
          (cw "FN_SIM_RESULT s=acceptance-model r=passed~%")
          (cw "FN_SIM_RESULT s=acceptance-model r=failed~%")))))
    :ld-error-action :return :ld-error-triples t)
(quit)
'''


def observe(scenario, output, exit_code, elapsed):
    """Observations come from executed trace records, never the expected oracle."""
    j = Journal(scenario.id)
    j.stage("workload", "begun")
    try:
        traces = run_simulator.parse_records(output, run_simulator.TRACE_PREFIX)
        oracles = run_simulator.parse_records(output, run_simulator.ORACLE_PREFIX)
        plans = run_simulator.parse_records(output, run_simulator.PLAN_PREFIX)
        results = run_simulator.parse_records(output, run_simulator.RESULT_PREFIX)
    except ValueError as error:
        return j, checker.harness_failure(scenario, j, "malformed-model-record:" + str(error))
    expected = [("0", str(i)) for i in range(len(scenario.operations))]
    if (exit_code == 0 and results == [dict(s="acceptance-model", r="failed")]
            and plans == [dict(s="acceptance-world", k="0", n=str(len(expected)))]
            and traces and len(traces) <= len(expected)
            and [(t.get("k"), t.get("i")) for t in traces] == expected[:len(traces)]
            and [(t.get("k"), t.get("i")) for t in oracles] == expected[:len(traces)]):
        # The model itself stopped at a failed state/oracle predicate. Preserve
        # that counterexample rather than relabeling it a missing workload.
        j.internal("model-counterexample", observation=traces[-1], oracle=oracles[-1])
        return j, checker.Verdict("violation", scenario.id, j.digest(),
                  cause="model-oracle-rejected",
                  explanation=dict(record=traces[-1], oracle=oracles[-1],
                                   rule="fn-sim-world-agreesp")).sign()
    if (exit_code != 0 or results != [dict(s="acceptance-model", r="passed")]
            or plans != [dict(s="acceptance-world", k="0", n=str(len(expected)))]
            or [(t.get("k"), t.get("i")) for t in traces] != expected
            or [(t.get("k"), t.get("i")) for t in oracles] != expected):
        return j, checker.harness_failure(scenario, j, "model-driver-incomplete")
    healing = set(scenario.healing)
    begun = False
    prepared = {}
    previous_pending = "none"
    for operation, trace, oracle in zip(scenario.operations, traces, oracles):
        args = operation.args
        wanted = dict(t=KINDS[operation.op], m=args["identity"], g=str(args["generation"]),
                      x=":" + args["result"].upper() if "result" in args else "-")
        if (trace.get("s") != "acceptance-world" or oracle.get("s") != "acceptance-world"
                or any(trace.get(k) != v for k, v in wanted.items())
                or any(k not in trace or k not in oracle for k in VIEW)):
            return j, checker.harness_failure(scenario, j, "model-operation-not-executed:" + operation.id)
        if operation.id in healing and not begun:
            j.stage("workload", "ended")
            j.stage("healing", "begun")
            begun = True
        j.client("model-step", operation=operation.id, **{k: trace[k] for k in VIEW})
        j.internal("model-oracle", operation=operation.id, **{k: oracle[k] for k in VIEW})
        if any(trace[k] != oracle[k] for k in VIEW):
            return j, checker.Verdict("violation", scenario.id, j.digest(),
                      explanation=dict(record=trace, oracle=oracle,
                                       rule="independent-ACL2-oracle")).sign()
        for fault in scenario.faults:
            if fault.operation == operation.id:
                activated = ((fault.action == "report-error" and trace["x"] in
                              (":ABORTED", ":INDETERMINATE")) or
                             (fault.action == "deliver-stale-completion" and
                              args["identity"] in prepared and
                              trace["g"] != prepared[args["identity"]]))
                if not activated:
                    return j, checker.harness_failure(scenario, j,
                              "fault-never-occurred:" + operation.id)
                j.environment("fault-fired", operation=operation.id, boundary=fault.boundary,
                              action=fault.action, evidence=wanted,
                              scope="logical completion delivery; no native I/O")
        if operation.op == "model-prepare" and previous_pending == "none" \
                and trace["p"] == args["identity"]:
            prepared[args["identity"]] = trace["g"]
        previous_pending = trace["p"]
    j.environment("model-terminal", **{k: traces[-1][k] for k in VIEW})
    j.stage("healing", "ended", elapsed=elapsed)
    return j, checker.check(scenario, j)


def execute(scenario, out, timeout=120):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    source = driver(scenario)
    (out / "scenario.json").write_text(json.dumps(scenario.to_json(), indent=2) + "\n")
    (out / "driver.lsp").write_text(source)
    launcher = run_simulator.executable()
    started = time.monotonic()
    if launcher is None:
        output, status = "ACL2 launcher unavailable", 2
    else:
        try:
            result = acl2_slots.run([str(launcher)], "resilience acceptance-model", cwd=ROOT,
                                    input=source.encode(), stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=timeout, check=False)
            output, status = result.stdout.decode(errors="replace"), result.returncode
        except subprocess.TimeoutExpired as error:
            output = (error.stdout or b"").decode(errors="replace")
            status = "timed-out"
    elapsed = time.monotonic() - started
    (out / "acl2.log").write_text(output)
    journal, verdict = observe(scenario, output, status, elapsed)
    journal.write(out / "journal.jsonl")
    (out / "verdict.json").write_text(json.dumps(verdict.to_json(), indent=2) + "\n")
    manifest = dict(status=verdict.kind, exit_code=status, elapsed=elapsed,
                    scope="ACL2 acceptance model; not native I/O or release qualification",
                    input_digests_sha256={str(p.relative_to(ROOT)): run_simulator.digest(p)
                         for p in (ROOT / "tests/acl2/simulator.lisp", ROOT / "books/acceptance.lisp",
                                   ROOT / "books/acceptance.cert", ROOT / "tools/run_simulator.py",
                                   ROOT / "tools/resilience/adapters/simulator.py",
                                   ROOT / "tools/resilience/contract.py",
                                   ROOT / "tools/resilience/checker.py",
                                   ROOT / "tools/resilience/scenario.py")},
                    scenario_sha256=run_simulator.digest(out / "scenario.json"),
                    driver_sha256=run_simulator.digest(out / "driver.lsp"))
    if launcher:
        manifest.update(launcher=str(launcher), launcher_sha256=run_simulator.digest(launcher))
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return verdict


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    scenario = Scenario.from_json(json.loads(args.scenario.read_text())) if args.scenario else example()
    verdict = execute(scenario, args.out)
    print(f"{scenario.id}: {verdict.kind} ({verdict.cause or 'model scope'})")
    return 0 if verdict.green else 1


if __name__ == "__main__":
    raise SystemExit(main())
