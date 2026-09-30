"""Hypothesis stateful acceptance workloads executed by the actual ACL2 adapter.

Bundles retain symbolic proposal dependencies. Workload decisions come from
Hypothesis; the separately keyed fault stream decides stale deliveries. Every
trial retains its exact scenario, actual transitions, oracle and verdict.
This bounded A/B model establishes no native lifetime or served-path claim.
"""
import argparse
import json
from pathlib import Path
import hashlib
from importlib.metadata import distribution
import sys

from .adapters.simulator import execute
from .generate import fault_choice
from .scenario import Fault, Operation, Scenario, check


def run(out, examples=6, steps=6, fault_seed=23):
    if type(examples) is not int or examples < 1 or type(steps) is not int or steps < 1:
        raise ValueError("stateful campaign example and step budgets must be positive")
    from hypothesis import settings, strategies as st
    from hypothesis.stateful import Bundle, RuleBasedStateMachine, precondition, rule, run_state_machine_as_test

    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    trials = []
    import hypothesis
    from tools.run_simulator import digest
    (out / "campaign.json").write_text(json.dumps(dict(
        hypothesis=hypothesis.__version__, examples=examples, steps=steps, fault_seed=fault_seed,
        python=sys.version,
        hypothesis_install_record_sha256=hashlib.sha256(
            distribution("hypothesis").read_text("RECORD").encode()).hexdigest(),
        sortedcontainers_install_record_sha256=hashlib.sha256(
            distribution("sortedcontainers").read_text("RECORD").encode()).hexdigest(),
        generator_sha256=digest(Path(__file__)),
        fault_stream_sha256=digest(Path(__file__).with_name("generate.py")),
        scope="bounded acceptance model; native/composition claims pending"), indent=2) + "\n")

    class AcceptanceMachine(RuleBasedStateMachine):
        proposals = Bundle("proposals")

        def __init__(self):
            super().__init__()
            self.operations = []
            self.faults = []
            self.pending = None
            self.fenced = False
            self.add("prepare", "A")
            self.add("complete", "A", "durable")

        def add(self, kind, identity="B", result=None, generation=7):
            name = f"op-{len(self.operations)}"
            args = dict(identity=identity, generation=generation)
            if result is not None:
                args["result"] = result
            self.operations.append(Operation(name, "core", "model-" + kind, args))
            return name

        @precondition(lambda self: self.pending is None and not self.fenced)
        @rule(target=proposals)
        def prepare(self):
            self.pending = self.add("prepare")
            return self.pending

        @precondition(lambda self: self.pending is not None and not self.fenced)
        @rule(proposal=proposals, result=st.sampled_from(("aborted", "indeterminate")))
        def complete(self, proposal, result):
            # A selected old symbolic proposal supplies stale generation
            # delivery, never an invented effect for the current proposal.
            stale = proposal != self.pending or fault_choice(fault_seed, self.pending)
            if stale:
                operation = self.add("complete", result="durable", generation=8)
                self.faults.append(Fault(operation, "model-completion-delivery",
                                         "deliver-stale-completion", "contract-admissible", "observed"))
            operation = self.add("complete", result=result)
            if result == "indeterminate":
                self.fenced = True
                self.faults.append(Fault(operation, "model-completion-delivery", "report-error",
                                         "contract-admissible", "observed"))
            else:
                self.pending = None

        @precondition(lambda self: self.fenced)
        @rule()
        def recover(self):
            self.add("recover", result="absent")
            self.pending = None
            self.fenced = False

        @rule()
        def schedule_tick(self):
            # A scheduler choice without a model operation is not journaled
            # as an executed transition or counted as positive evidence.
            pass

        def teardown(self):
            healing_start = len(self.operations)
            if self.fenced:
                self.add("recover", result="absent")
            elif self.pending is not None:
                self.add("complete", result="aborted")
            self.add("prepare")
            self.add("complete", result="durable")
            number = len(trials)
            scenario = check(Scenario(f"hypothesis-acceptance-{number}",
                "Stateful bounded proposal/completion/recovery schedule", "acceptance-model",
                {"recipe": "acceptance-model-empty", "prior": []},
                [{"name": "core", "kind": "client"}], self.operations, self.faults,
                [o.id for o in self.operations[healing_start:]],
                ["model-prepared", "model-published", "model-settled"], requirements=["STO-002"],
                replay="exact", healing_bound={"kind": "experimental", "value": 120,
                                               "source": "bounded actual model execution"}))
            directory = out / f"trial-{number:04d}"
            verdict = execute(scenario, directory)
            trials.append(dict(directory=str(directory), kind=verdict.kind, cause=verdict.cause,
                               operations=len(self.operations), faults=len(self.faults)))
            (out / "trials.json").write_text(json.dumps(trials, indent=2) + "\n")
            assert verdict.green, verdict.to_json()

    run_state_machine_as_test(AcceptanceMachine,
        settings=settings(max_examples=examples, stateful_step_count=steps,
                          deadline=None, derandomize=True, database=None))
    return trials


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--examples", type=int, default=6)
    parser.add_argument("--steps", type=int, default=6)
    parser.add_argument("--fault-seed", type=int, default=23)
    args = parser.parse_args()
    trials = run(args.out, args.examples, args.steps, args.fault_seed)
    print(f"{len(trials)} actual ACL2 model trials, all positive witnesses observed")


if __name__ == "__main__":
    main()
