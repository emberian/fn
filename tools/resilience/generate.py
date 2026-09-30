"""Bounded acceptance IR generation with separately keyed fault decisions.

This is the finite generator substrate for W7g, not its planned Hypothesis
state machine. Replay retains the scenario and exact decisions, not a seed.
"""
import hashlib
import random

from .scenario import Fault, Operation, Scenario, check


def fault_choice(seed, operation_id):
    digest = hashlib.sha256(f"resilience-fault-v1:{seed}:{operation_id}".encode()).digest()
    return int.from_bytes(digest[:8], "big") % 2 == 0


def acceptance(workload_seed, fault_seed, episodes=4):
    if type(episodes) is not int or not 1 <= episodes <= 32:
        raise ValueError("bounded generator episodes must be 1..32")
    workload = random.Random(workload_seed)
    operations, faults = [], []

    def add(name, kind, identity, result=None, generation=7):
        args = dict(identity=identity, generation=generation)
        if result is not None:
            args["result"] = result
        operations.append(Operation(name, "core", "model-" + kind, args))

    # A productive prefix keeps fault-heavy generated worlds from winning
    # merely by refusing everything. Model completion still decides its fate.
    add("productive-prepare", "prepare", "A")
    add("productive-durable", "complete", "A", "durable")
    for i in range(episodes):
        # Keep B uncommitted until healing, so each selected fault is
        # attached to an actual pending proposal rather than a duplicate.
        identity = "B"
        result = workload.choice(("aborted", "indeterminate"))
        resolution = "absent"
        add(f"prepare-{i}", "prepare", identity)
        stale = f"stale-{i}"
        if fault_choice(fault_seed, stale):
            add(stale, "complete", identity, "durable", 8)
            faults.append(Fault(stale, "model-completion-delivery", "deliver-stale-completion",
                                "contract-admissible", "observed"))
        add(f"complete-{i}", "complete", identity, result)
        if result == "indeterminate":
            faults.append(Fault(f"complete-{i}", "model-completion-delivery", "report-error",
                                "contract-admissible", "observed"))
            add(f"recover-{i}", "recover", identity, resolution)
    add("healing-prepare", "prepare", "B")
    add("healing-durable", "complete", "B", "durable")
    return check(Scenario(f"generated-acceptance-{workload_seed}-{fault_seed}",
                          "Generated bounded acceptance lifecycle", "acceptance-model",
                          {"recipe": "acceptance-model-empty", "prior": []},
                          [{"name": "core", "kind": "client"}], operations, faults,
                          ["healing-prepare", "healing-durable"],
                          ["model-prepared", "model-published", "model-settled"],
                          replay="exact", requirements=["STO-002"],
                          healing_bound={"kind": "experimental", "value": 120,
                                         "source": "bounded model execution budget"}))
