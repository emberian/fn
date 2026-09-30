"""Bounded dependency-preserving scenario reduction using the same backend.

Only an observed violation with the original cause is retained. Inconclusive,
missing-witness and harness failures are never accepted as reproductions.
The output is deletion-minimal within the declared execution budget, not a
claim of a globally smallest history.
"""
from dataclasses import dataclass, replace

from .scenario import Scenario, ScenarioError, check


def violation_signature(verdict):
    if verdict.kind != "violation":
        return None
    if verdict.cause:
        return ("cause", verdict.cause)
    rule = (getattr(verdict, "explanation", None) or {}).get("rule")
    return ("rule", rule) if rule else None


def dependencies(scenario):
    """Conservative prerequisites, including all model state transitions.

Model operations depend on their preceding transition: deleting a state
producer must not silently change the state supplied to a surviving action.
Explicit `requires` edges augment native identity and hold dependencies.
"""
    ids = {o.id for o in scenario.operations}
    edges = {}
    previous = None
    holds = {}
    for operation in scenario.operations:
        args = operation.args
        required = set(args.get("requires", ()))
        for key in ("of", "article"):
            if args.get(key) in ids:
                required.add(args[key])
        if scenario.contract in ("acceptance-model", "response-holds-model") and previous:
            required.add(previous)
        if operation.op == "acquire-hold":
            holds[args.get("owner")] = operation.id
        elif operation.op == "release-hold" and args.get("owner") in holds:
            required.add(holds[args["owner"]])
        if not required <= set(edges):
            raise ScenarioError(operation.id + ": prerequisite must precede operation")
        edges[operation.id] = required
        previous = operation.id
    return edges


def delete(scenario, operation_id):
    """Delete an operation and transitive dependents; retain fault decisions."""
    edges = dependencies(scenario)
    if operation_id not in edges:
        raise KeyError(operation_id)
    removed = {operation_id}
    for identity, required in edges.items():
        if required & removed:
            removed.add(identity)
    operations = [o for o in scenario.operations if o.id not in removed]
    # Remove a whole fault if one of its participating actions disappeared;
    # never rewrite the schedule of a surviving fault.
    faults = [f for f in scenario.faults
              if f.operation not in removed and not set(f.interleave) & removed]
    candidate = replace(scenario, operations=operations, faults=faults,
                        healing=[i for i in scenario.healing if i not in removed])
    return check(candidate)


@dataclass
class Reduction:
    scenario: Scenario
    verdict: object
    executions: int
    exhausted: bool
    attempts: list


def minimize(scenario, execute, budget=100):
    """`execute` runs and retains each supplied scenario on one chosen backend."""
    if type(budget) is not int or budget < 1:
        raise ValueError("execution budget must be positive")
    check(scenario)
    dependencies(scenario)
    verdict = execute(scenario)
    count = 1
    attempts = []
    if verdict.kind != "violation":
        raise ValueError("minimization requires an observed violation")
    signature = violation_signature(verdict)
    if signature is None:
        raise ValueError("observed violation must name its cause or contract rule")
    while True:
        changed = False
        for operation in scenario.operations:
            try:
                candidate = delete(scenario, operation.id)
            except ScenarioError:
                continue
            if count == budget:
                return Reduction(scenario, verdict, count, True, attempts)
            observed = execute(candidate)
            count += 1
            retained = violation_signature(observed) == signature
            attempts.append(dict(removed=operation.id, kind=observed.kind,
                                 cause=observed.cause, retained=retained))
            if retained:
                scenario, verdict = candidate, observed
                changed = True
                break
        if not changed:
            return Reduction(scenario, verdict, count, False, attempts)
