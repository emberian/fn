"""The scenario IR, version 1 (design §2).

A scenario is data: a contract profile, an initial-state recipe, actors and
ordered operations with SYMBOLIC identities, faults attached to NAMED
BOUNDARIES (never sleeps or syscall counts), a healing phase, assertions
and the positive witnesses the run must produce.  `validate` refuses a
scenario that names an unregistered boundary, an unknown operation, a
retry of nothing, or a fault without its class.
"""
from __future__ import annotations

from dataclasses import dataclass, field, asdict
import json
from pathlib import Path
import sys

from . import IR_VERSION

ROOT = Path(__file__).resolve().parents[2]

OPERATIONS = ("post", "read", "list-group", "retry", "recover", "restart",
              "reader-snapshot", "deliver-chunk", "disconnect", "policy-change",
              "acquire-hold", "release-hold", "begin-compaction",
              "deliver-delayed-page", "replay-media", "probe")
FAULT_ACTIONS = ("kill", "lose-response", "withhold-completion", "report-error",
                 "drop-writes", "substitute-record", "rollback")
FAULT_CLASSES = ("contract-admissible", "assumption-challenging")
STAGES = ("issued", "performed", "persisted", "observed")
WITNESSES = ("post-accepted", "retry-reconciled", "read-completed",
             "read-during-competing-work", "reclaim-freed")
REPLAY = ("exact", "timed", "image")
CONTRACTS = ("local-commit-log",)
CANDIDATE_RULES = ("absent", "present", "either")

# The review's schedule points without a host coordinate yet (design §5):
# a scenario may name them; it is then not executable on the native
# backend, and no verdict is manufactured for it.
PENDING_BOUNDARIES = {
    "page-read-outstanding": "reader cancel, generation retire, then the read delivered",
    "reclaim-candidate-selected": "a new independent hold before the destructive action",
    "receipt-observed": "duplicate, reorder with a policy change, lose its durable completion",
}


class ScenarioError(ValueError):
    pass


@dataclass(frozen=True)
class Operation:
    id: str
    actor: str
    op: str
    args: dict = field(default_factory=dict)


@dataclass(frozen=True)
class Fault:
    operation: str
    boundary: str
    action: str
    fault_class: str
    stage: str = "persisted"


@dataclass
class Scenario:
    id: str
    title: str
    contract: str
    initial: dict
    actors: list
    operations: list
    faults: list
    healing: list
    witnesses: list
    requirements: list = field(default_factory=list)
    assertions: dict = field(default_factory=lambda: {"contract-consistent": True})
    replay: str = "exact"
    version: int = IR_VERSION

    def operation(self, op_id: str) -> Operation:
        for o in self.operations:
            if o.id == op_id:
                return o
        raise KeyError(op_id)

    def posts(self) -> list:
        return [o for o in self.operations if o.op == "post"]

    def retries(self) -> list:
        return [o for o in self.operations if o.op == "retry"]

    def prior_posts(self) -> list:
        """The initial recipe's already-accepted posts: [{id, groups}]."""
        return list(self.initial.get("prior", []))

    def groups_of(self, post_id: str) -> frozenset:
        for p in self.prior_posts():
            if p["id"] == post_id:
                return frozenset(p["groups"])
        return frozenset(self.operation(post_id).args.get("groups", ()))

    def to_json(self) -> dict:
        d = asdict(self)
        d["operations"] = [asdict(o) for o in self.operations]
        d["faults"] = [asdict(f) for f in self.faults]
        return d

    @classmethod
    def from_json(cls, d: dict) -> "Scenario":
        d = dict(d)
        d["operations"] = [Operation(**o) for o in d.get("operations", [])]
        d["faults"] = [Fault(**f) for f in d.get("faults", [])]
        return cls(**d)

    def dump(self, path: Path) -> None:
        Path(path).write_text(json.dumps(self.to_json(), indent=1, sort_keys=True) + "\n")

    @classmethod
    def load(cls, path: Path) -> "Scenario":
        return cls.from_json(json.loads(Path(path).read_text()))


def boundary_registry() -> dict:
    """Every boundary a fault may name: the native cut tables (each cut's
    candidate column is the crash rule at that boundary, verified against
    the model programs by native_cuts.verify_*), and the pending schedule
    points (no host coordinate, not executable)."""
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from tests.campaign import native_cuts  # noqa: E402
    registry = {}
    tables = (("POST_LOG_CUTS", native_cuts.POST_LOG_CUTS),
              ("POST_CUTS", native_cuts.POST_CUTS),
              ("RECOVERY_CUTS", native_cuts.RECOVERY_CUTS),
              ("LOG_CUTS", native_cuts.LOG_CUTS),
              ("STATE_CHECKPOINT_CUTS", native_cuts.STATE_CHECKPOINT_CUTS),
              ("IMPORT_CUTS", native_cuts.IMPORT_CUTS),
              ("EXPORT_CUTS", native_cuts.EXPORT_CUTS),
              ("STATEMENT_CUTS", native_cuts.STATEMENT_CUTS))
    for table, cuts in tables:
        for cut in cuts:
            rule = cut.candidate
            if table == "POST_LOG_CUTS":
                # `store post' commits a batch of one: the column for it.
                rule = native_cuts.POST_LOG_ONE_CANDIDATE[cut.name]
            registry.setdefault(cut.name, {
                "source": "tests/campaign/native_cuts.py:" + table,
                "program": cut.program, "book": cut.book,
                "rule": rule, "executable": True})
    for name, note in PENDING_BOUNDARIES.items():
        registry[name] = {"source": "design §5 (pending)", "program": None, "book": None,
                          "rule": None, "executable": False, "note": note}
    return registry


def validate(scenario: Scenario, registry: dict | None = None) -> list:
    """Every problem, by name; [] when the scenario is well-formed."""
    registry = boundary_registry() if registry is None else registry
    problems = []
    if scenario.version != IR_VERSION:
        problems.append("version {} is not {}".format(scenario.version, IR_VERSION))
    if scenario.contract not in CONTRACTS:
        problems.append("unknown contract profile " + scenario.contract)
    if scenario.replay not in REPLAY:
        problems.append("unknown replay label " + scenario.replay)
    ids = [o.id for o in scenario.operations]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        problems.append("duplicate operation id " + dup)
    prior_ids = {p["id"] for p in scenario.prior_posts()}
    actors = {a["name"] for a in scenario.actors}
    for o in scenario.operations:
        if o.op not in OPERATIONS:
            problems.append("{}: unknown operation {}".format(o.id, o.op))
        if o.actor not in actors:
            problems.append("{}: unknown actor {}".format(o.id, o.actor))
        if o.op == "post" and not o.args.get("groups"):
            problems.append("{}: a post names its groups".format(o.id))
        if o.op == "retry":
            of = o.args.get("of")
            if of not in ids or scenario.operation(of).op != "post":
                problems.append("{}: retry of nothing ({})".format(o.id, of))
        if o.op == "read" and o.args.get("article") not in set(ids) | prior_ids:
            problems.append("{}: read of an unknown article".format(o.id))
    for f in scenario.faults:
        if f.operation not in ids:
            problems.append("fault on unknown operation " + f.operation)
        if f.boundary not in registry:
            problems.append("fault at unregistered boundary " + f.boundary)
        if f.action not in FAULT_ACTIONS:
            problems.append("unknown fault action " + f.action)
        if f.fault_class not in FAULT_CLASSES:
            problems.append("fault {}@{} has no class".format(f.operation, f.boundary))
        if f.stage not in STAGES:
            problems.append("unknown effect stage " + f.stage)
    for w in scenario.witnesses:
        if w not in WITNESSES:
            problems.append("unknown witness " + w)
    if not scenario.witnesses:
        problems.append("a scenario requires at least one positive witness")
    if not scenario.healing:
        problems.append("a scenario has a healing phase")
    return problems


def executable_on_native(scenario: Scenario, registry: dict | None = None) -> bool:
    registry = boundary_registry() if registry is None else registry
    return all(registry.get(f.boundary, {}).get("executable") for f in scenario.faults)


def check(scenario: Scenario, registry: dict | None = None) -> Scenario:
    problems = validate(scenario, registry)
    if problems:
        raise ScenarioError("; ".join(problems))
    return scenario
