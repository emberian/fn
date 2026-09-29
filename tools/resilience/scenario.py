"""The scenario IR, version 2 (design §2).

A scenario is data: a contract profile, an initial-state recipe, actors and
ordered operations with SYMBOLIC identities, faults attached to NAMED
BOUNDARIES (never sleeps or syscall counts), a healing phase with its
declared bound, assertions, the positive witnesses the run must produce and
the verdict it expects.  `validate` refuses a scenario that names an
unregistered boundary, an unknown operation, a retry of nothing, a fault
without its class, a fault at a boundary its operation's programs never
reach, or a bound of no kind.

Version 2 adds (each with a default, so version-1 scenarios read as before):
the fault's ROUTE (the same cut name is a different column on `store post',
`operator post' and the served POST: native_cuts.POST_LOG_CUTS versus
POST_LOG_ONE_CANDIDATE), the `interleave' fault action (the nemesis runs
named operations while the boundary is held: the review's schedule-point
interleavings), the healing bound, the expected verdict and the recovery,
checkpoint, reclaim and receipt operations.
"""
from __future__ import annotations

from dataclasses import dataclass, field, asdict
import json
from pathlib import Path
import re
import sys

from . import IR_VERSION

ROOT = Path(__file__).resolve().parents[2]

OPERATIONS = ("post", "read", "list-group", "retry", "recover", "restart", "checkpoint",
              "status", "reader-snapshot", "deliver-chunk", "disconnect", "policy-change",
              "acquire-hold", "release-hold", "begin-compaction", "reclaim",
              "cancel-reader", "retire-generation", "deliver-delayed-page",
              "receipt", "replay-media", "probe")
FAULT_ACTIONS = ("kill", "lose-response", "withhold-completion", "report-error",
                 "drop-writes", "substitute-record", "rollback", "interleave")
FAULT_CLASSES = ("contract-admissible", "assumption-challenging")
STAGES = ("issued", "performed", "persisted", "observed")
WITNESSES = ("post-accepted", "retry-reconciled", "read-completed",
             "read-during-competing-work", "reclaim-freed", "recovery-completed",
             "memberships-listed", "checkpoint-installed")
REPLAY = ("exact", "timed", "image")
CONTRACTS = ("local-commit-log",)
CANDIDATE_RULES = ("absent", "present", "either")
# The routes a post's cut is reached by; the registry carries each route's
# column where they differ (design §5: `operator post' and `store post' are
# a batch of one, the served POST a member of the owner's quantum).
ROUTES = ("store-post", "operator-post", "served-post")
HEALING_BOUND_KINDS = ("seconds", "experimental")
EXPECTED = ("consistent", "violation", "inconclusive", "no-witness", "harness-failure",
            "healing-overran")

# The review's schedule points without an executable host coordinate for
# their INTERLEAVING (design §5): a scenario may name them; it is then not
# executable on the native backend, no verdict is manufactured, and the
# report names it pending.  `owner` is the lane asked for the coordinate;
# `kill_form` the cut that already exists for a process death there, if any.
PENDING_BOUNDARIES = {
    "page-read-outstanding": {
        "note": "reader cancel, generation retire, then the read delivered",
        "operations": ("read", "reader-snapshot"),
        "owner": "online-reclaim-8",
        "kill_form": None,
        "coordinate": "none yet: the hold sits in fn-owner-chunk-span (host/native/owner.lisp) "
                      "after the reader's snapshot and before the page's delivery; reader "
                      "generations are reclaim's since the pin port (extent-identity finished "
                      "at ef75e8f4e), so online-reclaim-8 adds the held form"},
    "reclaim-candidate-selected": {
        "note": "a new independent hold before the destructive action",
        "operations": ("reclaim",),
        "owner": "online-reclaim-8",
        "kill_form": "reclaim-captured",
        "coordinate": "kill form only: FN_NATIVE_RECLAIM_FAULT=captured:kill "
                      "(host/native/owner.lisp +fnn-reclaim-cuts+); the interleaving needs a "
                      "held (pause/resume) form of the same cut so a hold can be acquired "
                      "between the capture and the install"},
    "receipt-observed": {
        "note": "duplicate, reorder with a policy change, lose its durable completion",
        "operations": ("receipt",),
        "owner": "bp-remainder-3",
        "kill_form": None,
        "coordinate": "none yet: host/native/bp-app.lisp fnn-bpapp-receipt runs prepare, decide "
                      "and the ADU without a held point (FN_APP_JOURNAL_TEST_FAIL_RECEIPT_"
                      "DECISION_NAMESPACE fails the decision, it does not hold it); "
                      "bp-remainder-3 adds a hold after the decision is recorded and before "
                      "the ADU/completion"},
}

# Which operations reach each cut table, and the developer selector that
# names the cut (tests/campaign/native_cuts.py; host/native/io.lisp).
TABLE_OPERATIONS = {
    "POST_LOG_CUTS": ("post",), "POST_CUTS": ("post",),
    "RECOVERY_CUTS": ("recover", "restart"),
    "STATE_CHECKPOINT_CUTS": ("checkpoint",),
    "IMPORT_CUTS": ("probe",), "EXPORT_CUTS": ("probe",), "STATEMENT_CUTS": ("probe",),
}
TABLE_SELECTORS = {
    "POST_LOG_CUTS": "FN_NATIVE_POST_FAULT", "POST_CUTS": "FN_NATIVE_POST_FAULT",
    "RECOVERY_CUTS": "FN_NATIVE_RECOVERY_FAULT", "LOG_CUTS": "FN_NATIVE_LOG_FAULT",
    "STATE_CHECKPOINT_CUTS": "FN_NATIVE_STATE_CHECKPOINT_FAULT",
    "IMPORT_CUTS": "FN_NATIVE_IMPORT_FAULT", "EXPORT_CUTS": "FN_NATIVE_EXPORT_FAULT",
    "STATEMENT_CUTS": "FN_NATIVE_KEY_STATEMENT_FAULT",
}
RECLAIM_CUTS_SOURCE = "host/native/owner.lisp:+fnn-reclaim-cuts+"


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
    route: str = "store-post"
    interleave: tuple = ()      # operation ids the nemesis runs at the held boundary


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
    healing_bound: dict | None = None      # {kind, value, source}
    expected: str = "consistent"
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

    def fault_on(self, op_id: str) -> Fault | None:
        for f in self.faults:
            if f.operation == op_id:
                return f
        return None

    def to_json(self) -> dict:
        d = asdict(self)
        d["operations"] = [asdict(o) for o in self.operations]
        d["faults"] = [dict(asdict(f), interleave=list(f.interleave)) for f in self.faults]
        return d

    @classmethod
    def from_json(cls, d: dict) -> "Scenario":
        d = dict(d)
        d["operations"] = [Operation(**o) for o in d.get("operations", [])]
        d["faults"] = [Fault(**dict(f, interleave=tuple(f.get("interleave", ()))))
                       for f in d.get("faults", [])]
        return cls(**d)

    def dump(self, path: Path) -> None:
        Path(path).write_text(json.dumps(self.to_json(), indent=1, sort_keys=True) + "\n")

    @classmethod
    def load(cls, path: Path) -> "Scenario":
        return cls.from_json(json.loads(Path(path).read_text()))


def reclaim_cut_names(source: Path | None = None) -> list:
    """The reclaim pass's cut names as the host declares them
    (+fnn-reclaim-cuts+), [] when the tree has no reclaim pass."""
    path = Path(source) if source else ROOT / "host" / "native" / "owner.lisp"
    if not path.is_file():
        return []
    m = re.search(r"\(defparameter \+fnn-reclaim-cuts\+\s*'\(([^)]*)\)", path.read_text())
    return re.findall(r'"([a-z-]+)"', m.group(1)) if m else []


def boundary_registry() -> dict:
    """Every boundary a fault may name: the native cut tables (each cut's
    candidate column is the crash rule at that boundary, per route where the
    routes differ, verified against the model programs by
    native_cuts.verify_*), the reclaim pass's cuts (the host's own list),
    and the pending schedule points (no held coordinate, not executable)."""
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
            if table == "POST_LOG_CUTS":
                # `store post' and `operator post' commit a batch of one; the
                # served POST is a member of the owner's quantum.
                rules = {"store-post": native_cuts.POST_LOG_ONE_CANDIDATE[cut.name],
                         "operator-post": native_cuts.POST_LOG_ONE_CANDIDATE[cut.name],
                         "served-post": cut.candidate}
            else:
                rules = {r: cut.candidate for r in ROUTES}
            if table == "LOG_CUTS":
                ops = ("recover", "restart") if "recover" in cut.program else ("post",)
            else:
                ops = TABLE_OPERATIONS[table]
            entry = registry.get(cut.name)
            if entry is None:
                registry[cut.name] = {
                    "source": "tests/campaign/native_cuts.py:" + table, "tables": [table],
                    "program": cut.program, "book": cut.book,
                    "rule": rules["store-post"], "rules": rules,
                    "operations": list(ops), "actions": ["kill"],
                    "selector": TABLE_SELECTORS[table], "executable": True}
            else:
                entry["tables"].append(table)
                for op in ops:
                    if op not in entry["operations"]:
                        entry["operations"].append(op)
    for i, name in enumerate(reclaim_cut_names()):
        cuts = reclaim_cut_names()
        rule = "old" if i < cuts.index("installed") else "new"
        registry["reclaim-" + name] = {
            "source": RECLAIM_CUTS_SOURCE, "tables": ["RECLAIM_CUTS"],
            "program": "fn-owner-orcp-" + name, "book": "owner-reclaim-pass.lisp",
            "rule": rule, "rules": {r: rule for r in ROUTES},
            "operations": ["reclaim"], "actions": ["kill"],
            "selector": "FN_NATIVE_RECLAIM_FAULT", "selector_name": name, "executable": True}
    for name, row in PENDING_BOUNDARIES.items():
        registry[name] = {"source": "design §5 (pending)", "tables": [], "program": None,
                          "book": None, "rule": None, "rules": {},
                          "operations": list(row["operations"]), "actions": [],
                          "selector": None, "executable": False, "note": row["note"],
                          "owner": row["owner"], "kill_form": row["kill_form"],
                          "coordinate": row["coordinate"]}
    return registry


def validate(scenario: Scenario, registry: dict | None = None) -> list:
    """Every problem, by name; [] when the scenario is well-formed."""
    registry = boundary_registry() if registry is None else registry
    problems = []
    if scenario.version not in (1, IR_VERSION):
        problems.append("version {} is not {}".format(scenario.version, IR_VERSION))
    if scenario.contract not in CONTRACTS:
        problems.append("unknown contract profile " + scenario.contract)
    if scenario.replay not in REPLAY:
        problems.append("unknown replay label " + scenario.replay)
    if scenario.expected not in EXPECTED:
        problems.append("unknown expected verdict " + str(scenario.expected))
    b = scenario.healing_bound
    if b is not None:
        if b.get("kind") not in HEALING_BOUND_KINDS:
            problems.append("healing bound of no kind: " + str(b.get("kind")))
        if not isinstance(b.get("value"), (int, float)) or b.get("value") <= 0:
            problems.append("healing bound without a positive value")
        if not b.get("source"):
            problems.append("healing bound names its source (the contract, or experimental)")
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
    for step in scenario.healing:
        if step not in ids:
            problems.append("healing step {} is not an operation".format(step))
    for f in scenario.faults:
        if f.operation not in ids:
            problems.append("fault on unknown operation " + f.operation)
        entry = registry.get(f.boundary)
        if entry is None:
            problems.append("fault at unregistered boundary " + f.boundary)
        elif f.operation in ids:
            op = scenario.operation(f.operation)
            if op.op not in entry["operations"]:
                problems.append("fault {}@{}: a {} does not reach this boundary ({})".format(
                    f.operation, f.boundary, op.op, ", ".join(entry["operations"])))
        if f.action not in FAULT_ACTIONS:
            problems.append("unknown fault action " + f.action)
        if f.fault_class not in FAULT_CLASSES:
            problems.append("fault {}@{} has no class".format(f.operation, f.boundary))
        if f.stage not in STAGES:
            problems.append("unknown effect stage " + f.stage)
        if f.route not in ROUTES:
            problems.append("unknown route " + f.route)
        if f.action == "interleave" and not f.interleave:
            problems.append("fault {}@{} interleaves nothing".format(f.operation, f.boundary))
        for step in f.interleave:
            if step not in ids:
                problems.append("interleaved step {} is not an operation".format(step))
    for w in scenario.witnesses:
        if w not in WITNESSES:
            problems.append("unknown witness " + w)
    if not scenario.witnesses:
        problems.append("a scenario requires at least one positive witness")
    if not scenario.healing:
        problems.append("a scenario has a healing phase")
    return problems


def pending_reasons(scenario: Scenario, registry: dict | None = None) -> list:
    """Why the scenario is not executable on the native backend, by
    boundary; [] when every fault has a host coordinate for its action."""
    registry = boundary_registry() if registry is None else registry
    reasons = []
    for f in scenario.faults:
        entry = registry.get(f.boundary, {})
        if not entry.get("executable"):
            reasons.append("{}: {} (owner {})".format(
                f.boundary, entry.get("coordinate", "unregistered"), entry.get("owner", "?")))
        elif f.action not in entry.get("actions", ()):
            reasons.append("{}: no {} form of the cut (actions: {})".format(
                f.boundary, f.action, ", ".join(entry.get("actions", ()))))
    return reasons


def executable_on_native(scenario: Scenario, registry: dict | None = None) -> bool:
    return not pending_reasons(scenario, registry)


def check(scenario: Scenario, registry: dict | None = None) -> Scenario:
    problems = validate(scenario, registry)
    if problems:
        raise ScenarioError("; ".join(problems))
    return scenario
