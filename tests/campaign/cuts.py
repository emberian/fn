"""The cut table: every named barrier and side-effect boundary of a write path.

A *cut* is one point at which the campaign kills the host process.  Cuts are
not written by hand from prose: `discovered_points` reads the four host
modules and collects every `faults.at("<name>")` injection site together with
the function that encloses it, and `verify_table` refuses to run when the
declared table and the injector disagree.  A new fault point added to
`tools/` is therefore a new cut, and a renamed or deleted one is a loud
failure rather than a silently skipped check.

Each cut names the model crash point it corresponds to.  The store's crash
points are the `fn-sf-crash` choices of `books/store-files.lisp:466-527`:
`fn-sf-crash-choicep` admits `frontier-choice` in {:old, :new} and
`record-choice` in {:absent, :present}, and `fn-sf-frontier-new-visiblep` /
`fn-sf-record-present-visiblep` (`:476-488`) say in which phases each choice
is available -- exactly the windows in which the host has issued `os.replace`
or `os.link` but has not yet observed the reply.  The two journals' crash
points are the `fn-journal-crash` choices of `books/journal.lisp:281-311`
(:lost, :torn, :intact per volatile slot).  Where the model cannot express a
cut, the cut carries a `gap` string; the campaign reports those rather than
skipping them.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent

# One component per module: the campaign selects a component by passing its
# injector to that component's constructor, so two modules may use the same
# point name without ambiguity.
COMPONENT_MODULES = {
    "store": ROOT / "tools" / "run_store.py",
    "workflow": ROOT / "tools" / "workflow_journal.py",
    "receipt": ROOT / "tools" / "receipt_journal.py",
    "receive": ROOT / "tools" / "run_bp_receive.py",
}

SCENARIOS = ("cross-post", "bp-receive", "bp-retry", "capacity-refusal",
             "sender-enqueue")

# What the recovered durable state must show for the operation that was cut.
# "absent" and "present" are exact; "either" is the crash choice the model
# leaves open, and is the one place where a partial result would hide.
RECORD_EXPECTATIONS = ("absent", "either", "present", "n/a")


class CutTableError(RuntimeError):
    """The declared table and the host injector disagree."""


@dataclass(frozen=True)
class Cut:
    component: str
    point: str
    path: str                       # the enclosing host function
    model: str                      # the model crash point this cut is
    record: str = "n/a"             # expectation for the record this cut's
                                    # operation publishes, relative to the
                                    # scenario's template state
    scenarios: tuple[str, ...] = ()
    acknowledged: tuple[str, ...] = ()   # told to the caller/world before the kill
    quick: bool = False
    gap: str = ""                   # non-empty: the model cannot express this cut
    uncovered: str = ""             # non-empty: why no scenario reaches it

    @property
    def cut_id(self) -> str:
        return "{}:{}".format(self.component, self.point)

    @property
    def signature(self) -> tuple[str, str, str]:
        return (self.component, self.point, self.path)


# `:old` and `:new` below are `fn-sf-crash` frontier choices; `:absent` and
# `:present` are its record choices.  A cut whose comment says the model
# admits more than reality does is an over-approximation and is sound; a cut
# whose comment says reality admits more than the model does is a `gap`.
CUTS: tuple[Cut, ...] = (
    # -- store, advance_frontier ---------------------------------------------
    Cut("store", "frontier-staged-durable", "advance_frontier",
        "fn-sf phase :frontier-data-durable; frontier :old (the model also "
        "admits :new here, an over-approximation: os.replace has not run)",
        record="absent", scenarios=("cross-post",), quick=True),
    Cut("store", "frontier-replaced", "advance_frontier",
        "fn-sf crash point frontier-replace (store-files.lisp:471-479): "
        "phase :frontier-data-durable, frontier :old or :new",
        record="absent", scenarios=("cross-post",), quick=True),
    Cut("store", "frontier-attempted", "advance_frontier",
        "fn-sf phase :frontier-attempted, frontier :old or :new",
        record="absent", scenarios=("cross-post",)),
    Cut("store", "frontier-durable", "advance_frontier",
        "fn-sf phase :frontier-attempted after the host directory barrier but "
        "before its observation: frontier :old or :new; reality is :new, and "
        "fn-sf-completed-frontier-barrier-removes-old-choice removes :old "
        "only once the barrier is observed",
        record="absent", scenarios=("cross-post",)),
    Cut("store", "frontier-reserved", "advance_frontier",
        "fn-sf phase :reserved; no crash choice applies -- the reservation "
        "is stable and no record candidate exists",
        record="absent", scenarios=("cross-post",)),
    # -- store, publish -------------------------------------------------------
    Cut("store", "record-staged-durable", "publish",
        "fn-sf phase :record-data-durable, record :absent (the model also "
        "admits :present here, an over-approximation: os.link has not run)",
        record="absent", scenarios=("cross-post",), quick=True),
    Cut("store", "record-linked", "publish",
        "fn-sf crash point final-link (store-files.lisp:481-488): phase "
        ":record-data-durable, record :absent or :present",
        record="either", scenarios=("cross-post",), quick=True),
    Cut("store", "record-attempted", "publish",
        "fn-sf phase :record-attempted, record :absent or :present; reality is "
        ":present because os.link returned before the observation",
        record="present", scenarios=("cross-post",), quick=True),
    Cut("store", "record-durable", "publish",
        "fn-sf phase :record-attempted after the host directory barrier but "
        "before its observation: record :absent or :present; reality is "
        ":present, and fn-sf-completed-record-barrier-removes-absent-choice "
        "removes :absent only once the barrier is observed",
        record="present", scenarios=("cross-post",)),
    Cut("store", "record-completing", "publish",
        "fn-sf phase :completing, record :present",
        record="present", scenarios=("cross-post",)),
    Cut("store", "record-staging-cleaned", "publish",
        "fn-sf phase :completing, record :present; staging names are not "
        "kernel state, so the cleanup is outside every crash choice",
        record="present", scenarios=("cross-post",)),
    # -- store, finish --------------------------------------------------------
    Cut("store", "finish-consumed", "finish",
        "fn-sf phase :completing, record :present; the host gate is "
        "consumed and fn-sn-finish has not been called",
        record="present", scenarios=("cross-post",)),
    Cut("store", "finish-durable", "finish",
        "fn-sn durable completion observed; fn-sf record :present",
        record="present", scenarios=("cross-post",), quick=True),
    # -- store, recover -------------------------------------------------------
    Cut("store", "recover-replayed", "recover",
        "fn-sf-recover has moved :replaying -> :recovering; recovery writes "
        "no record, so both crash choices are the stable image",
        record="absent", scenarios=("cross-post", "capacity-refusal")),
    Cut("store", "recover-barrier", "recover",
        "fn-sf-recovery-barrier (store-files.lisp:542-557) between two of "
        "the *fn-sf-recovery-barrier-count* barriers; stable image",
        record="absent", scenarios=("cross-post", "capacity-refusal"),
        quick=True),
    # -- workflow journal, publish -------------------------------------------
    Cut("workflow", "write", "publish",
        "fn-journal-crash slot :lost -- the staged bytes are not durable and "
        "no final name exists",
        scenarios=("sender-enqueue",), quick=True),
    Cut("workflow", "file-fsync", "publish",
        "fn-journal-crash slot :lost -- the barrier returned but no final "
        "name was attempted, so the record cannot be in the image",
        scenarios=("sender-enqueue",)),
    Cut("workflow", "prepublish", "publish",
        "fn-journal-crash slot :lost",
        scenarios=("sender-enqueue",)),
    Cut("workflow", "postlink", "publish",
        "fn-journal-crash slot :intact or :lost -- the FNWF analogue of the "
        "store's final-link crash point",
        scenarios=("sender-enqueue",), quick=True,
        gap="fn-journal-crash is a generic slot model; no theorem binds an "
            "FNWF record file to a journal slot, so this cut is expressible "
            "only by analogy with fn-sf-crash record :absent/:present."),
    Cut("workflow", "directory-fsync", "publish",
        "fn-journal-crash slot :intact",
        scenarios=("sender-enqueue",)),
    Cut("workflow", "image-applied", "publish",
        "fn-journal-crash slot :intact; the ACL2 image is process state and "
        "is rebuilt by replay, so it has no crash choice",
        scenarios=("sender-enqueue",)),
    # -- workflow journal, stage_inbound -------------------------------------
    Cut("workflow", "inbound-staged-durable", "stage_inbound",
        "fn-journal-crash slot :lost -- the inbound frame is data durable "
        "under a staging name only",
        record="absent", scenarios=("bp-receive", "capacity-refusal"),
        quick=True),
    Cut("workflow", "inbound-linked", "stage_inbound",
        "fn-journal-crash slot :intact or :lost -- os.link has returned and "
        "the directory barrier has not run",
        record="absent", scenarios=("bp-receive", "capacity-refusal")),
    Cut("workflow", "inbound-durable", "stage_inbound",
        "fn-journal-crash slot :intact",
        record="absent", scenarios=("bp-receive", "capacity-refusal")),
    Cut("workflow", "inbound-reconciled", "stage_inbound",
        "fn-journal-crash slot :intact; the re-barrier of an already durable "
        "frame adds no new slot",
        record="present", scenarios=("bp-retry",), quick=True),
    Cut("workflow", "inbound-deleted", "stage_inbound",
        "the BPA delete is a transport side effect outside both crash models",
        uncovered="the receiver always defers BPA deletion (_defer_delete "
                  "raises), so this boundary is crossed only by a direct "
                  "stage_inbound caller; the same side effect is cut as "
                  "receive:bpa-deleted."),
    # -- workflow journal, retry_staged_delete -------------------------------
    Cut("workflow", "inbound-retry-deleted", "retry_staged_delete",
        "the BPA delete is a transport side effect outside both crash models",
        uncovered="retry_staged_delete has no caller on the receiver path; "
                  "its delete boundary is cut as receive:bpa-deleted."),
    # -- receipt journal, publish --------------------------------------------
    Cut("receipt", "receipt-staged-durable", "publish",
        "fn-journal-crash slot :lost -- FNRJ bytes durable under a staging "
        "name, no final name attempted",
        record="present", scenarios=("bp-receive",), quick=True),
    Cut("receipt", "postlink", "publish",
        "fn-journal-crash slot :intact or :lost -- the FNRJ analogue of the "
        "store's final-link crash point",
        record="present", scenarios=("bp-receive",), quick=True,
        gap="as for workflow:postlink: no theorem binds an FNRJ record file "
            "to a fn-journal-crash slot."),
    Cut("receipt", "receipt-durable", "publish",
        "fn-journal-crash slot :intact",
        record="present", scenarios=("bp-receive",)),
    Cut("receipt", "receipt-applied", "publish",
        "fn-journal-crash slot :intact; the applied ACL2 image is process "
        "state rebuilt by replay",
        record="present", scenarios=("bp-receive",)),
    # -- composite receiver ---------------------------------------------------
    Cut("receive", "staged", "receive_bpa_request",
        "fn-sf crash (:old, :absent) -- no store mutation has been issued; "
        "the inbound frame is a durable fn-journal slot",
        record="absent",
        scenarios=("bp-receive", "bp-retry", "capacity-refusal"), quick=True),
    Cut("receive", "store-published", "receive_bpa_request",
        "fn-sn durable completion observed: fn-sf record :present with no "
        "receiver-journal context record",
        record="present", scenarios=("bp-receive",), quick=True),
    Cut("receive", "context-persisted", "receive_bpa_request",
        "fn-sf record :present; FNRJ request-context slot :intact",
        record="present", scenarios=("bp-receive",)),
    Cut("receive", "receipt-intent", "_durably_decide",
        "fn-sf record :present; FNRJ receipt-intent slot :intact, decision "
        "slot absent -- the model's pending/blocked receipt state",
        record="present", scenarios=("bp-receive",), quick=True),
    Cut("receive", "receipt-committed", "_durably_decide",
        "fn-sf record :present; FNRJ decision slot :intact",
        record="present", scenarios=("bp-receive",)),
    Cut("receive", "receipt-regenerated", "_durably_decide",
        "fn-sf record :present; every journal slot :intact and the receipt "
        "ADU regenerated from them",
        record="present", scenarios=("bp-receive",),
        acknowledged=("receipt",)),
    Cut("receive", "bpa-deleted", "_delete_after_decision",
        "every durable slot :intact; the BPA delete is a transport side "
        "effect outside both crash models",
        record="present", scenarios=("bp-receive", "bp-retry"),
        acknowledged=("receipt", "bpa-delete"), quick=True),
)


def discovered_points() -> set[tuple[str, str, str]]:
    """Read the host modules and collect (component, point, function)."""
    found: set[tuple[str, str, str]] = set()
    for component, module in COMPONENT_MODULES.items():
        tree = ast.parse(module.read_text(), filename=str(module))
        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            for inner in ast.walk(node):
                if not isinstance(inner, ast.Call):
                    continue
                call = inner.func
                if not isinstance(call, ast.Attribute) or call.attr != "at":
                    continue
                owner = call.value
                name = (owner.attr if isinstance(owner, ast.Attribute)
                        else owner.id if isinstance(owner, ast.Name) else "")
                if name != "faults":
                    continue
                if len(inner.args) != 1 or not isinstance(inner.args[0], ast.Constant):
                    raise CutTableError(
                        "{}: fault point in {} is not a literal name".format(
                            module, node.name))
                found.add((component, inner.args[0].value, node.name))
    return found


def verify_table() -> None:
    """Fail loudly when the table and the host injector have drifted apart."""
    declared = {cut.signature for cut in CUTS}
    if len(declared) != len(CUTS):
        raise CutTableError("duplicate cut in the table")
    found = discovered_points()
    missing = sorted(found - declared)
    extra = sorted(declared - found)
    problems = []
    if missing:
        problems.append("fault points with no cut: {}".format(missing))
    if extra:
        problems.append("cuts with no fault point: {}".format(extra))
    for cut in CUTS:
        if cut.record not in RECORD_EXPECTATIONS:
            problems.append("{}: unknown record expectation {!r}".format(
                cut.cut_id, cut.record))
        for scenario in cut.scenarios:
            if scenario not in SCENARIOS:
                problems.append("{}: unknown scenario {!r}".format(
                    cut.cut_id, scenario))
        if not cut.scenarios and not cut.uncovered:
            problems.append(
                "{}: no scenario reaches it and no reason is recorded".format(
                    cut.cut_id))
        if cut.scenarios and cut.uncovered:
            problems.append("{}: covered but marked uncovered".format(cut.cut_id))
    if problems:
        raise CutTableError("; ".join(problems))


def cuts_for(scenario: str, quick: bool = False) -> tuple[Cut, ...]:
    return tuple(cut for cut in CUTS if scenario in cut.scenarios
                 and (cut.quick or not quick))


def pairs(quick: bool = False) -> tuple[tuple[str, Cut], ...]:
    """Every (scenario, cut) pair the campaign runs, in scenario order."""
    verify_table()
    return tuple((scenario, cut) for scenario in SCENARIOS
                 for cut in cuts_for(scenario, quick))


def uncovered_cuts() -> tuple[Cut, ...]:
    return tuple(cut for cut in CUTS if not cut.scenarios)


def model_gaps() -> tuple[Cut, ...]:
    return tuple(cut for cut in CUTS if cut.gap)


if __name__ == "__main__":
    verify_table()
    print("cuts={} pairs={} quick-pairs={} uncovered={} model-gaps={}".format(
        len(CUTS), len(pairs()), len(pairs(quick=True)),
        len(uncovered_cuts()), len(model_gaps())))
    for scenario in SCENARIOS:
        print("  {}: {}".format(scenario, " ".join(
            cut.cut_id for cut in cuts_for(scenario))))
