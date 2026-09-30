"""Joint actual owner admission and PIO lifecycle, source scope only.

The actual owner wrapper derives read demand and the PRL token. The adapter
never calls fn-pio-issue or calculates a served charge. Supplied :ok/:error
completion is a logical core input, not observed native return/death/join.
"""
import copy
import re
from .checker import Verdict
from .journal import Journal
from .scenario import Operation, Scenario

ACTIONS = ("register", "admit", "cancel", "complete", "evict", "close")
SELECTORS = ("exact", "wrong-trailer")
RECIPE = {"recipe": "admitted-page-owner-fixture", "budget": [100000, 0, 2, 1, 10],
          "baseline": [3000, 0, 0, 0, 0], "bookkeeping": 64,
          "fd_bookkeeping": 64, "file_limit": 100}


def example():
    def op(name, action, request="A", selector="exact", verdict="ok"):
        return Operation(name, "core", "page-" + action,
                         {"request": request, "selector": selector, "verdict": verdict})
    operations = [op("register", "register"), op("admit-A", "admit"),
                  op("cancel-A", "cancel"), op("close-held", "close"),
                  op("wrong-completion", "complete", selector="wrong-trailer"),
                  op("settle-cancelled", "complete"), op("admit-B", "admit", "B"),
                  op("old-completion", "complete"), op("publish-B", "complete", "B"),
                  op("close-cached", "close", "B"), op("evict-B", "evict", "B"),
                  op("close", "close", "B")]
    return Scenario("admitted-page-owner-lifecycle", "actual owner admission, cancellation and exact settlement",
                    "admitted-page-source", copy.deepcopy(RECIPE), [{"name": "core", "kind": "client"}],
                    operations, [], [o.id for o in operations[5:]], ["admitted-page-logical-clear"],
                    replay="exact")


def from_scenario(scenario):
    if scenario.contract != "admitted-page-source" or scenario.initial != RECIPE:
        raise ValueError("admitted page source requires exact owner fixture coordinate")
    if scenario.faults or scenario.healing_bound is not None:
        raise ValueError("source lifecycle has no native fault or healing-time observation")
    if scenario.witnesses != ["admitted-page-logical-clear"]:
        raise ValueError("source lifecycle supports only its logical clear witness")
    seen = set()
    for operation in scenario.operations:
        args = operation.args
        if operation.op not in {"page-" + a for a in ACTIONS} or set(args) != {"request", "selector", "verdict"}:
            raise ValueError("unsupported admitted page operation or arguments")
        if not isinstance(args["request"], str) or not re.fullmatch(r"[A-Z][A-Z0-9-]{0,39}", args["request"]):
            raise ValueError("uppercase symbolic request label required; no Lisp case aliases")
        if args["selector"] not in SELECTORS or args["verdict"] not in ("ok", "error"):
            raise ValueError("unsupported token selector or supplied logical verdict")
        action = operation.op[5:]
        if action == "admit":
            if args["request"] in seen:
                raise ValueError("request label cannot overwrite retained token")
            seen.add(args["request"])
        elif action in ("cancel", "complete", "evict") and args["request"] not in seen:
            raise ValueError("request consumer precedes its actual admission")
    ids = [o.id for o in scenario.operations]
    if not scenario.healing or ids[-len(scenario.healing):] != scenario.healing:
        raise ValueError("source lifecycle healing must be a nonempty suffix")
    return scenario.operations


def driver(scenario, trial=0):
    operations = from_scenario(scenario)
    if type(trial) is not int or trial < 0:
        raise ValueError("natural trial ID required")
    prefix = f"fn-w7-prl-{trial}"
    steps = " ".join(f'(:{o.op[5:]} :{o.args["request"]} :{o.args["selector"]} :{o.args["verdict"]})'
                     for o in operations)
    # Fresh helper names per trial, no candidate adds a rewrite rule.
    return f'''(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(defun {prefix}-step (op rows tokens fn-page-read-pool)
 (declare (xargs :mode :program :stobjs fn-page-read-pool))
 (let* ((kind (car op)) (label (cadr op)) (original (cdr (assoc-equal label tokens)))
        (token (if (and original (equal (caddr op) :wrong-trailer))
                   (update-nth 5 (+ 1 (nth 5 original)) original) original))
        (row (cdr (assoc-equal label rows))))
  (cond
   ((eq kind :register)
    (mv-let (answer fn-page-read-pool)
      (fn-owner-page-read-register-path 11 "journal000000.log" fn-page-read-pool)
      (mv answer rows tokens fn-page-read-pool)))
   ((eq kind :admit)
    (mv-let (answer token fn-page-read-pool)
      (fn-owner-page-read-admit 7 11 200 64 999 fn-page-read-pool)
      (mv answer (acons label (fn-pio-own-admitted-token token) rows)
          (acons label token tokens) fn-page-read-pool)))
   ((eq kind :cancel)
    (mv :cancel-attempt (acons label (fn-pio-cancel row token) (remove-assoc-equal label rows))
        tokens fn-page-read-pool))
   ((eq kind :complete)
    (mv-let (next answer) (fn-pio-complete row token (cadddr op))
      (let ((rows (acons label next (remove-assoc-equal label rows))))
       (if (eq answer :stale) (mv answer rows tokens fn-page-read-pool)
         (mv-let (settled fn-page-read-pool)
          (fn-owner-page-read-settle token (eq answer :publish) fn-page-read-pool)
          (mv (if (eq settled :settled) answer :settlement-missing) rows tokens fn-page-read-pool))))))
   ((eq kind :evict)
    (mv-let (answer fn-page-read-pool) (fn-owner-page-cache-evict token fn-page-read-pool)
     (mv answer rows tokens fn-page-read-pool)))
   (t
    (if (not (fn-pio-file-clear-p 11 (strip-cdrs rows)))
        (mv :owned-read-held rows tokens fn-page-read-pool)
      (mv-let (answer fn-page-read-pool) (fn-owner-page-read-close 11 fn-page-read-pool)
        (mv answer rows tokens fn-page-read-pool)))))))
(defun {prefix}-run (ops rows tokens i fn-page-read-pool)
 (declare (xargs :mode :program :stobjs fn-page-read-pool))
 (if (atom ops) fn-page-read-pool
  (mv-let (answer rows tokens fn-page-read-pool)
   ({prefix}-step (car ops) rows tokens fn-page-read-pool)
   (let* ((row (cdr (assoc-equal (cadar ops) rows)))
          (ledger (fn-owner-page-read-ledger fn-page-read-pool)))
    (prog2$ (cw "FN_W7_ADMITTED trial={trial} step=~x0 answer=~x1 phase=~x2 bytes=~x3 workers=~x4 next=~x5 spent=~x6 baseline=~x7 clear=~x8 preview=~x9~%"
       i (if (equal answer '(:fault :error)) :fault-error answer) (or (nth 6 row) :none) (fn-prl-nth 0 (fn-prl-nth 1 ledger))
       (fn-prl-nth 3 (fn-prl-nth 1 ledger)) (fn-prl-nth 2 ledger)
       (fn-prl-nth 4 (fn-prl-nth 1 ledger)) (fn-prl-nth 0 (fn-prl-baseline ledger))
       (fn-pio-file-clear-p 11 (strip-cdrs rows))
       (fn-owner-page-read-close-preview 11 fn-page-read-pool))
      ({prefix}-run (cdr ops) rows tokens (+ 1 i) fn-page-read-pool))))))
(defun {prefix}-trial (fn-page-read-pool)
 (declare (xargs :mode :program :stobjs fn-page-read-pool))
 (mv-let (installed fn-page-read-pool)
  (fn-owner-page-read-install-baseline '(100000 0 2 1 10) '(3000 0 0 0 0) 64 64 100 fn-page-read-pool)
  (if (not (eq installed :installed)) (mv nil fn-page-read-pool)
      (let ((fn-page-read-pool ({prefix}-run '({steps}) nil nil 0 fn-page-read-pool)))
       (mv t fn-page-read-pool)))))
(defun {prefix}-local () (declare (xargs :mode :program))
 (with-local-stobj fn-page-read-pool
  (mv-let (ok fn-page-read-pool) ({prefix}-trial fn-page-read-pool) ok)))
(value-triple ({prefix}-local))
(value-triple (cw "FN_W7_ADMITTED_COMPLETE trial={trial}~%"))
'''


TRACE = re.compile(r"FN_W7_ADMITTED trial=(\d+) step=(\d+) answer=(:[A-Z-]+)\s+phase=(:[A-Z-]+)\s+"
                   r"bytes=(\d+) workers=(\d+) next=(\d+) spent=(\d+) baseline=(\d+) clear=(T|NIL) preview=(:[A-Z-]+)")


def observe(scenario, text, trial=0):
    journal = Journal(scenario.id)
    for match in TRACE.finditer(text):
        run, index, answer, phase, charged, workers, next_id, spent, baseline, clear, preview = match.groups()
        if int(run) != trial:
            continue
        index = int(index)
        journal.client("admitted-page-step", operation=(scenario.operations[index].id
                       if index < len(scenario.operations) else "unknown"), step=index,
                       answer=answer, phase=phase, charged_bytes=int(charged), workers=int(workers),
                       next_id=int(next_id), spent=int(spent), baseline_bytes=int(baseline), clear=clear == "T", preview=preview)
    return journal


def judge(scenario, journal):
    """Relational oracle over observed calls, not a served admission decision."""
    operations = from_scenario(scenario)
    base = dict(scenario_id=scenario.id, journal_digest=journal.digest(),
                pending_rules=["page-native-integrity-verdict", "page-native-return-and-join",
                               "page-supported-runtime-startup", "page-captured-reclaim-composition"])
    rows = journal.of_kind("client")
    fields = {"step", "answer", "phase", "charged_bytes", "workers", "next_id", "spent", "baseline_bytes", "clear", "preview"}
    if len(rows) != len(operations) or any(not fields <= set(r) or r.get("operation") != o.id
         or r.get("step") != i or r.get("event") != "admitted-page-step"
         or any(type(r[k]) is not int or r[k] < 0 for k in ("charged_bytes", "workers", "next_id", "spent", "baseline_bytes"))
         or type(r["clear"]) is not bool for i, (o, r) in enumerate(zip(operations, rows))):
        return Verdict("harness-failure", cause="admitted-page-observation-incomplete", **base).sign()
    prior = None
    active = {}
    cached = set()
    for op, row in zip(operations, rows):
        action, label = op.op[5:], op.args["request"]
        rule = None
        if row["baseline_bytes"] != scenario.initial["baseline"][0] or row["spent"] != row["next_id"]:
            rule = "admitted-page-installed-baseline-or-spent-credit"
        elif prior and row["next_id"] < prior["next_id"]:
            rule = "admitted-page-identity-counter-regressed"
        elif action == "admit" and row["answer"] == ":ADMITTED":
            if row["phase"] != ":ISSUED" or row["clear"] or row["workers"] != 1 or (
                    prior and row["next_id"] != prior["next_id"] + 1):
                rule = "admitted-page-token-ownership"
            active[label] = ":ISSUED"
        elif action == "admit" and prior and any(row[k] != prior[k] for k in
                                              ("charged_bytes", "workers", "next_id")):
            rule = "admitted-page-refusal-mutated-ledger"
        elif action == "cancel" and op.args["selector"] == "exact" and active.get(label) == ":ISSUED":
            if row["phase"] != ":CANCELLED" or any(row[k] != prior[k] for k in
                                                 ("charged_bytes", "workers", "next_id")):
                rule = "admitted-page-cancel-refunded-before-completion"
            active[label] = ":CANCELLED"
        elif action == "complete":
            stale = op.args["selector"] != "exact" or active.get(label) not in (":ISSUED", ":CANCELLED")
            if stale:
                if row["answer"] != ":STALE" or any(row[k] != prior[k] for k in
                                                   ("charged_bytes", "workers", "next_id")):
                    rule = "admitted-page-stale-completion-mutated-live-charge"
            else:
                expected = (":PUBLISH" if active.get(label) == ":ISSUED" else ":CANCELLED")
                if op.args["verdict"] != "ok":
                    expected = ":FAULT-ERROR"
                if row["answer"] != expected or row["phase"] != ":SETTLED" or row["workers"] != 0:
                    rule = "admitted-page-exact-completion"
                active[label] = ":SETTLED"
                if expected == ":PUBLISH":
                    cached.add(label)
        elif action == "evict":
            if label in cached:
                if row["answer"] != ":EVICTED" or row["charged_bytes"] >= prior["charged_bytes"]:
                    rule = "admitted-page-cache-eviction"
                cached.discard(label)
            elif row["answer"] != ":STALE":
                rule = "admitted-page-stale-cache-eviction"
        elif action == "close" and cached and row["answer"] != ":READ-FILE-HELD":
            rule = "admitted-page-closed-charged-cache"
        elif action == "close" and not row["clear"] and row["answer"] != ":OWNED-READ-HELD":
            rule = "admitted-page-closed-live-owned-read"
        if rule:
            return Verdict("violation", cause=rule, explanation={"rule": rule, "operation": op.id,
                            "observed": row}, surviving=0, **base).sign()
        prior = row
    if not rows or rows[-1]["answer"] != ":CLOSED" or not rows[-1]["clear"] or rows[-1]["workers"]:
        return Verdict("no-witness", cause="admitted-page-logical-clear-not-observed", **base).sign()
    return Verdict("consistent", surviving=1, witnesses_observed=["admitted-page-logical-clear"],
                   diagnostics=["Actual source calls with supplied completion verdict; no native worker join observed."],
                   **base).sign()
