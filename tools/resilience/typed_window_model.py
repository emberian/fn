"""Bounded experimental typed-window IR and independent logical oracle.

One fixed supplied-vector fixture starts with request `initial` assigned.
Request labels are symbolic; the driver calls actual ACL2 APIs for every step.
No logical `return` operation asserts that a native thread physically joined.
"""
from dataclasses import dataclass

ACTIONS = ("admit", "acquire", "cancel", "return", "release", "settle")
SELECTORS = ("exact", "wrong-offset", "wrong-ticket", "wrong-worker")


@dataclass(frozen=True)
class Step:
    id: str
    action: str
    request: str = "initial"
    selector: str = "exact"


def validate(steps):
    seen, requests = set(), {"initial"}
    for step in steps:
        if not isinstance(step, Step) or step.action not in ACTIONS or step.selector not in SELECTORS:
            raise ValueError("unknown typed-window operation or selector")
        if not isinstance(step.id, str) or not step.id or step.id in seen:
            raise ValueError("empty or duplicate operation identity")
        if not isinstance(step.request, str) or not step.request:
            raise ValueError("request label missing")
        if step.action == "admit":
            if step.request in requests or step.selector != "exact":
                raise ValueError("admission must create a fresh symbolic request")
            requests.add(step.request)
        elif step.request not in requests:
            raise ValueError("request used before its producer")
        seen.add(step.id)
    return steps


def initial():
    return dict(live="initial", worker_request="initial", phase=":RUNNING",
                charged=320, workers=1, worker_id=0)


def transition(state, step):
    """Small logical contract transcription, independent of the ACL2 driver."""
    state = dict(state)
    answer = ":STALE-JOB"
    if step.selector == "wrong-worker":
        state["worker_id"] = 1
    if step.action == "admit":
        if state["live"] is None:
            state.update(live=step.request, charged=320, workers=1)
            answer = ":ADMITTED"
        else:
            answer = ":READ-RESOURCES-UNAVAILABLE"
    elif step.selector == "exact" and step.request == state["live"]:
        phase = state["phase"]
        if step.action == "acquire" and phase == ":IDLE":
            state.update(worker_request=step.request, phase=":RUNNING")
            answer = ":ASSIGNED"
        elif step.request == state["worker_request"] and state["worker_id"] == 0:
            if step.action == "cancel" and phase in (":RUNNING", ":RETURNED", ":CANCELLED-RUNNING", ":CANCELLED-RETURNED"):
                state["phase"] = ":CANCELLED-RUNNING" if phase in (":RUNNING", ":CANCELLED-RUNNING") else ":CANCELLED-RETURNED"
                answer = ":CANCELLED"
            elif step.action == "return" and phase in (":RUNNING", ":CANCELLED-RUNNING"):
                state["phase"] = ":RETURNED" if phase == ":RUNNING" else ":CANCELLED-RETURNED"
                answer = ":RETURNED"
            elif ((step.action == "release" and phase == ":RETURNED") or
                  (step.action == "settle" and phase == ":CANCELLED-RETURNED")):
                state.update(live=None, worker_request=None, phase=":IDLE", charged=64, workers=0)
                answer = ":RELEASED"
    return state, dict(answer=answer, phase=state["phase"], charged_bytes=state["charged"],
                       workers=state["workers"], close=":CLOSABLE" if state["live"] is None else ":READ-FILE-HELD")


def expectations(steps):
    validate(steps)
    state, views = initial(), []
    for step in steps:
        state, view = transition(state, step)
        views.append(view)
    return views


def dependencies(steps):
    """Retain state producers and each symbolic request's admission."""
    validate(steps)
    previous, producers, edges = None, {}, {}
    for step in steps:
        required = {previous} if previous else set()
        if step.request in producers:
            required.add(producers[step.request])
        if step.action == "admit":
            producers[step.request] = step.id
        edges[step.id] = required
        previous = step.id
    return edges


def driver(steps, trial=0):
    """Generated executable text contains only whitelisted verbs and integers."""
    validate(steps)
    if type(trial) is not int or trial < 0:
        raise ValueError("trial identity must be natural")
    prefix = f"w7t{trial}"
    forms = [f'(defconst *{prefix}-base* (mv-nth 1 (mv-list 2 (fn-prl-make-baseline \'(10000 0 2 1 20) \'(1000 0 0 0 0)))))',
             f'(defconst *{prefix}-registered* (mv-nth 1 (mv-list 2 (fn-prl-register *{prefix}-base* 11 \'(64 0 1 0 0)))))',
             f'(defconst *{prefix}-admit0* (mv-list 3 (fn-prw-admit *{prefix}-registered* \'(11 100 1000000000 200 900000000 16384 77) \'(256 0 0 1 1))))',
             f'(defconst *{prefix}-token0* (nth 1 *{prefix}-admit0*))',
             f'(defconst *{prefix}-state0* (mv-list 3 (fn-pwx-acquire (nth 2 *{prefix}-admit0*) (fn-pxe-new 0) *{prefix}-token0*)))']
    tokens = {"initial": f"*{prefix}-token0*"}
    for i, step in enumerate(steps, 1):
        prior = f"*{prefix}-state{i - 1}*"
        state = f"*{prefix}-state{i}*"
        if step.action == "admit":
            admit = f"*{prefix}-admit{i}*"
            token = f"*{prefix}-token{i}*"
            forms += [f'(defconst {admit} (mv-list 3 (fn-prw-admit (nth 2 {prior}) \'(11 100 1000000000 200 900000000 16384 77) \'(256 0 0 1 1))))',
                      f'(defconst {token} (nth 1 {admit}))',
                      f'(defconst {state} (list (nth 0 {admit}) (nth 1 {prior}) (nth 2 {admit})))']
            tokens[step.request] = token
        else:
            token = tokens[step.request]
            worker = f"(nth 1 {prior})"
            if step.selector == "wrong-offset":
                token = f"(update-nth 7 0 {token})"
            elif step.selector == "wrong-ticket":
                token = f"(update-nth 1 (+ 1000 (nfix (nth 1 {token}))) {token})"
            elif step.selector == "wrong-worker":
                worker = f"(update-nth 0 1 {worker})"
            function = "fn-pwx-settle-cancelled" if step.action == "settle" else "fn-pwx-" + step.action
            forms.append(f'(defconst {state} (mv-list 3 ({function} (nth 2 {prior}) {worker} {token})))')
        forms.append(f'(value-triple (cw "FN_W7_TYPED trial={trial} step={i - 1} answer=~x0 phase=~x1 bytes=~x2 workers=~x3 close=~x4~%" (nth 0 {state}) (fn-prl-nth 2 (nth 1 {state})) (fn-prl-nth 0 (fn-prl-nth 1 (nth 2 {state}))) (fn-prl-nth 3 (fn-prl-nth 1 (nth 2 {state}))) (fn-prl-close-preview (nth 2 {state}) 11)))')
    return "\n".join(forms) + "\n"


def observe(text, trial):
    """Collect only literal executed CW records for the selected trial."""
    import re
    from .journal import Journal
    pattern = re.compile(r"FN_W7_TYPED trial=(\d+)\s+step=(\d+)\s+answer=(:[A-Z-]+)\s+phase=(:[A-Z-]+)\s+bytes=(\d+)\s+workers=(\d+)\s+close=(:[A-Z-]+)")
    journal = Journal(f"typed-window-trial-{trial}")
    for match in pattern.finditer(text):
        found, step, answer, phase, charged, workers, close = match.groups()
        if int(found) == trial:
            journal.client("typed-window-step", step=int(step), answer=answer,
                           phase=phase, charged_bytes=int(charged), workers=int(workers), close=close)
    return journal


def judge(steps, journal, trial):
    from .checker import Verdict
    expected = expectations(steps)
    base = dict(scenario_id=journal.scenario_id, journal_digest=journal.digest(),
                pending_rules=["typed-window-native-return-and-join", "typed-window-whole-composition"])
    rows = journal.of_kind("client")
    if (journal.scenario_id != f"typed-window-trial-{trial}" or len(rows) != len(steps)
            or [r.get("step") for r in rows] != list(range(len(steps)))
            or any(r.get("event") != "typed-window-step" for r in rows)):
        return Verdict("harness-failure", cause="typed-window-incomplete-trial", **base).sign()
    for step, row, view in zip(steps, rows, expected):
        if any(field not in row for field in view):
            return Verdict("harness-failure", cause="typed-window-incomplete-observation", **base).sign()
        actual = {field: row[field] for field in view}
        if actual != view:
            return Verdict("violation", cause="typed-window-transition-contract", surviving=0,
                           explanation={"operation": step.id, "observed": actual, "expected": view}, **base).sign()
    return Verdict("consistent", surviving=1, diagnostics=["Logical API trial; physical native return and join remain unobserved."], **base).sign()
