#!/usr/bin/env python3
"""Drive durable BP sender attempts from a contact plan through the scheduler.

This module is a byte pump and an ordering.  It chooses no work, computes no
priority, tests no admissibility and decides no expiry: every one of those is
`books/scheduler.lisp`, reached through the `:program` wrappers in
`host/scheduler-host.lisp`.  What lives here is the contact-plan reader, the
durable decision log, and the loop that calls the wrappers in the order the
model composes them --- selection, the journal's durable attempt, then the
scheduler's commit (`fn-sched-selection`, `fn-bp-step` twice, `fn-sched-take`;
`fn-sched-tick-step` in the book is that composition).

A decision record is durable before the attempt it authorizes.  An attempt the
workflow refuses is committed as a pass: no retry is charged, because the
scheduler charges a retry only for a submit permission ACL2 granted.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Callable, Optional, Sequence

# The durability barrier and every ACL2 result parse have exactly one owner.
try:
    from tools.run_store import (acl2_boolean, acl2_octets, acl2_result,
                                 durable_barrier)
except ImportError:  # loaded with tools/ itself on sys.path
    from run_store import (acl2_boolean, acl2_octets, acl2_result,
                           durable_barrier)

# Bounds are checked before any list is consumed, as the parsing rule requires.
MAX_PLAN_BYTES = 1 << 20
MAX_WINDOWS = 64
MAX_TICKS = 4096
MAX_WORKS = 1024
MAX_EXPIRIES = 1024
MAX_TEXT = 512
MAX_DECISION_RECORD = 4096 + 42


class PlanError(ValueError):
    """The contact plan is not a contact plan."""


@dataclass(frozen=True)
class Window:
    start: int
    end: int
    ticks: tuple[int, ...]


@dataclass(frozen=True)
class Work:
    work_id: str
    kind: str          # "receipt" or "article"; ACL2's :receipt / :article
    size: int


@dataclass(frozen=True)
class Expiry:
    at_tick: int
    work_id: str
    creation_time: int
    lifetime: int
    age: Optional[int]
    age_monotonic: Optional[int]
    monotonic: int
    wall: int
    wall_error: int
    has_wall: bool


@dataclass(frozen=True)
class ContactPlan:
    peer: str
    queue_bound: int
    aging_limit: int
    retry_bound: int
    works: tuple[Work, ...]
    windows: tuple[Window, ...]
    expiries: tuple[Expiry, ...]


def _text(value: object, field: str) -> str:
    if not isinstance(value, str) or not value or len(value) > MAX_TEXT:
        raise PlanError(f"{field} is not bounded text")
    return value


def _nat(value: object, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise PlanError(f"{field} is not a natural number")
    return value


def load_plan(path: Path) -> ContactPlan:
    """Read one bounded JSON contact plan.  No evaluator sees this file."""
    raw = Path(path).read_bytes()
    if len(raw) > MAX_PLAN_BYTES:
        raise PlanError("contact plan exceeds bound")
    document = json.loads(raw.decode("utf-8"))
    if not isinstance(document, dict):
        raise PlanError("contact plan is not an object")
    return plan_from(document)


def plan_from(document: dict) -> ContactPlan:
    peer = _text(document.get("peer"), "peer")
    config = document.get("config")
    if not isinstance(config, dict):
        raise PlanError("config is not an object")
    queue_bound = _nat(config.get("queue-bound"), "queue-bound")
    aging_limit = _nat(config.get("aging-limit"), "aging-limit")
    retry_bound = _nat(config.get("retry-bound"), "retry-bound")
    if not (queue_bound and aging_limit and retry_bound):
        raise PlanError("every configured bound is positive")

    entries = document.get("works", [])
    if not isinstance(entries, list) or len(entries) > MAX_WORKS:
        raise PlanError("works exceed bound")
    works = []
    for entry in entries:
        if not isinstance(entry, dict):
            raise PlanError("work is not an object")
        kind = _text(entry.get("class"), "class")
        if kind not in ("receipt", "article"):
            raise PlanError("class is neither receipt nor article")
        works.append(Work(_text(entry.get("work-id"), "work-id"), kind,
                          _nat(entry.get("size"), "size")))

    entries = document.get("windows", [])
    if not isinstance(entries, list) or not entries or len(entries) > MAX_WINDOWS:
        raise PlanError("windows exceed bound")
    windows = []
    total_ticks = 0
    for entry in entries:
        if not isinstance(entry, dict):
            raise PlanError("window is not an object")
        start = _nat(entry.get("start"), "start")
        end = _nat(entry.get("end"), "end")
        if end < start:
            raise PlanError("window ends before it starts")
        ticks = entry.get("ticks", [])
        if not isinstance(ticks, list):
            raise PlanError("ticks is not a list")
        total_ticks += len(ticks)
        if total_ticks > MAX_TICKS:
            raise PlanError("ticks exceed bound")
        for tick in ticks:
            _nat(tick, "tick")
        windows.append(Window(start, end, tuple(ticks)))

    entries = document.get("expiries", [])
    if not isinstance(entries, list) or len(entries) > MAX_EXPIRIES:
        raise PlanError("expiries exceed bound")
    expiries = []
    for entry in entries:
        if not isinstance(entry, dict):
            raise PlanError("expiry is not an object")
        age = entry.get("age")
        age_monotonic = entry.get("age-monotonic")
        if (age is None) != (age_monotonic is None):
            raise PlanError("a bundle age anchor is an age and a monotonic reading")
        expiries.append(Expiry(
            _nat(entry.get("at-tick"), "at-tick"),
            _text(entry.get("work-id"), "work-id"),
            _nat(entry.get("creation-time"), "creation-time"),
            _nat(entry.get("lifetime"), "lifetime"),
            None if age is None else _nat(age, "age"),
            None if age_monotonic is None else _nat(age_monotonic, "age-monotonic"),
            _nat(entry.get("monotonic"), "monotonic"),
            _nat(entry.get("wall", 0), "wall"),
            _nat(entry.get("wall-error", 0), "wall-error"),
            bool(entry.get("has-wall", False))))

    return ContactPlan(peer, queue_bound, aging_limit, retry_bound,
                       tuple(works), tuple(windows), tuple(expiries))


class DecisionLog:
    """The scheduler's durable decision log, inside the sender journal root.

    One FNSC frame per file.  ACL2 built the header, the field encoding and
    the payload (`fn-sched-decision-protected`); the host appends the A-CRYPTO
    trailer over exactly those octets and owns the filesystem ordering, as it
    does for FNST, FNWF, FNRJ and FNBI.
    """

    def __init__(self, root: Path):
        self.dir = Path(root) / "schedule"
        self.staging = Path(root) / "staging"

    def open(self) -> None:
        self.dir.mkdir(mode=0o700, parents=True, exist_ok=True)
        self.staging.mkdir(mode=0o700, parents=True, exist_ok=True)

    def entries(self) -> list[Path]:
        return sorted(p for p in self.dir.iterdir() if p.suffix == ".sc")

    def record(self, protected: bytes) -> Path:
        if not isinstance(protected, (bytes, bytearray)) or not protected:
            raise PlanError("ACL2 refused the decision record")
        framed = bytes(protected) + hashlib.sha256(bytes(protected)).digest()
        if len(framed) > MAX_DECISION_RECORD:
            raise PlanError("decision record exceeds bound")
        sequence = len(self.entries())
        stage = self.staging / f"sc{sequence:016x}.{os.getpid()}.tmp"
        final = self.dir / f"{sequence:016x}.sc"
        fd = os.open(stage, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        try:
            os.write(fd, framed)
            durable_barrier(fd)
        finally:
            os.close(fd)
        try:
            os.link(stage, final)
            dir_fd = os.open(self.dir, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
            try:
                durable_barrier(dir_fd)
            finally:
                os.close(dir_fd)
        finally:
            try:
                stage.unlink()
            except OSError:
                pass
        return final


class SchedulerHost:
    """The seam onto `host/scheduler-host.lisp`.  No decision is taken here."""

    def install(self, plan: ContactPlan, next_tx: int) -> None:
        raise NotImplementedError

    def observe(self, event: str) -> None:
        raise NotImplementedError

    def admissible(self) -> bool:
        raise NotImplementedError

    def selection(self) -> Optional[str]:
        raise NotImplementedError

    def decision_octets(self, work_id: str, attempt_id: str) -> bytes:
        raise NotImplementedError

    def commit(self, work_id: str, attempt_id: str) -> None:
        raise NotImplementedError

    def pass_tick(self) -> None:
        raise NotImplementedError


def _lit(text: str) -> str:
    return json.dumps(text)


class Acl2SchedulerHost(SchedulerHost):
    """Marshal to the `:program` wrappers.  Every answer is ACL2's."""

    def __init__(self, acl2):
        self.acl2 = acl2
        self.acl2.call('(ld "host/scheduler-host.lisp" :ld-error-action :return '
                       ':ld-error-triples t)')

    def _call(self, form: str) -> str:
        return self.acl2.call(form)

    def install(self, plan: ContactPlan, next_tx: int) -> None:
        self._call(f"(fn-sched-host-install (fn-sched-config {plan.queue_bound} "
                   f"{plan.aging_limit} {plan.retry_bound}) {next_tx} state)")
        for work in plan.works:
            self.observe(f"(fn-sched-admit-event {_lit(work.work_id)} "
                         f":{work.kind} {work.size})")

    def observe(self, event: str) -> None:
        self._call(f"(fn-sched-host-observe {event} state)")

    def admissible(self) -> bool:
        return acl2_boolean(self._call("(fn-sched-host-admissiblep state)"))

    def selection(self) -> Optional[str]:
        body = acl2_result(self._call("(fn-sched-host-selection state)"))
        return None if body.upper() == b":NONE" else work_id_of(body)

    def decision_octets(self, work_id: str, attempt_id: str) -> bytes:
        # The ids cross as string literals, as everywhere on this seam; the
        # wrapper converts them to the codec's octet lists once, next to the
        # contact peer that only ACL2 holds (host/scheduler-host.lisp).
        octets = acl2_octets(
            self._call(f"(fn-sched-host-decision-octets {_lit(work_id)} "
                       f"{_lit(attempt_id)} state)"))
        if not octets:
            raise PlanError("ACL2 refused the decision record")
        return octets

    def commit(self, work_id: str, attempt_id: str) -> None:
        self._call(f"(fn-sched-host-commit {_lit(work_id)} {_lit(attempt_id)} state)")

    def pass_tick(self) -> None:
        self._call("(fn-sched-host-pass state)")


def work_id_of(body: bytes) -> str:
    """One ACL2 string literal.  A bare symbol is not a work identifier."""
    text = body.decode("utf-8", "strict")
    start, end = text.find('"'), text.rfind('"')
    if start < 0 or end <= start or end - start - 1 > MAX_TEXT:
        raise PlanError("ACL2 returned no work identifier")
    return text[start + 1:end]


def contact_open_event(peer: str, start: int, end: int) -> str:
    return f"(fn-sched-open-event {_lit(peer)} {start} {end})"


def contact_close_event() -> str:
    return "(fn-sched-close-event)"


def expiry_event(expiry: Expiry) -> str:
    anchor = ("nil" if expiry.age is None
              else f"(cons {expiry.age} {expiry.age_monotonic})")
    observation = (f"(fn-clock-observation {expiry.monotonic} {expiry.wall} "
                   f"{expiry.wall_error} {'t' if expiry.has_wall else 'nil'})")
    return (f"(fn-sched-expiry-event {_lit(expiry.work_id)} "
            f"{expiry.creation_time} {expiry.lifetime} {anchor} {observation})")


def run_plan(plan: ContactPlan, host: SchedulerHost, log: DecisionLog,
             attempt: Callable[[str, str, int], bool],
             attempt_id: Callable[[int], str] = lambda n: f"attempt:{n}"
             ) -> list[dict]:
    """Run one contact plan.  Returns what happened at each tick, in order.

    `attempt(work_id, attempt_id, tick)` performs the durable attempt through
    `tools/workflow_journal.py` and returns whether ACL2 granted the submit
    permission.  A False answer is a pass, not a retry.
    """
    log.open()
    host.install(plan, next_tx=1000)
    outcomes: list[dict] = []
    tick_index = 0
    for window in plan.windows:
        host.observe(contact_open_event(plan.peer, window.start, window.end))
        for monotonic in window.ticks:
            for expiry in plan.expiries:
                if expiry.at_tick == tick_index:
                    host.observe(expiry_event(expiry))
            record = {"tick": tick_index, "monotonic": monotonic,
                      "peer": plan.peer, "outcome": "pass", "work-id": None}
            if not host.admissible():
                record["outcome"] = "inadmissible"
                host.pass_tick()
            else:
                work_id = host.selection()
                if work_id is None:
                    host.pass_tick()
                else:
                    name = attempt_id(tick_index)
                    log.record(host.decision_octets(work_id, name))
                    record["work-id"] = work_id
                    record["attempt-id"] = name
                    if attempt(work_id, name, tick_index):
                        host.commit(work_id, name)
                        record["outcome"] = "submitted"
                    else:
                        host.pass_tick()
                        record["outcome"] = "refused"
            outcomes.append(record)
            tick_index += 1
        host.observe(contact_close_event())
    return outcomes


def main(argv: Sequence[str]) -> int:
    if len(argv) != 2:
        print("usage: scheduler.py <contact-plan.json>")
        return 2
    try:
        plan = load_plan(Path(argv[1]))
    except (PlanError, OSError, json.JSONDecodeError) as error:
        print(f"refused: {error}")
        return 3
    print(json.dumps({"peer": plan.peer, "windows": len(plan.windows),
                      "ticks": sum(len(w.ticks) for w in plan.windows),
                      "works": len(plan.works),
                      "expiries": len(plan.expiries),
                      "queue-bound": plan.queue_bound,
                      "aging-limit": plan.aging_limit,
                      "retry-bound": plan.retry_bound}, indent=2))
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI
    import sys
    raise SystemExit(main(sys.argv))
