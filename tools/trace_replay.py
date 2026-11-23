#!/usr/bin/env python3
"""Independent diagnostic FIFO projection; never part of the served scheduler.

Input JSON contains records (the actual 19 scalar trace columns), lost,
calendar (principal/service pairs), cursor, and queues (Lisp-shaped rows,
e.g. [[0, 7, 8], [1, 9]]). Loss or incomplete visits refuse projection.
"""
from __future__ import annotations

import json
import sys
from collections.abc import Sequence
from dataclasses import dataclass

NONE = (1 << 32) - 1
MAILBOX, MACHINE, SERVICE, CLOCK, SIGNAL, MACHINE_START, ENQUEUE = range(7)
WIDTHS = (8, 32, 16, 32, 32, 32, 8, 1, 32, 16, 32, 32, 60, 32, 60, 32, 60, 32, 60)


class TraceError(ValueError):
    """Diagnostic evidence is incomplete or contradicts its queue history."""


@dataclass(frozen=True)
class Projection:
    cursor: int
    queues: tuple[tuple[int, ...], ...]


def _natural(value: object, width: int) -> bool:
    return type(value) is int and 0 <= value < 1 << width


def _record(row: Sequence[int]) -> tuple[int, ...]:
    if len(row) != len(WIDTHS) or any(not _natural(v, w) for v, w in zip(row, WIDTHS)):
        raise TraceError("invalid trace row")
    if row[0] > ENQUEUE:
        raise TraceError("unknown trace kind")
    return tuple(row)


def _metadata(row: tuple[int, ...]) -> bool:
    return row[4:8] == (0, 0, 0, 0) and row[8:10] == (NONE, 0) and row[11:] == (0,) * 8


def replay(records: Sequence[Sequence[int]], lost: int, calendar: Sequence[Sequence[object]],
           cursor: int, queues: Sequence[Sequence[int]]) -> Projection:
    if type(lost) is not int or lost != 0:
        raise TraceError("trace loss")
    if not calendar or type(cursor) is not int or not 0 <= cursor < len(calendar):
        raise TraceError("invalid calendar cursor")
    cal: list[tuple[str, int]] = []
    for item in calendar:
        if (len(item) != 2 or item[0] not in ("principal", "service")
                or not _natural(item[1], 16)):
            raise TraceError("invalid calendar entry")
        cal.append((str(item[0]), item[1]))
    principals = {p for kind, p in cal if kind == "principal"}
    fifo: dict[int, list[int]] = {}
    seen: set[int] = set()
    for queue in queues:
        if not queue or not _natural(queue[0], 16) or queue[0] not in principals or queue[0] in fifo:
            raise TraceError("invalid principal queue")
        ids = list(queue[1:])
        if any(not _natural(x, 32) or x == NONE or x in seen for x in ids):
            raise TraceError("invalid queued row")
        if len(set(ids)) != len(ids):
            raise TraceError("duplicate queued row")
        seen.update(ids)
        fifo[queue[0]] = ids

    def enqueue(machine: int, principal: int) -> None:
        if machine == NONE:
            return
        if principal not in principals:
            raise TraceError("unknown enqueue principal")
        if any(machine in values for values in fifo.values()):
            return
        fifo.setdefault(principal, []).append(machine)

    opened: tuple[int, int, int, int] | None = None
    for value in records:
        row = _record(value)
        kind, machine, principal, position = row[:4]
        identity = (machine, principal, position, row[10])
        if kind == ENQUEUE:
            if not _metadata(row) or machine == NONE or position != 0 or row[10] != 0:
                raise TraceError("invalid enqueue event")
            enqueue(machine, principal)
        elif kind == MACHINE_START:
            if opened is not None or not _metadata(row):
                raise TraceError("nested or malformed machine start")
            if position != cursor or cal[cursor] != ("principal", principal):
                raise TraceError("machine calendar mismatch")
            queue = fifo.get(principal, [])
            expected = queue[0] if queue else NONE
            if machine != expected:
                raise TraceError("dequeue mismatch")
            if queue:
                queue.pop(0)
            opened = identity
            cursor = (cursor + 1) % len(cal)
        elif kind == MACHINE:
            if opened is None or opened != identity:
                raise TraceError("unmatched machine end")
            if machine == NONE and (row[4:8] != (0, 1, 0, 0) or row[8] != NONE):
                raise TraceError("invalid empty visit")
            enqueue(row[8], row[9])
            if row[7]:
                enqueue(machine, principal)
            opened = None
        else:
            if opened is not None:
                raise TraceError("interleaved callback visit")
            if kind == SERVICE:
                if position != cursor or cal[cursor] != ("service", principal):
                    raise TraceError("service calendar mismatch")
                cursor = (cursor + 1) % len(cal)
                enqueue(row[8], row[9])
            elif kind == MAILBOX:
                enqueue(machine, principal)
    if opened is not None:
        raise TraceError("incomplete machine visit")
    return Projection(cursor, tuple((p, *values) for p, values in fifo.items()))


def main() -> int:
    try:
        source = json.load(sys.stdin)
        result = replay(source["records"], source["lost"], source["calendar"],
                        source["cursor"], source["queues"])
    except (KeyError, TypeError, ValueError) as error:
        json.dump({"error": str(error)}, sys.stdout)
        sys.stdout.write("\n")
        return 1
    json.dump({"cursor": result.cursor, "queues": result.queues}, sys.stdout)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
