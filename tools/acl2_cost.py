"""What an ACL2 certification log says a book and its events cost.

ACL2 prints a summary after every event: `Form:`, `Time:` and, when the
prover ran, `Prover steps counted:`.  The step count is ACL2's own count of
rewriter and prover work and does not depend on the machine or its load:
the same bytes certified at 6.3 s and at 14.9 s of wall on persvati
(certify-20260927T060346Z-185095 and ...062853Z-481059,
books/byte-store-k0-authority-error) counted 1,488,179 steps both times.
`Time:` is not load-independent on these boxes (it tracked the wall in both
of those runs), so it is reported, never ratcheted.

The `(CERTIFY-BOOK ...)` summary counts every event of the certification's
proof pass, so its steps are the book's.  An enclosing event (encapsulate,
progn, make-event) prints its own summary after its inner events' and counts
them again, so the per-event view skips wrappers.  A certification that
failed before its CERTIFY-BOOK summary has no book step count: None, never 0.
"""

from __future__ import annotations

from dataclasses import dataclass
import re

SUMMARY = re.compile(r"(?m)^Summary\s*$")
FORM = re.compile(r"(?m)^Form:\s*(.*)$")
TIME = re.compile(r"(?m)^Time:\s*([0-9]+(?:\.[0-9]+)?) seconds")
STEPS = re.compile(r"(?m)^Prover steps counted:\s*(More than\s+)?([0-9,]+)")
WRAPPER = re.compile(r"^\(\s*(?:ENCAPSULATE|PROGN|MAKE-EVENT|CERTIFY-BOOK)\b", re.I)
CERTIFY = re.compile(r"^\(\s*CERTIFY-BOOK\b", re.I)


@dataclass(frozen=True)
class Event:
    form: str
    seconds: float | None
    steps: int | None
    capped: bool = False  # "More than N": N is a lower bound


def events(log: str) -> list[Event]:
    """Every summary in the log, in order."""
    found: list[Event] = []
    starts = [match.start() for match in SUMMARY.finditer(log)]
    for first, last in zip(starts, starts[1:] + [len(log)]):
        block = log[first:last]
        form = FORM.search(block)
        if form is None:
            continue
        time, steps = TIME.search(block), STEPS.search(block)
        found.append(Event(
            form.group(1).strip(),
            float(time.group(1)) if time else None,
            int(steps.group(2).replace(",", "")) if steps else None,
            bool(steps and steps.group(1))))
    return found


def book_steps(log: str) -> int | None:
    """The book's prover steps: its last CERTIFY-BOOK summary's count.

    A CERTIFY-BOOK summary with no steps line proved nothing (0 steps); no
    CERTIFY-BOOK summary at all is unknown (None).  Under --pcert the log is
    three waves; the proof pass is the one that counts steps, so the waves'
    counts are summed.
    """
    certified = [event for event in events(log) if CERTIFY.match(event.form)]
    if not certified:
        return None
    return sum(event.steps or 0 for event in certified)


def costliest_event(log: str) -> Event | None:
    """The non-wrapper event with the most prover steps (ties: the slower)."""
    inner = [event for event in events(log)
             if not WRAPPER.match(event.form) and event.steps is not None]
    return max(inner, key=lambda event: (event.steps, event.seconds or 0.0),
               default=None)


def slowest_event(log: str) -> Event | None:
    """The non-wrapper event with the largest `Time:`."""
    inner = [event for event in events(log)
             if not WRAPPER.match(event.form) and event.seconds is not None]
    return max(inner, key=lambda event: event.seconds, default=None)
