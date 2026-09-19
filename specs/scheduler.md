# Contact scheduler and bounded work selection

REP-005 (`specs/replication.md`) requires durable queued work with explicit
resource limits, retry state and policy; contacts and monotonic elapsed time as
environmental observations; and no starvation or eventual-delivery claim
without a specified fairness/resource policy. This specification covers the
scheduler that C2-06 adds: `books/scheduler.lisp`,
`books/scheduler-invariants.lisp`, `host/scheduler-host.lisp`,
`tools/scheduler.py`.

## The property

For every finite sequence of contact-plan, clock, expiry, admission, transport
and restart observations, and for every sender workflow state: the scheduler
preserves its own state and never drops a queued work; it emits a BPv7 submit
only by consuming one that `fn-bp-step` produced from a durable attempt intent;
and neither a bundle expiry nor the loss of a contact changes the workflow —
its works, its receipts and the node its archive and forward pins live in come
back as the same object. Conditional on recurring contacts, sufficient
capacity, an accepting peer and a work that stays eligible, a work that has
reached the promotion queue is selected within `queue-bound` + 1 admissible
contact ticks.

## Inputs, and who decides what

| Input | Shape | Decided by |
| --- | --- | --- |
| Contact plan | `(fn-sched-contact peer start end)`, monotonic ms | the plan; `fn-sched-contact-holdsp` only checks containment |
| Clock | `fn-clock-observationp` (`books/clock.lisp`) | the host supplies, ACL2 reads |
| Expiry | `fn-clock-expiry-decision` | `books/clock.lisp`, never recomputed here |
| Durable works | `fn-bp-state-works` of an `fn-bp-statep` | `books/bp-workflow.lisp` |
| Eligibility | `fn-bp-work-retryablep` and not expired | `books/bp-workflow.lisp` |
| Priority, aging, admissibility, selection | `fn-sched-selection` | `books/scheduler.lisp` |
| Durability, ordering, bytes | the journal and the decision log | `tools/workflow_journal.py`, `tools/scheduler.py` |

`tools/scheduler.py` computes none of the above. It reads a bounded JSON
contact plan, calls the `:program` wrappers, writes frames ACL2 built, and
orders the filesystem.

## Priority, aging and the starvation counterexample

Deterministic priority is receipts before articles, then smaller before larger,
then oldest admission first (`fn-sched-betterp`). That order starves: with a
small article re-armed by a `:no-contact` observation at every contact,
`tests/acl2/scheduler-tests.lisp` runs `*sched-starvation-trace*` under the
stated unfair policy (`fn-sched-unfair-step`, priority with no aging) and the
large article receives no submit at all. The same trace under the aging policy
submits it on the third tick.

The aging rule is a FIFO, not a boost. An eligible item that is passed over
counts the pass; on reaching the configured `aging-limit` it is appended once
to a promotion queue, and selection drains that queue from the head before
consulting priority at all. Priority inversion is therefore bounded by the
promotion queue's length, which is bounded by the configured `queue-bound`.

## Composition with the workflow

A contact tick that selects a work drives two workflow events and no others:
`:attempt-prepare` then `:storage-complete :durable`, both through
`fn-bp-step`. The tick emits that dispatcher's effect list verbatim. If the
workflow refuses — fenced, a pending intent, a consumed transaction pair, a
work that is not retryable — there is no effect, no retry is charged, and no
decision is recorded (`fn-sched-refused-submit-is-a-no-op`).

`fn-sched-tick-step` is the modeled composition.
`fn-sched-tick-step-is-select-drive-take` is the equation between it and the
three calls the host makes in sequence: `fn-sched-host-selection`, the
journal's `persist_attempt_then_call`, and `fn-sched-host-commit`.

## The durable decision record

Proposed FNWF record kind `:schedule`, to be added to
`*fn-frame-workflow-kinds*` and `*fn-frame-workflow-specs*` in `books/frame`:

```
(cons :schedule (list :nat :nat :text :text :text :nat
                      (cons :enum '(:aged :priority)) :nat))
```

fields `(generation tick peer work-id attempt-id attempt-generation reason
passes)`. `books/scheduler.lisp` models the shape and validates it with
`fn-frame-values-okp` against that specification, so nothing outside ACL2
decides what a decision record is. Until the frame owner adds the row, the
host writes each record as one FNSC frame — the same header, the same field
encoding, the same A-CRYPTO trailer — under `<journal>/schedule/`.
A decision record is durable before the attempt it authorizes.

## Hypotheses

Safety takes none. `fn-sched-step-preserves-state`,
`fn-sched-trace-preserves-state`, `fn-sched-step-preserves-queued`,
`fn-sched-only-a-tick-or-a-relay-touches-the-workflow`,
`fn-sched-expiry-preserves-workflow`,
`fn-sched-contact-loss-preserves-queue-and-workflow`,
`fn-sched-selected-submit-is-a-workflow-submit`,
`fn-sched-refused-submit-is-a-no-op` and
`fn-sched-retries-stay-within-the-contact-bound` hold for every state and every
trace. FLR-004 forbids a safety property conditional on a contact schedule,
and none of these is.

Conditional progress (`fn-sched-conditional-progress-under-a-fairness`) takes
four, and `tests/acl2/scheduler-tests.lisp` has the `must-fail` case for each:

* **contacts recur** — A-FAIRNESS (`fn-assume-fairness-contact-index`,
  `books/assumptions.lisp`) makes the horizon a natural number of ticks;
* **capacity suffices** — `fn-sched-contact-runp`: each tick is admissible (a
  contact is open, the retry budget is not spent) and the durable store accepts
  the intent the scheduler prepares;
* **the peer accepts, the work is not closed** — `fn-sched-eligible-runp`;
* **the work is promoted and the promotion queue fits** —
  `member-equal` in `fn-sched-aged` and `fn-sched-aged-fitsp`.

## Covered scope, and what remains for C3-03

Covered: safety over arbitrary finite traces; the submit composition; expiry
and contact loss; the bounded retry accounting; the aging bound from the
promotion queue, `N = queue-bound + 1`, with `fn-sched-aged-fitsp` as an
explicit hypothesis; the starvation counterexample as a runnable trace under a
named unfair policy.

Not covered, and C3-03's:

* the multi-tick promotion induction that turns the single-tick fact
  `fn-sched-passed-over-work-reaches-the-promotion-queue` into the full
  `aging-limit` + `queue-bound` horizon without the membership hypothesis;
* `fn-sched-aged-fitsp` as a preserved invariant rather than a hypothesis —
  it needs the promotion queue's freedom from duplicates as a theorem;
* delivery, as opposed to selection: eventual handoff needs the validated
  transfer and relay transitions C2-07 and C2-08 produce;
* safety under clock jumps and outages stated over the scheduler rather than
  over `books/clock.lisp` alone;
* a real BPv7 run of the contact plan. `tests/bp-dtn7/fn_sender_lab.py` runs
  `CONTACT_PLAN` (two windows, one expiry) against `MockBpa` when the pinned
  dtn7-rs build is unavailable; that mock transmits no bundle and has no peer,
  and any report using it says so.
