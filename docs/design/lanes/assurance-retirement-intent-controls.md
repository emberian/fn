# Ordinary retirement intent controls

The isolated `tests/retirement-intent-unit.lisp` depends on primitive/coordinator
changes 060bb71b6, completion-mode repair 0036c2769, and relocation repair
06337e461. It invokes the actual functions and observes their concrete tables;
there is no alternate retirement model. The composed submit/poll and record-install controls remain unexecuted in
ACL2; the narrower allocator controls passed the author gate described below.
No physical writer result is claimed.

The leaf control reserves/commits exact allocations, retains an existing target
obligation, begins retirement intent, and interleaves new installed-root refusal
with successful transient read pins and unrelated durable publication. Wrong
batch/epoch cancellation leaves the exact intent and allocation view unchanged.
Exact cancellation permits durable publication again. A second intent refuses a
wrong containing-batch install; exact install retires and clears its intent while
RETIRE_PENDING still blocks new durable edges. Existing protectors and unrelated
allocation/edge tuples remain unchanged.

Relocation controls use actual same-owner allocations and an installed-root edge,
so removing the intent check would move it onto the pending target. Refusal keeps
its source holder/counts intact; unrelated destination relocation and handback
work outside freeze. A separate frozen-state refusal keeps the same source.

The core control calls actual `fn2-retirement-submit`, then attempts durable-edge
publication and relocation onto that exact submitted handle before any turn.
It also acquires a transient pin and publishes/moves an unrelated placement.
Actual `fn2-retirement-poll` first returns pending. A clearly synthetic exact
refusal settlement then exercises cancellation and workspace release. A synthetic
accepted settlement without the target retirement must instead become uncertain,
retaining intent/workspace. A stopped-core variant retains pending intent and
workspace without converting ambiguity to refusal. These are prepared component
controls, not a claim that a real disk/fence/refusal/acceptance sequence ran.

Source review found an accepted-poll hole: ordinary first-use count/offset zeros
could pass the maintenance fallback without RETIRE_PENDING. Parent repaired it
in 0036c2769 by requiring maintenance mode on that branch; the contradictory
accepted-settlement control exercises that exact condition after real submit.

The no-I/O admission cancellation ordering is visible in the actual source:

- `fn2-commit-txn-join` returns :exhausted/0/0 at the size/member preflight before
  `fn2-commit-put-txn-member`. After a failed member mutation it stops the core.
- `fn2-commit-txn-open` maps commit-start pre-admission failures to
  :admission/:exhausted with 0/0 before member installation. Commit-start may
  reserve/unwind volatile pool/extent state, but invokes no issue/write/fence.
- After successful start, member/identity failures stop the core. The coordinator
  therefore retains intent on those paths; it does not treat 0/0 alone as proof.
- Ordinary admit starts intent only after exact planner batch and record packing;
  no scheduling boundary occurs between that binding and open/join. An unexpected
  result or successful mismatched batch stops with intent retained.
- Poll pending/wrong owner/stopped/uncertain paths return before cancellation.
  Exact settled refusal checks the actual allocation tuple before cancellation;
  accepted poll requires exact RETIRE_PENDING/batch and does not cancel.

This is a source-order audit, not an admitted causal/physical-I/O theorem. The
bounded physical writer, recovery and actual composed interleaving gates remain
pending the parent's narrow qualification. No production files were edited here.

## Isolated source gate entries

The original leaf body/run/assertion now lives verbatim in
`tests/retirement-intent-leaf-unit.lisp`, including `books/retirement` directly.
The composed `retirement-intent-unit` includes that leaf and the simulator/core
closure; its original submit/poll bodies and three assertions are byte-for-byte
unchanged. All four original assertions therefore remain in the composed closure.

`tests/retirement-intent-allocator-unit.lisp` uses the same actual allocator
scenario without fields or record serialization. It calls actual intent
begin/cancel, alloc-retire, edge-add/drop and relocate. It does not test submit,
poll, record installation or physical durability and contains no reference model.

The existing certification runner's read-only local-include scanner reports:

- Allocator entry: 7 local source books, including its test root. Dependencies
  are alloc, columns, declare, operations, owed and tuple.
- Record-install leaf entry: 28 local source books, including its test root.
- Composed submit/poll entry: 284 local source books, including its test root.

The qualified system B* book is outside those local-source counts. These are
source dependency closures, not certificate keys or executed gate results.

## Allocator lifecycle author gate (2026-11-14)

The exact nine-book source gate began at `926f82ffe`, with five qualified cached
parents (tuple, owed, declare, columns, operations). The source roots were alloc,
alloc-planning-unit, retirement-intent-allocator-unit and alloc-lifecycle-unit.
No format or core book was loaded. This is source admission and assertion
execution, not a record certificate.

The original allocator refused stobj translation in intent cancellation. The
same retained world admitted `d82406b1b` after all three new direct stobj-return
terms were given explicit LET bindings, preserving their guards and equations:
12.33 seconds and 1,463,790 prover steps. Planning's test observer then exposed
an attempted guard verification, non-executable projection, and missing deferred
snapshot definition. The final fixture (`aef710296`) instantiates the existing
column reference generator from the exact schema, including all columns and
scalar extras; it does not substitute a narrower observation.

Actual retirement assertions passed in 0.06 seconds; actual planning assertions
passed in 0.89 seconds, followed by the umbrella with zero refusals. These cover
owner/stale-frontier refusal, generic allocation closure, transient pin blocking
cancellation, exact cancellation and reopening, plus the intent interleavings
above. HELD construction, journal submit/poll, and durable FREE remain unqualified.

Forge logs: `/tmp/reclamation-alloc-lifecycle.log` (original refusal),
`-continue1.log` (revised allocator), `-retirement.log` (retirement assertions),
`-controls4.log` (planning and umbrella), all with the same filename prefix.
The detached outer PID was 594353, server 594586, ACL2 process group 594590;
external memory.max was 2147483648 and memory.swap.max was 0. The 600-second
window used a per-event 60-second/2,000,000-step limit. Explicit session cleanup
completed and all three recorded handles were absent; the cgroup disappeared.
Wrapper status 75 preserves the original startup refusal, separately from the
later successful retained-world results. The named 2 GiB allocation was released.

## Existing-control regression gate (2026-11-14)

The narrow integration branch now includes the existing `alloc-unit` controls.
Its final source is `58b4e89f5`, and the 12-book lifecycle closure key is
`2a03cf3072673dab9921831a09dd525ab8a1d8c8fa4466793076b6ced8512f70`.
Five cached foundational books were unchanged. Seven source books cover alloc,
the declaration-generated test projections, the independent reclaim checker,
existing allocator controls, planning, retirement intent and the umbrella.

Review found five old setups that acquired durable protection after retirement.
Their valid ordering now acquires it beforehand; transient post-retirement races
remain. The first retained-world attempt exposed the fifth case in pressure
teeth. Its LIVE, QUARANTINE, CHECKPOINT-BLOCKED and OK observations were preserved
by dropping the pre-existing protection before checking checkpoint pressure.
All original protector scenarios and corresponding model traces remain.

The final existing allocator target's 66 forms passed source admission and actual
assertions in 0.11 seconds / 103 prover steps. New controls exercise actual
release-prepare refusal/preservation, marker publication closure, transient pin
interleaving, release recheck and stale reuse. Both fixtures now use the existing
column-reference generator for every actual column and scalar extra, avoiding a
hand-maintained inventory. Planning and intent controls also passed in this same
world; no format/core book or physical writer was loaded.

Forge run prefix: `/tmp/reclamation-alloc-existing`; `-controls1.log` records the
successful resumed allocator/umbrella, while `.log` preserves the pressure setup
refusal and prior admitted source dependencies. Source hash of the repaired
`alloc-unit` is `c9e20c26e181530bfc64477839907cd64de9e811c7c33f217e966cd00705d1d4`.
Outer PID 619697, server 619764 and ACL2 process group 619765 were explicitly
stopped and absent; the cgroup disappeared. External memory.max was 2147483648,
swap.max 0, outer deadline 600 seconds and per-event budget 60 seconds / 2,000,000
steps. Status 75 retains the initial refusal separately from resumed success.
The named allocation was released. This remains an author source/assertion gate,
not record certification or actual composed persistence/ACK qualification.
