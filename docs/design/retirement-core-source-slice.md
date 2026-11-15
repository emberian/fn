# Actual ordinary retirement callback source slice

`tests/retirement-intent-core-unit` has a 106-book local source closure. It
materializes the actual A/B machine/core/access registrations, existing commit
admission sections and the production persisted lifecycle dispatcher. It includes
checkpoint catalog, construction and future lease state because the current B
operations actually use them; it does not invent an ordinary implementation of
those operations. Its closure contains no checkpoint builder, master, boot,
writer or restore worker. The machine callbacks are the ones served assembly
materializes, without the full simulator/executor entry.

The exact local include closure and its 28 new / 14 changed source files relative
to root adacd9e71 are in `retirement-core-source-slice.json`. The additional runtime
files are `commit-arms.lisp`, `ops-semantic-steps.lisp` and the catalog-only include
in `assembly-index.lisp`. Root transport, compression and C attachments are
preserved. The actual scheduled retirement producer still resides in checkpoint
teardown, outside this slice. This slice connects the consumer and callable
producer; it does not enable reclamation or FREE. Full checkpoint scheduling,
selected-base recovery and retained-history rebase remain required.

`checkpoint-catalog-kind` contains the same capacity helper and three catalog
registrations formerly embedded in `checkpoint-kind-b`; the latter retains its
publication/lifecycle/worker registrations and includes the catalog leaf. This
is state/worker separation, with no alternate layout or runtime variant. Two
existing pure test profile helpers now live in `sim/commit-test-profile`, shared
by the original simulator harness and this callback fixture.

The original submit/poll body, run function and all three assertions moved
unchanged into one test event macro. Both the original full simulator entry and
the small core entry emit these exact events. Source structural comparisons of
those events, catalog declarations and test-profile functions passed. The three
controls exercise actual submit/poll with exact refusal, contradictory accepted
settlement, and stopped ambiguity, including durable-edge interleaving and
transient pins. Settlements are deliberately synthetic; none is a physical
writer/fence/ACK acceptance witness. Existing leaf and higher assertions remain.

The source entry also calls the actual generic transaction-body decoder for
ALLOCATION, RETIREMENT and CHECKPOINT_INSTALLATION and expects `:kind`. Generic
admission reaches this decoder through `txn-scan`, before open/join. Ordinary
keyed packing writes KEYED_MUTATION; its journal extent allocation is performed
by `fn2-commit-allocate` after durability, not an ALLOCATION transaction record.
Dedicated retirement packs RETIREMENT. Explicit ALLOCATION and checkpoint
installation members originate from their dedicated checkpoint coordinators,
which remain connected to the production checkpoint adapter. The ordinary
adapter's lifecycle-kind refusal therefore does not discard ordinary keyed
journal extent allocation. This is a source reachability inventory plus an
unrun actual decoder control, not a proved whole-machine reachability theorem.

The small instance retains the existing refusing default C hook attachments and
does not materialize the complete commit run/ACK loop. It is useful to qualify
actual submit/poll/dispatcher translation and those controls, not full ordinary
persistence. The original full simulator entry still supplies the later physical
writer/fence/install/notification qualification boundary. No ACL2, native,
remote, service or runtime compute was run for this source slice.

## Actual persisted dispatcher controls

`retirement-dispatch-core-unit` calls the actual retirement producer and derives
its containing collector, exact member workspace, control identity and allocator
intent. It decodes that retained member with the real framing/body codecs and
checks the full extent/epoch/allocation/batch tuple. The fixture then explicitly
sets the logical persisted premises: publish phase, installed containing batch,
successful dependency/log/fence flags, and no recorded failure. These assignments
are not a physical storage or process-death witness.

The positive calls `fn2-commit-lifecycle-step` itself and requires the exact
allocation to become RETIRE_PENDING at the containing batch, with intent cleared.
A real owned obligation is installed before submit; the positive requires its
exact holder/handle/kind and count to survive. The retained control and all edge
rows must stay unchanged. Nine separate controls remove phase, dependency, log,
fence, failure-free state, installed batch, member workspace owner generation,
control event or intent. Every one must return `:invalid` and preserve the full
allocator, control and protector-edge state compared immediately before/after
the dispatcher call. Those snapshots come from the existing column generator,
including all arrays, row counts and scalar extra fields. The member-generation
case exercises workspace ownership; the control-event case exercises the deeper
exact retained-control identity check. The original three submit/poll assertions
remain unchanged. All ten dispatcher assertions are source prepared and unrun.

## Cursor partition boundary

Both the actual persisted dispatcher and the production publish arm check the
same scalar `fn2-commit-lifecycle-cursorp` against the declared member partition.
Counts beyond that partition, cursors beyond the count and nonzero terminal
offsets refuse before member indexing or publication. Only an exact terminal
cursor with zero offset can report completion; the dispatcher also requires its
existing persisted containing-batch envelope for that result. These checks do
not scan or revalidate the store. Execution qualification remains pending.

## Partition/cursor controls added after c68d8b006

The dispatcher fixture adds six actual-entry scenarios: over-capacity count,
physical cross-partition index, member greater than count, terminal nonzero
byte offset, valid terminal completion, and terminal cursor with the wrong
installed batch. Every malformed scenario requires `:invalid` and the same
full allocator/control/edge snapshots as the existing controls. The crossing
witness explicitly confirms that the computed index exists in the next
partition and holds its initialized real `:none` row; global array bounds alone
would allow the old dispatcher to skip it. The over-count/member-zero case
would otherwise reach the actual pending retirement. Corrupted cursor states
must still satisfy the actual core WFP, making the missing semantic bound
explicit rather than assuming WFP excludes these states.

The terminal positive first installs the actual produced retirement, advances
past its exact byte length using the actual dispatcher, then calls again at
member=count/off=0. It requires `:done` and unchanged full snapshots for that
terminal call. Shared-predicate boundary assertions call the runtime owner's
`fn2-commit-lifecycle-cursorp` directly, using the declared per-batch geometry.
No fixture-local cursor model or literal partition capacity is introduced.

These additive controls depend on the runtime owner's matching cursor/partition
fix; c68 itself does not yet define the predicate or enforce these refusals.
They are source prepared, not executed. The served publish-arm boundary is a
separate entry through the existing generated `fn2-commit-run-publish`; the
small callback instance does not materialize those arms.
