# Actual ordinary retirement callback source slice

`tests/retirement-intent-core-unit` has a 109-book local source closure. It
materializes the actual A/B machine/core/access registrations, existing commit
admission sections and the production persisted lifecycle dispatcher. It includes
checkpoint catalog, construction and future lease state because the current B
operations actually use them; it does not invent an ordinary implementation of
those operations. Its closure contains no checkpoint builder, master, boot,
writer or restore worker. The machine callbacks are the ones served assembly
materializes, without the full simulator/executor entry.

The exact local include closure and its 31 new / 14 changed source files relative
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

## Actual served publish-arm negative entry

`tests/retirement-publish-core-unit` includes the existing
`assembly-callbacks-r2` entry and directly calls the generated served
`fn2-commit-run-publish`. It does not instantiate another machine or arm
implementation. The four source controls supply a real submitted retirement,
held obligation, good actual partner, and logical persisted envelope, then
corrupt only count/cursor: over-capacity count, physical cross-partition cursor,
member greater than count, or terminal nonzero offset. The arm budget comes
from the actual registered commit declaration and must be positive.

Each requires sticky `commit-publish` stop, no descriptors, unchanged publication
and acknowledgement markers/cursor/phase, and complete declaration-generated
snapshots of allocator, retirement control, protection edges, members,
settlements, commit root (including published frontier), source pool/fields,
operations and C's ID-engine published state. `retirement-control` is distinct
from global execution `control`: global stop/reason are expected to change and
are asserted directly rather than included in that unchanged source frame.
The comparison does not claim a complete frame for every global-control field.

The existing test projection helper moves unchanged to the shared
`retirement-state-projections` book; the original callback fixture's schema
snapshots are unchanged. Local source closures are now 107 for the callback
root and 162 for this served publish negative root, with no missing files.
The publish target is registered in Makefile. All controls remain source
prepared and unrun, and depend on the parent's matching runtime guard commit.
Positive complete C publication/ACK remains a subsequent qualification step;
these negatives establish no physical persistence claim.

## Canonical-first control entry at 347058fb0

The canonical gate root is now `tests/retirement-canonical-core-unit`, with 166
local source books. It first includes the existing served R2 publish fixture,
then emits shared control events in that same actual core/C-attachment world:
submit/poll 3, generic decoder 1, dispatcher 16, cursor predicate 8, publish 4.
These 32 assertions are the existing operation bodies and expectations, not
rewritten models. The canonical closure contains no partial core instance.
The staged runtime prefix owned by recover_children is unchanged: this source
change touches tests, source identity tooling, registration and documentation,
with no runtime book or host edits.

The dispatcher functions/assertions move verbatim into
`retirement-dispatch-controls`; its historical partial entry retains its same
core/profile/projection setup and emits the shared events. Generic decoder
functions/assertion likewise move into `retirement-generic-controls`. The
existing submit/poll macro and publish fixture remain byte unchanged. Shared
macro books define source-time test events only; no runtime generator, adapter,
function body, guard or attachment selection changes.

`tests/retirement-canonical-controls-receipt.json` freezes event-tree identities
from source base 347058fb0, event/assertion counts and the unchanged publish
file's byte identity. Run `python3 tools/test_retirement_canonical_controls.py`
for the exact extraction, common event selection, assertion inventory and
canonical-world checks. The historical partial root remains separately scoped
(now 109 local books due the two pure macro includes); it is not a second
instance to include alongside the canonical entry in one ACL2 world. Its old
source scope is preserved for comparison, not substituted for the canonical
gate's actual served core.

Qualification plan: admit/record the current canonical target and execute its
32 actual controls after the staged runtime prefix is ready. No control was
executed during this extraction. Their logical persisted premises and synthetic
settlements remain explicit; canonical-world execution alone will not establish
physical IO, complete positive C publication/ACK, or crash qualification.

## Current integration and qualification

The clean donor is based on root `6a2b565f625dd5bf1872db616ae847c705ba1897`. It preserves current TLS and codec work and excludes unfinished cold recovery, rebase and checkpoint scheduling. The canonical entry remains the finish gate; the earlier partial-entry inventory above is historical.

The exact 4fa retirement prefix of 33 books is record-qualified (21 reused, 12 new), record `certify-20261115T015645Z-703564`, toolchain 8aeb. Compact retirement final ordering also passed author admission. The current composed machines-b and canonical controls remain unqualified. Source identity tests pass all three checks; none executes ACL2 controls.

- `books/machines-b`: 76 local books, closure key `1120aa27bbdbd793107927b4836d2cd2439375fe8c84bc659f5b9034faf28cb4`.

- `tests/retirement-canonical-core-unit`: 166 local books, closure key `d836c8196760e5c5852c45259143f3636b00f10ee7b54f3b46f85711f15c1e91`.

- `tests/retirement-publish-core-unit`: 162 local books, closure key `9b14ca2c7b1ff94ea894277e1e8c2d62c97800d277d6ae297ffaa816488c4d57`.
