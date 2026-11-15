# Actual ordinary retirement callback source slice

`tests/retirement-intent-core-unit` has a 106-book local source closure. It
materializes the actual A/B machine/core/access registrations, existing commit
admission sections and the production persisted lifecycle dispatcher. It includes
checkpoint catalog, construction and future lease state because the current B
operations actually use them; it does not invent an ordinary implementation of
those operations. Its closure contains no checkpoint builder, master, boot,
writer or restore worker. The machine callbacks are the ones served assembly
materializes, without the full simulator/executor entry.

The exact local include closure and its 28 new / 15 changed source files relative
to root b7b79808d are in `retirement-core-source-slice.json`. This is an include
manifest, not permission to replace root files wholesale: the reviewed integration
568724889 already preserves root transport/layout/helper-leaf changes. Changes
outside this manifest are not required to admit this callback entry.

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

## Served connection supplement against adacd9

The 106-book manifest is the callback/control qualification slice, not a
complete served-path integration manifest. Three additional production files
are mandatory even though they lie outside that local include closure:

- `books/assembly-index.lisp`: explicitly include `checkpoint-catalog-kind`
  after machines-b, before either registry is consumed. This registers the
  actual checkpoints/refs/bytes carriers for the lifecycle callbacks. It imports
  no writer, builder, master or recovery worker.
- `books/commit-arms.lisp`: initialize cb-life-member/off after installed-root
  ownership succeeds, call the bounded lifecycle dispatcher during publish until
  all members/bytes have been consumed, and only then publish C's successor and
  advance toward accepted settlement. Preserve the existing uncertain/stop and
  membership-release ordering. Its declared lifecycle and maintenance-return
  footprints must include all actual state read or written.
- `books/ops-semantic-steps.lisp`: preserve the existing operation vocabulary,
  including TLS/compression, and update the block-read child ABI to pass allocator
  edges alongside extents. Its operation-carrier result remains position 4;
  additional extent/edge results are at positions 6/7.

The source represented by those three additional files is already present in
this lane, except the explicit catalog include added in this supplement. The
integrator must take the relevant runtime hunks onto current root, not replace
root's unrelated assembly/transport changes or import the lane's master-worker
registration as part of ordinary retirement. The callback manifest's existing
core/core-children/core-harvest/read-pins/machines-b/commit files remain required.

Generator/attachment invariants for the connected served instance:

1. Register catalog, construction and future carriers before index/directory and
   core generation. The catalog leaf owns exactly the same three declarations
   formerly reached through checkpoint-kind-b. Registered init/profile contracts
   and the shared retirement control schema remain authoritative.
2. Preserve existing callback section order: B hook constraints and first commit
   events, transaction admission section, C's actual hook attachments, second
   commit events, then commit-arms and final commit events. The final section
   emits the lifecycle function before generated arms/run use it. Do not use the
   fixture's refusing C defaults in place of served attachments. Existing
   successor-publish/drop and member-replay attach through
   fn2-commit-hook-attach-events; stream-wake retains its CNS attachment. Their
   declared child frames, machine/allocator frame constraints and owner avoidance
   must still hold in the newly composed core.
3. Keep actual publish/dependency/log/fence/failed guard checks. The served arms
   obtain these from their original journal lifecycle; the test's explicit
   logical premise writes are not a production source for those flags. No
   accepted outcome precedes successful lifecycle completion.
4. The shared pin issuer reserves edge `6+2*N+opslot` for the actual operation
   generation before descriptor issue. A refused unpublished issue drops that
   exact pin; uncertainty retains it. Completion hooks run only after validated
   completion/pool settlement and before operation finish/reuse. The hook sees
   the original opslot/opgen, cannot alter operation identity, and drops a live
   outstanding-IO edge only for its exact owner generation. The edge floor must
   cover these slots; journal IO's six dedicated edges remain separate.

A producer activation boundary remains: in current source the only production
caller of `fn2-retirement-submit` is checkpoint-teardown; its poll follows the
same path. Root without those workers therefore has a connected commit
consumer and callable ordinary submit/poll operations, but no scheduled ordinary
reclamation trigger. This supplement does not claim an activated ordinary
retirement feature. The root must retain that explicit outstanding owner/trigger
work rather than infer runtime reachability from the test's direct calls.
