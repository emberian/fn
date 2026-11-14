# Persistent reclamation frontier

The current fn2 served machine does not implement persistent extent recycling.
`FN2-PERSISTENT-RECLAMATION-LIFETIME` in `books/owed-reclamation.lisp` records
that missing guarantee in the existing square registry. It deliberately has
no statement, proof or checker result. The product completion scope must
require this row with served subject `FN2-TURN`; an allocator-local theorem
does not establish that subject's lifetime guarantee.

## Existing mechanisms and their limits

`books/alloc.lisp` provides reserve, edge add/drop, retire, checkpoint advance,
release and relocate. Its release predicate checks retirement, checkpoint cut
and protection. `tests/alloc-unit.lisp` manually drives those operations and
feeds `sim/check-reclaim.lisp`, an independent event interpreter. Those are
useful allocator tests, not a served reclamation trace. The generic
`sim/check.lisp` dispatcher still answers `:not-yet` for reclamation.

The source recovery replay now calls `fn2-retirement-install`, which applies
`fn2-alloc-retire` only for the containing batch and matching allocation.
The live writer has no lifecycle producer yet. Persistent release, checkpoint
advance and relocation remain unconnected to served reclamation.
`books/commit.lisp` does reserve extents and
maintain installed-root, prepared-successor and outstanding-I/O edges.
Cancelling an uncommitted reservation is distinct from retiring live data.
`fn2-rd-release` in `books/machines-c-read.lisp` releases query/range/read
rows; it does not release persistent allocations. Scheduler machine reclaim
and pool release likewise do not establish persistent extent recycling.

`docs/b-durability.md` identifies B6 checkpoint/cleaner machines as owed;
`books/checkpoint.lisp` and `books/cleaner.lisp` are absent. The legacy native
expiry/reclaim tests name absent `books/store-reclaim-pack.lisp`,
`books/owner-reclaim.lisp` and `host/native/checkpoint.lisp`. Their existence
is not evidence about the current fn2 served path.

This absence is not a demonstrated premature-reuse bug. Never reclaiming
committed extents can avoid reuse while still failing the product's capacity
and progress requirements.

## Integration contract

The next implementation must connect a bounded, resumable coordinator to the
served machine, rather than enabling release calls in isolation:

1. A read/borrow transition acquires its concrete extent and generation's
   protection before exposing bytes. Protection lasts through the promised
   read and every outstanding operation; completion and cancellation release
   precisely the holder's edge. Query-row release alone is insufficient.
2. Installed roots, every selectable checkpoint, recovery bases and candidates,
   prepared successors and custody obligations preserve their own protection
   through root replacement and recovery. These are distinct from read pins.
3. Retirement and checkpoint selection make release eligible, but eligibility
   does not make an extent reusable. The composed machine persists the release
   before FREE, models each death cut, and excludes stale-generation references
   after restart and reuse. Ambiguous persistence results require recovery.
4. Once the last actual protector disappears and the installed cut permits
   release, bounded steps eventually reclaim under stated scheduling and I/O
   assumptions. This progress obligation is separate from lifetime safety;
   no whole-store validation or arbitrary stored-data ceiling substitutes for it.

The first connected witness should hold a served read across retirement,
checkpoint installation and attempted release, assert the entire antecedent,
then finish the read and observe persisted release and generation-safe reuse.
Its removal control omits that live read's protection and reaches a stale read
or premature reuse in the same composed trace. Crash controls straddle release
persistence and reuse; a separate progress control detects permanent retention.

`tests/owed-reclamation-unit.lisp` exercises only the registry boundary: the
unbound requirement is valid, while fabricated proof and allocator-only check
attachments are refused. It is not a storage safety witness. The completion
gate owns the product scope and served-subject check; this lane adds no rival
completion inventory. Until the coordinator and witnesses exist, this row
must remain unbound and product completion must fail closed.

## Concrete integration seams

`fn2-alloc-release-code` now owns the actual release decision used by
`fn2-alloc-release`. It is read-only preflight, not a durability token.
`fn2-alloc-reclaim-candidate` visits one retired FIFO row and returns its next
row, writer epoch, allocation counter and retirement commit. A protected head
does not prevent the coordinator from inspecting its successor on the next
turn. Both functions use existing concrete allocator metadata; neither is a
second reference implementation or an enabled reclamation machine.

The proposed served B coordinator enters through `fn2-turn` dispatch and keeps
one candidate handle, next FIFO row, installed checkpoint identity/cut, and the
pending journal operation identity across turns. A completed candidate scan
does not certify that the store is reclaimable. A later pass revisits blocked
rows. Candidate selection, record construction, persistence, and final release
are separate states, with the release decision rechecked after persistence.

The physical read pin belongs at `fn2-block-read-children` in
`books/machines-b.lisp`: it currently validates the physical unit's extent,
epoch and allocation, then issues asynchronous storage I/O. The logical
read-row release is not that boundary. Cursor and CNS callers copy physical
data into their owned pool lease; source-extent protection must last through
physical read completion/backend exclusion, independently of subsequent pool
borrow lifetime. The operation slot and generation are the proposed pin
owner. Outbox acknowledgement cannot release this pin. Pin attachment must
complete before the issued descriptor becomes visible to the adapter, and
failure must not leave a descriptor without protection.

Two dependencies prevent enabling final FREE now. First, the source physical
pin integration needs admission and executable qualification. Second, although
`fn2-format-retirement` and `fn2-format-release-allocation` already encode the
lifecycle records (including checkpoint and physical release evidence), the
internal retirement producer now joins the existing batch planner and writer,
but has not been admitted or executed. General transaction admission remains
closed to lifecycle input. Ordered recovery has a source retirement branch,
but no release branch.
The release coordinator must join the actual journal persistence and
recovery path, including checkpoint-root protection, before any call to FREE.

The persistence interval also needs an admission rule: a successful preflight
must not let a new durable root or custody obligation publish against an
extent whose release record is becoming durable. A late ephemeral read pin
can make the final runtime recheck retain the extent, but this alone does not
justify replaying release in the presence of a newly durable protector.
Retirement/publication serialization must prohibit that durable reference
race; recovery must establish backend exclusion for pre-crash physical I/O.

The physical pin seam now has a source implementation awaiting admission:
`fn2-block-read-children` acquires the next operation identity's dedicated edge
before issuing, rolls it back on ordinary refusal, and retains it when issuance
stops uncertainly. The profile reserves one edge per operation after the six
commit-I/O edges and the two-per-extent root edges. `defcorechild :harvest`
generates completion extensions; `fn2-harvest-one` calls them after validated
harvest and pool settlement, before operation finish/recycle. B's callback
releases only the matching read-result generation. Generated extension bindings
exclude operation, pool and control children, with an unconditional operation
table frame theorem for the lifecycle proof consumer.

`tests/read-pins-unit.lisp` drives the actual block-read and harvest entries,
interleaving retirement/checkpoint, ACK, stale completion and real physical
completion; its removal control drops the acquired pin while that same read
is outstanding. These fixtures do not implement checkpoint publication or
journal replay, and source presence is not certification. No served FREE path
is enabled by this change.

The explicit `release-pending` allocator marker now closes durable edge
admission after successful `fn2-alloc-release-prepare`. Ordinary retirement
still accepts protections. Transient pins remain possible and continue to
block release; no generic abort clears ambiguous intent. The marker itself
is not durability evidence. Source fixtures inspect it directly, including
reset on reuse; the allocator's display view does not carry it.

`books/retirement.lisp` shares the existing member framing/body codec and one
exact-batch install operation. Recovery passes its verified containing commit
to `fn2-recovery-replay-record`, flushes any pending C workspace, and applies
retirement after adoption. Wrong-batch, stale and conflicting records fail.
Codec/truncation and actual replay-entry fixtures are in the unit catalog;
admission and execution remain pending. `fn2-retirement-submit` now selects
the actual collector, derives its batch, encodes one member, and joins it in
one operation. A singleton retains the workspace through uncertain outcomes.
The publish phase visits one member/frame per step after log/fence durability
and root installation; retirement must match that singleton's physical handle,
workspace, owner and containing batch before the shared installer runs.
`fn2-retirement-poll` consumes only its exact batch/event settlement, preserving
other outcomes from the same owner. `tests/retirement-live-unit.lisp` drives
these entries through `fn2-turn` and the simulated adapter, with early-install
refusal and ambiguous-write controls. These source fixtures remain unexecuted.

Before reuse, recovery's historical-location adoption must become checkpoint
aware: old and reused identities cannot be adopted as simultaneously live.
Checkpoint publication/root selection and a journaled writer-epoch transition
remain prerequisites. A release record decoder alone cannot close these gaps.
